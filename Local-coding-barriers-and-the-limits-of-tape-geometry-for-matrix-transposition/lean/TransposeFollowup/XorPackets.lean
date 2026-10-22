import TransposeFollowup.ComponentPartition

/-! Static singleton/XOR broadcasts on Boolean coordinates. Repeated packets,
cycles, same-row packets and self-XORs are all allowed. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

inductive XorPacket (V : Type u)
  | single (v : V)
  | pair (v w : V)

def XorPacket.eval {V : Type u} (z : V → Bool) : XorPacket V → Bool
  | .single v => z v
  | .pair v w => z v ^^ z w

theorem xor_difference_of_pair_equal {a b c d : Bool} (h : (a ^^ b) = (c ^^ d)) :
    (a ^^ c) = (b ^^ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

structure XorSystem (V : Type u) (B : ℕ) where
  packet : Fin B → XorPacket V

namespace XorSystem

variable {V : Type u} {B : ℕ} (C : XorSystem V B)

def broadcast (z : V → Bool) : Fin B → Bool := fun k => (C.packet k).eval z

def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ k, C.packet k = .pair v w ∨ C.packet k = .pair w v
  symm := ⟨by rintro v w ⟨hne, k, hk⟩; exact ⟨hne.symm, k, hk.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def IsAnchor (v : V) : Prop := ∃ k, C.packet k = .single v

variable [Fintype V]

noncomputable def anchors : Finset V := Finset.univ.filter C.IsAnchor

noncomputable def component (v : V) : Finset V := componentSet C.graph ∅ v

noncomputable def components : Finset (Finset V) := graphComponents C.graph ∅

noncomputable def unanchored : Finset (Finset V) :=
  C.components.filter (fun S => Disjoint S C.anchors)

theorem mem_unanchored (S : Finset V) :
    S ∈ C.unanchored ↔ S ∈ C.components ∧ Disjoint S C.anchors := by
  simp only [unanchored, Finset.mem_filter]

theorem mem_component_self (v : V) : v ∈ C.component v :=
  componentSet_self_mem C.graph ∅ v (Finset.notMem_empty v)

theorem component_mem (v : V) : C.component v ∈ C.components :=
  (mem_graphComponents C.graph ∅ _).mpr ⟨v, Finset.notMem_empty v, rfl⟩

theorem component_nonempty {S : Finset V} (hS : S ∈ C.components) : S.Nonempty :=
  graphComponents_nonempty C.graph ∅ S hS

theorem component_eq_of_mem {v w : V} (hw : w ∈ C.component v) :
    C.component v = C.component w :=
  componentSet_eq_of_outsideConnected C.graph ∅ ((mem_componentSet C.graph ∅ v w).mp hw)

theorem pair_same_component {v w : V} {k : Fin B} (hk : C.packet k = .pair v w) :
    C.component v = C.component w := by
  by_cases hvw : v = w
  · subst w; rfl
  · exact componentSet_compatible C.graph ∅ v (Finset.notMem_empty v)
      w (Finset.notMem_empty w) ⟨hvw, k, Or.inl hk⟩

theorem mem_component_iff {S : Finset V} (hS : S ∈ C.components) (v : V) :
    v ∈ S ↔ C.component v = S := by
  obtain ⟨w, _, rfl⟩ := (mem_graphComponents C.graph ∅ S).mp hS
  constructor
  · intro hv
    exact (C.component_eq_of_mem hv).symm
  · intro heq
    rw [← heq]
    exact C.mem_component_self v

omit [Fintype V] in
theorem same_broadcast_anchor {z z' : V → Bool} (hz : C.broadcast z = C.broadcast z')
    {v : V} (hv : C.IsAnchor v) : z v = z' v := by
  obtain ⟨k, hk⟩ := hv
  have h := congrFun hz k
  simpa [broadcast, hk, XorPacket.eval] using h

omit [Fintype V] in
theorem same_broadcast_edge_difference {z z' : V → Bool}
    (hz : C.broadcast z = C.broadcast z') {v w : V} (hvw : C.graph.Adj v w) :
    (z v ^^ z' v) = (z w ^^ z' w) := by
  obtain ⟨_, k, hk | hk⟩ := hvw
  · have h := congrFun hz k
    simp only [broadcast, hk, XorPacket.eval] at h
    exact xor_difference_of_pair_equal h
  · have h := congrFun hz k
    simp only [broadcast, hk, XorPacket.eval] at h
    exact (xor_difference_of_pair_equal h).symm

/-- Equal broadcasts make the bitwise difference constant on each variable
component. This is a fact about transformed bits only, not raw recoded rows. -/
theorem same_broadcast_component_difference {z z' : V → Bool}
    (hz : C.broadcast z = C.broadcast z') {v w : V} (hw : w ∈ C.component v) :
    (z v ^^ z' v) = (z w ^^ z' w) := by
  obtain ⟨_, _, ⟨p⟩⟩ := (mem_componentSet C.graph ∅ v w).mp hw
  have along : ∀ {a b : {x : V | x ∉ (∅ : Finset V)}},
      (C.graph.induce {x | x ∉ (∅ : Finset V)}).Walk a b →
      (z a.val ^^ z' a.val) = (z b.val ^^ z' b.val) := by
    intro a b q
    induction q with
    | nil => rfl
    | cons h _ ih => exact (C.same_broadcast_edge_difference hz h).trans ih
  exact along p

noncomputable def representative (S : C.unanchored) : V :=
  (C.component_nonempty (Finset.mem_filter.mp S.property).1).choose

theorem representative_mem (S : C.unanchored) : C.representative S ∈ S.val :=
  (C.component_nonempty (Finset.mem_filter.mp S.property).1).choose_spec

/-- Broadcast bits plus one original transformed bit from each unanchored
component determine all transformed bits. This supplies the rank count by
finite injectivity, without needing a separate linear-algebra normalization. -/
theorem broadcast_with_representatives_injective :
    Function.Injective (fun z : V → Bool =>
      (C.broadcast z, fun S : C.unanchored => z (C.representative S))) := by
  intro z z' heq
  have hm := congrArg Prod.fst heq
  have hr := congrArg Prod.snd heq
  funext v
  have hc := C.component_mem v
  by_cases hu : C.component v ∈ C.unanchored
  · let S : C.unanchored := ⟨C.component v, hu⟩
    have hd := C.same_broadcast_component_difference (v := v) hm (C.representative_mem S)
    have he : z (C.representative S) = z' (C.representative S) := congrFun hr S
    simpa [he] using hd
  · have hdis : ¬Disjoint (C.component v) C.anchors := by
      intro h
      exact hu (Finset.mem_filter.mpr ⟨hc, h⟩)
    obtain ⟨w, hw, ha⟩ := Finset.not_disjoint_iff.mp hdis
    have he := C.same_broadcast_anchor hm (Finset.mem_filter.mp ha).2
    have hd := C.same_broadcast_component_difference hm hw
    simpa [he] using hd

theorem coordinate_count_le_broadcast_add_unanchored :
    Fintype.card V ≤ B + C.unanchored.card := by
  have h := Fintype.card_le_of_injective _ C.broadcast_with_representatives_injective
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe, ← pow_add] at h
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp h

end XorSystem
end TransposeFollowup
