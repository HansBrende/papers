import TransposeFollowup.XorPackets

/-! Fixed Boolean packet occurrences with declared supports of at most two
coordinates. Evaluation may be nonlinear; the support may be empty, and
different occurrences may have the same function and support. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false
universe u

structure CoordinatePacket (V : Type u) where
  support : Finset V
  support_card_le : support.card ≤ 2
  eval : (V → Bool) → Bool
  eval_congr : ∀ z z', (∀ v ∈ support, z v = z' v) → eval z = eval z'

structure CoordinateSystem (V : Type u) (B : ℕ) where
  packet : Fin B → CoordinatePacket V

namespace CoordinateSystem

variable {V : Type u} {B : ℕ} (C : CoordinateSystem V B)

def broadcast (z : V → Bool) : Fin B → Bool := fun k => (C.packet k).eval z

def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ k, v ∈ (C.packet k).support ∧ w ∈ (C.packet k).support
  symm := ⟨by rintro v w ⟨hne, k, hv, hw⟩; exact ⟨hne.symm, k, hw, hv⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable [Fintype V]

noncomputable def component (v : V) : Finset V := componentSet C.graph ∅ v

noncomputable def components : Finset (Finset V) := graphComponents C.graph ∅

theorem mem_component_self (v : V) : v ∈ C.component v :=
  componentSet_self_mem C.graph ∅ v (Finset.notMem_empty v)

theorem component_mem (v : V) : C.component v ∈ C.components :=
  (mem_graphComponents C.graph ∅ _).mpr ⟨v, Finset.notMem_empty v, rfl⟩

theorem component_nonempty {S : Finset V} (hS : S ∈ C.components) : S.Nonempty :=
  graphComponents_nonempty C.graph ∅ S hS

theorem component_eq_of_mem {v w : V} (hw : w ∈ C.component v) :
    C.component v = C.component w :=
  componentSet_eq_of_outsideConnected C.graph ∅ ((mem_componentSet C.graph ∅ v w).mp hw)

theorem mem_component_iff {S : Finset V} (hS : S ∈ C.components) (v : V) :
    v ∈ S ↔ C.component v = S := by
  obtain ⟨w, _, rfl⟩ := (mem_graphComponents C.graph ∅ S).mp hS
  constructor
  · intro hv; exact (C.component_eq_of_mem hv).symm
  · intro heq; rw [← heq]; exact C.mem_component_self v

theorem components_disjoint : (C.components : Set (Finset V)).PairwiseDisjoint id :=
  graphComponents_pairwise_disjoint C.graph ∅

theorem components_cover : C.components.biUnion id = Finset.univ := by
  simpa [components] using graphComponents_cover C.graph ∅

theorem support_same_component (k : Fin B) {v w : V}
    (hv : v ∈ (C.packet k).support) (hw : w ∈ (C.packet k).support) :
    C.component v = C.component w := by
  by_cases he : v = w
  · subst w; rfl
  · exact componentSet_compatible C.graph ∅ v (Finset.notMem_empty v)
      w (Finset.notMem_empty w) ⟨he, k, hv, hw⟩

theorem support_subset_component (k : Fin B) {S : Finset V} (hS : S ∈ C.components)
    {v : V} (hv : v ∈ (C.packet k).support) (hvS : v ∈ S) :
    (C.packet k).support ⊆ S := by
  intro w hw
  rw [C.mem_component_iff hS, ← C.support_same_component k hv hw]
  exact (C.mem_component_iff hS v).mp hvS

/-- Empty supports are intentionally excluded: their outputs are constant
and they do not belong to a variable component. -/
noncomputable def packetIndices (S : Finset V) : Finset (Fin B) :=
  Finset.univ.filter (fun k => (C.packet k).support.Nonempty ∧ (C.packet k).support ⊆ S)

omit [Fintype V] in
theorem mem_packetIndices (S : Finset V) (k : Fin B) :
    k ∈ C.packetIndices S ↔ (C.packet k).support.Nonempty ∧ (C.packet k).support ⊆ S := by
  simp [packetIndices]

theorem packetIndices_disjoint :
    (C.components : Set (Finset V)).PairwiseDisjoint C.packetIndices := by
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro k hkS hkT
  obtain ⟨⟨v, hv⟩, hs⟩ := (C.mem_packetIndices S k).mp hkS
  have ht := ((C.mem_packetIndices T k).mp hkT).2
  exact Finset.disjoint_left.mp (C.components_disjoint hS hT hne) (hs hv) (ht hv)

theorem support_disjoint_of_not_packetIndices {S : Finset V} (hS : S ∈ C.components)
    {k : Fin B} (hk : k ∉ C.packetIndices S) : Disjoint (C.packet k).support S := by
  apply Finset.disjoint_left.mpr
  intro v hv hvS
  exact hk ((C.mem_packetIndices S k).mpr
    ⟨⟨v, hv⟩, C.support_subset_component k hS hv hvS⟩)

/-- Equal local packet values plus agreement outside the component imply
equal complete broadcasts, including all constant and repeated packets. -/
theorem broadcast_eq_of_component {S : Finset V} (hS : S ∈ C.components)
    {z z' : V → Bool} (hout : ∀ v ∉ S, z v = z' v)
    (hin : ∀ k ∈ C.packetIndices S, (C.packet k).eval z = (C.packet k).eval z') :
    C.broadcast z = C.broadcast z' := by
  funext k
  by_cases hk : k ∈ C.packetIndices S
  · exact hin k hk
  · apply (C.packet k).eval_congr
    intro v hv
    exact hout v (fun hvS => Finset.disjoint_left.mp
      (C.support_disjoint_of_not_packetIndices hS hk) hv hvS)

noncomputable def deficient : Finset (Finset V) :=
  C.components.filter (fun S => (C.packetIndices S).card < S.card)

theorem mem_deficient (S : Finset V) :
    S ∈ C.deficient ↔ S ∈ C.components ∧ (C.packetIndices S).card < S.card := by
  simp [deficient]

noncomputable def smallComponents (ell : ℕ) : Finset (Finset V) :=
  C.deficient.filter (fun S => S.card ≤ ell)

end CoordinateSystem

namespace XorPacket

noncomputable def toCoordinatePacket {V : Type u} (p : XorPacket V) : CoordinatePacket V :=
  match p with
  | .single v =>
    { support := {v}
      support_card_le := by simp
      eval := fun z => z v
      eval_congr := by intro z z' h; exact h v (by simp) }
  | .pair v w =>
    { support := {v, w}
      support_card_le := by exact (Finset.card_insert_le _ _).trans (by simp)
      eval := fun z => z v ^^ z w
      eval_congr := by intro z z' h; rw [h v (by simp), h w (by simp)] }

@[simp] theorem toCoordinatePacket_eval {V : Type u} (p : XorPacket V) (z : V → Bool) :
    p.toCoordinatePacket.eval z = p.eval z := by cases p <;> rfl

end XorPacket

noncomputable def XorSystem.toCoordinateSystem {V : Type u} {B : ℕ} (C : XorSystem V B) :
    CoordinateSystem V B := ⟨fun k => (C.packet k).toCoordinatePacket⟩

@[simp] theorem XorSystem.toCoordinateSystem_broadcast {V : Type u} {B : ℕ}
    (C : XorSystem V B) (z : V → Bool) :
    C.toCoordinateSystem.broadcast z = C.broadcast z := by
  funext k
  exact (C.packet k).toCoordinatePacket_eval z

end TransposeFollowup
