import TransposeFollowup.XorPackets

/-! Independent flips of Boolean coordinate sets and unanchored XOR
components. These operations are linear only in the transformed coordinates. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false
universe u

noncomputable def toggleBits {V : Type u} (S : Finset V) (z : V → Bool) : V → Bool :=
  fun v => z v ^^ decide (v ∈ S)

@[simp] theorem toggleBits_empty {V : Type u} (z : V → Bool) : toggleBits ∅ z = z := by
  funext v
  simp [toggleBits]

@[simp] theorem toggleBits_twice {V : Type u} (S : Finset V) (z : V → Bool) :
    toggleBits S (toggleBits S z) = z := by
  funext v
  simp [toggleBits]

theorem toggleBits_union {V : Type u} [DecidableEq V]
    (S T : Finset V) (h : Disjoint S T) (z : V → Bool) :
    toggleBits (S ∪ T) z = toggleBits S (toggleBits T z) := by
  funext v
  by_cases hs : v ∈ S <;> by_cases ht : v ∈ T
  · exact False.elim ((Finset.disjoint_left.mp h) hs ht)
  all_goals simp [toggleBits, hs, ht]

theorem bool_xor_left_cancel {a b c : Bool} (h : (a ^^ b) = (a ^^ c)) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem xor_pair_flip (a b c : Bool) : ((a ^^ c) ^^ (b ^^ c)) = (a ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem toggleBits_set_injective {V : Type u} (z : V → Bool) :
    Function.Injective (fun S : Finset V => toggleBits S z) := by
  intro S T h
  ext v
  have hv := bool_xor_left_cancel (congrFun h v)
  change decide (v ∈ S) = decide (v ∈ T) at hv
  by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all

namespace XorSystem

variable {V : Type u} [Fintype V] {B : ℕ} (C : XorSystem V B)

theorem broadcast_toggle_component {S : Finset V} (hS : S ∈ C.unanchored) (z : V → Bool) :
    C.broadcast (toggleBits S z) = C.broadcast z := by
  obtain ⟨hcomp, hdis⟩ := Finset.mem_filter.mp hS
  funext k
  cases hk : C.packet k with
  | single v =>
      have ha : v ∈ C.anchors := Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk⟩
      have hv : v ∉ S := fun hs => (Finset.disjoint_left.mp hdis) hs ha
      simp [broadcast, hk, XorPacket.eval, toggleBits, hv]
  | pair v w =>
      have hmem : v ∈ S ↔ w ∈ S := by
        rw [C.mem_component_iff hcomp, C.mem_component_iff hcomp, C.pair_same_component hk]
      simp only [broadcast, hk, XorPacket.eval, toggleBits]
      have hd : decide (v ∈ S) = decide (w ∈ S) := by simp only [hmem]
      rw [hd]
      exact xor_pair_flip _ _ _

end XorSystem
end TransposeFollowup
