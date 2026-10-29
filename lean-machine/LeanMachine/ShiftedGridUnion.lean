import LeanMachine.ShiftedGrid
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Pay the distinct coordinates of a clipped raw-block union once. -/

namespace LeanMachine.ShiftedGrid

open Classical Finset
open scoped BigOperators
noncomputable section

def blockUnion (L w θ : ℕ) (S : Finset ℕ) : Finset (Fin L) :=
  S.biUnion fun y => univ.filter fun z => label w θ z.val = label w θ y

@[simp] theorem mem_blockUnion {L w θ : ℕ} {S : Finset ℕ} {z : Fin L} :
    z ∈ blockUnion L w θ S ↔ ∃ y ∈ S, label w θ z.val = label w θ y := by
  simp [blockUnion]

@[simp] theorem blockUnion_empty (L w θ : ℕ) : blockUnion L w θ ∅ = ∅ := by
  simp [blockUnion]

/-- Valid for every shift; neither disjoint blocks nor distinct labels are assumed. -/
theorem blockUnion_card_le {L w : ℕ} (hw : 0 < w) (θ : ℕ) (S : Finset ℕ) :
    (blockUnion L w θ S).card ≤ min L (w * S.card) := by
  apply le_min (by simpa using card_le_univ (s := blockUnion L w θ S))
  calc
    _ ≤ ∑ y ∈ S, (univ.filter fun z : Fin L => label w θ z.val = label w θ y).card :=
      card_biUnion_le
    _ ≤ ∑ _y ∈ S, w := by
      apply sum_le_sum
      intro y _
      let B := univ.filter fun z : Fin L => label w θ z.val = label w θ y
      have h := card_le_of_constant (θ := θ) hw (S := B.image Fin.val) (by
        intro u hu v hv
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
        exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
      simpa only [card_image_of_injective _ Fin.val_injective] using h
    _ = w * S.card := by simp [Nat.mul_comm]

end
end LeanMachine.ShiftedGrid
