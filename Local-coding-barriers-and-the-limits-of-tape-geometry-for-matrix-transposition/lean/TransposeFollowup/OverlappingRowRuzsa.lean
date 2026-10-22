import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Two applications of mathlib's Ruzsa triangle inequality turn a
large row intersection and small row doublings into a small mixed sum. -/
namespace TransposeFollowup.ScalarMetric
open scoped Pointwise
open Finset
set_option autoImplicit false

theorem card_mixed_sum_intersection_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) :
    (A + B).card * (A ∩ B).card * A.card ≤
      (A + A).card ^ 2 * (B + B).card := by
  have hdiff := ruzsa_triangle_inequality_sub_add_add A A A
  have hmix := ruzsa_triangle_inequality_add_sub_add A (A ∩ B) B
  have hleft : ((A ∩ B) - A).card ≤ (A - A).card :=
    card_le_card (sub_subset_sub inter_subset_left Subset.rfl)
  have hright : ((A ∩ B) + B).card ≤ (B + B).card :=
    card_le_card (add_subset_add inter_subset_right Subset.rfl)
  have hmix' : (A + B).card * (A ∩ B).card ≤
      (A - A).card * (B + B).card := by
    simpa only [Nat.mul_comm (A + B).card] using
      hmix.trans (Nat.mul_le_mul hleft hright)
  calc
    _ ≤ ((A - A).card * (B + B).card) * A.card := Nat.mul_le_mul_right _ hmix'
    _ = ((A - A).card * A.card) * (B + B).card := by ring
    _ ≤ ((A + A).card * (A + A).card) * (B + B).card :=
      Nat.mul_le_mul_right _ hdiff
    _ = _ := by ring

/-- The losses are explicit: overlap at least `|A|/(2*K)` and doubling
at most `L*|A|` imply mixed sum at most `2*K*L^3*|A|`. -/
theorem mixed_sum_le_of_popular_overlap {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) {K L : ℝ} (hA : A.Nonempty) (hK : 0 < K)
    (hAA : ((A + A).card : ℝ) ≤ L * A.card)
    (hBB : ((B + B).card : ℝ) ≤ L * A.card)
    (hover : (A.card : ℝ) ≤ 2 * K * (A ∩ B).card) :
    ((A + B).card : ℝ) ≤ 2 * K * L ^ 3 * A.card := by
  have hN : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hraw : ((A + B).card : ℝ) * (A ∩ B).card * A.card ≤
      ((A + A).card : ℝ) ^ 2 * (B + B).card := by
    exact_mod_cast card_mixed_sum_intersection_bound A B
  have hupper : ((A + A).card : ℝ) ^ 2 * (B + B).card ≤
      (L * A.card) ^ 2 * (L * A.card) :=
    mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hAA 2) hBB
      (Nat.cast_nonneg _) (sq_nonneg _)
  have hlower : ((A + B).card : ℝ) * A.card * A.card ≤
      2 * K * (((A + B).card : ℝ) * (A ∩ B).card * A.card) := by
    have h := mul_le_mul_of_nonneg_left hover
      (show 0 ≤ ((A + B).card : ℝ) * A.card by positivity)
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_left (hraw.trans hupper) (show 0 ≤ 2 * K by positivity)
  apply (mul_le_mul_iff_of_pos_right (show (0 : ℝ) < (A.card : ℝ) ^ 2 by positivity)).mp
  nlinarith only [hlower, h]

end TransposeFollowup.ScalarMetric
