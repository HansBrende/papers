import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Fibre-size moments and tails of a finite partition

The same deterministic label function works on every source subset. The
identities count its attained labels, without independence assumptions.
-/

namespace LeanMachine.FinitePartition

open Finset
set_option autoImplicit false
noncomputable section
variable {X Y : Type*} [DecidableEq Y]

open Classical in
/-- The exponential moment of a fibre deficit, with a label-dependent bill.
This is a finite counting identity and permits the empty source set. -/
theorem deficit_moment (S : Finset X) (f : X → Y) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≠ 1) (L : ℝ) (bill : Y → ℝ) :
    ∑ x ∈ S, b ^ ((L - Real.logb b (S.filter fun y => f y = f x).card) - bill (f x)) =
      ∑ z ∈ S.image f, b ^ (L - bill z) := by
  let weight z := b ^ (L - bill z) / (S.filter fun x => f x = z).card
  calc
    _ = ∑ x ∈ S, weight (f x) := by
      apply sum_congr rfl
      intro x hx
      have hpos : 0 < ((S.filter fun y => f y = f x).card : ℝ) := by
        exact_mod_cast (show (S.filter fun y => f y = f x).Nonempty from
          ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩).card_pos
      rw [sub_right_comm, Real.rpow_sub hb, Real.rpow_logb hb hb1 hpos]
    _ = ∑ z ∈ S.image f, ∑ x ∈ S with f x = z, weight z :=
      (sum_fiberwise_of_maps_to' (fun x hx => mem_image_of_mem f hx) _).symm
    _ = _ := by
      apply sum_congr rfl
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      have hpos : 0 < ((S.filter fun y => f y = f x).card : ℝ) := by
        exact_mod_cast (show (S.filter fun y => f y = f x).Nonempty from
          ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩).card_pos
      simp only [sum_const, nsmul_eq_mul, weight]
      field_simp

open Classical in
/-- A label-dependent deficit tail, charging only attained labels. -/
theorem bad_card_le (S : Finset X) (f : X → Y) {b : ℝ}
    (hb : 1 < b) (L : ℝ) (bill : Y → ℝ) :
    ((S.filter fun x => bill (f x) <
      L - Real.logb b (S.filter fun y => f y = f x).card).card : ℝ) ≤
      ∑ z ∈ S.image f, b ^ (L - bill z) := by
  rw [← deficit_moment S f (by linarith) hb.ne' L bill]
  let bad := S.filter fun x => bill (f x) <
    L - Real.logb b (S.filter fun y => f y = f x).card
  calc
    (bad.card : ℝ) = ∑ _x ∈ bad, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ bad,
        b ^ ((L - Real.logb b (S.filter fun y => f y = f x).card) - bill (f x)) :=
      sum_le_sum fun x hx => Real.one_le_rpow hb.le
        (sub_nonneg.mpr (mem_filter.mp hx).2.le)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ =>
      Real.rpow_nonneg (by linarith) _)

open Classical in
/-- A uniform source's fibre-size tail from any upper bound on attained labels.
The confidence parameter may be arbitrary; nonnegative values give useful bounds. -/
theorem tail_of_image_card (S : Finset X) (hS : S.Nonempty) (f : X → Y)
    {b h : ℝ} (hb : 1 < b) (hcount : ((S.image f).card : ℝ) ≤ b ^ h) (t : ℝ) :
    ((S.filter fun x => Real.logb b (S.filter fun y => f y = f x).card <
      Real.logb b S.card - h - t).card : ℝ) / S.card ≤ b ^ (-t) := by
  have hSP : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hbad := bad_card_le S f hb 0 (fun _ => -Real.logb b S.card + h + t)
  have heq : (S.filter fun x => -Real.logb b S.card + h + t <
      0 - Real.logb b (S.filter fun y => f y = f x).card) =
      (S.filter fun x => Real.logb b (S.filter fun y => f y = f x).card <
        Real.logb b S.card - h - t) := by
    ext x
    simp only [mem_filter]
    constructor <;> rintro ⟨hx, ht⟩ <;> exact ⟨hx, by linarith⟩
  rw [heq, sum_const, nsmul_eq_mul] at hbad
  apply (div_le_iff₀ hSP).mpr
  apply hbad.trans
  calc
    _ ≤ b ^ h * b ^ (0 - (-Real.logb b S.card + h + t)) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by linarith) _)
    _ = b ^ (-t) * S.card := by
      rw [← Real.rpow_add (by linarith : 0 < b),
        show h + (0 - (-Real.logb b S.card + h + t)) =
          -t + Real.logb b S.card by ring,
        Real.rpow_add (by linarith : 0 < b), Real.rpow_logb (by linarith) hb.ne' hSP]

open Classical in
/-- Normalizing the fibre size preserves the source-rate coefficient one.
The normalization scale may be any positive real. -/
theorem normalized_tail (S : Finset X) (hS : S.Nonempty) (f : X → Y)
    {b h N : ℝ} (hb : 1 < b) (hN : 0 < N)
    (hcount : ((S.image f).card : ℝ) ≤ b ^ h) (u : ℝ) :
    ((S.filter fun x => Real.logb b (S.filter fun y => f y = f x).card / N <
      Real.logb b S.card / N - h / N - u).card : ℝ) / S.card ≤ b ^ (-u * N) := by
  have htail := tail_of_image_card S hS f hb hcount (u * N)
  have heq : (S.filter fun x => Real.logb b (S.filter fun y => f y = f x).card / N <
      Real.logb b S.card / N - h / N - u) =
      (S.filter fun x => Real.logb b (S.filter fun y => f y = f x).card <
        Real.logb b S.card - h - u * N) := by
    ext x
    simp only [mem_filter, div_lt_iff₀ hN, sub_mul, div_mul_cancel₀ _ hN.ne']
  rw [heq]
  simpa only [neg_mul] using htail

end
end LeanMachine.FinitePartition
