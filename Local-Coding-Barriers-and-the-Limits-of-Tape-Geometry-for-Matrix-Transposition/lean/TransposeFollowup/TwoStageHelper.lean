import TransposeFollowup.TwoStageRows
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! One global helper may choose all maps and orders. It is counted once,
through its attained image on the correct input family. The exact finite
count implies the constant-fraction helper-or-deficit toll of unit216.
-/

namespace TransposeFollowup

set_option autoImplicit false
open Classical
open scoped BigOperators

structure TwoStageHelper (n b : ℕ) (H : Type*) where
  helper : FiniteMatrix n b → H
  branch : H → TwoStageRows n (Row n b)

namespace TwoStageHelper

variable {n b : ℕ} {H : Type*} (T : TwoStageHelper n b H)

noncomputable def apply (x : FiniteMatrix n b) : FiniteMatrix n b :=
  (T.branch (T.helper x)).apply x

def CorrectOn (F : Finset (FiniteMatrix n b)) : Prop :=
  ∀ x ∈ F, T.apply x = transposed x

theorem correct_family_card (F : Finset (FiniteMatrix n b)) (hc : T.CorrectOn F)
    (r : ℕ) (hr : r ≤ n) :
    F.card ≤ (F.image T.helper).card * 2 ^ ((n - r) * n * b + r * r * b) := by
  rw [Finset.card_eq_sum_card_image T.helper F]
  calc
    _ ≤ ∑ z ∈ F.image T.helper, 2 ^ ((n - r) * n * b + r * r * b) := by
      apply Finset.sum_le_sum
      intro z _
      apply (T.branch z).correct_family_card
        (F.filter (fun x => T.helper x = z)) _ r hr
      intro x hx
      obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx
      simpa only [apply, he] using hc x hx
    _ = _ := by simp

theorem exponent_decomposition (n b r : ℕ) (hr : r ≤ n) :
    (n-r)*n*b + r*r*b + b*r*(n-r) = n*n*b := by
  have hn := Nat.sub_add_cancel hr
  calc
    _ = (n-r)*n*b + r*((n-r)+r)*b := by ring
    _ = (n-r)*n*b + r*n*b := by rw [hn]
    _ = ((n-r)+r)*n*b := by ring
    _ = _ := by rw [hn]

theorem correct_family_count_toll (F : Finset (FiniteMatrix n b)) (hc : T.CorrectOn F)
    (r : ℕ) (hr : r ≤ n) :
    F.card * 2 ^ (b * r * (n - r)) ≤ (F.image T.helper).card * 2 ^ (n * n * b) := by

  calc
    _ ≤ ((F.image T.helper).card * 2 ^ ((n - r) * n * b + r * r * b)) *
        2 ^ (b * r * (n - r)) := Nat.mul_le_mul_right _ (T.correct_family_card F hc r hr)
    _ = _ := by rw [mul_assoc, ← pow_add, exponent_decomposition n b r hr]

/-- Exact deficit uses logarithmic cardinality, with no rounding or density
loss. Only helper values attained on F are charged; H need not be finite. -/
theorem helper_deficit_bound (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : T.CorrectOn F) (g r : ℕ) (hg : (F.image T.helper).card ≤ 2 ^ g)
    (hr : r ≤ n) :
    (n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2 + g ≥
      (b * r * (n - r) : ℕ) := by
  have hFpos : 0 < (F.card : ℝ) := by
    have hp : 0 < F.card := by simpa only [Fintype.card_coe] using Fintype.card_pos (α := F)
    exact_mod_cast hp
  have hcN : F.card * 2 ^ (b * r * (n - r)) ≤ 2 ^ (g + n * n * b) := by
    calc
      _ ≤ (F.image T.helper).card * 2 ^ (n * n * b) := T.correct_family_count_toll F hc r hr
      _ ≤ 2 ^ g * 2 ^ (n * n * b) := Nat.mul_le_mul_right _ hg
      _ = _ := (pow_add _ _ _).symm
  have hcR : (F.card : ℝ) * 2 ^ (b * r * (n - r)) ≤ 2 ^ (g + n * n * b) := by
    exact_mod_cast hcN
  have hl := Real.log_le_log (mul_pos hFpos (by positivity)) hcR
  rw [Real.log_mul hFpos.ne' (by positivity), Real.log_pow, Real.log_pow] at hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_right hlog).mp
  field_simp
  push_cast at hl ⊢
  nlinarith

end TwoStageHelper

theorem half_product_eq_floor_quarter (n : ℕ) :
    (n / 2) * (n - n / 2) = n * n / 4 := by
  have hdiv := Nat.mod_add_div n 2
  have hmod := Nat.mod_lt n (by norm_num : 0 < 2)
  have hsub := Nat.sub_add_cancel (Nat.div_le_self n 2)
  have he : n * n = 4 * ((n / 2) * (n - n / 2)) + n % 2 := by
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;> nlinarith
  omega

namespace TwoStageHelper

variable {n b : ℕ} {H : Type*} (T : TwoStageHelper n b H)

theorem quarter_count_toll (F : Finset (FiniteMatrix n b)) (hc : T.CorrectOn F) :
    F.card * 2 ^ (b * (n * n / 4)) ≤ (F.image T.helper).card * 2 ^ (n * n * b) := by
  have h := T.correct_family_count_toll F hc (n / 2) (Nat.div_le_self n 2)
  rwa [mul_assoc b, half_product_eq_floor_quarter] at h

/-- Unit216's exact helper bound for the fully specified two-stage model.
All maps and both orders may depend on the single global helper. -/
theorem quarter_helper_deficit_bound (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (hc : T.CorrectOn F) (g : ℕ) (hg : (F.image T.helper).card ≤ 2 ^ g) :
    (n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2 + g ≥
      (b * (n * n / 4) : ℕ) := by
  have h := T.helper_deficit_bound F hc g (n / 2) hg (Nat.div_le_self n 2)
  rwa [mul_assoc b, half_product_eq_floor_quarter] at h

/-- The manuscript's density formulation, for an arbitrary real deficit
upper bound D. No integrality or rounding assumption on D is needed. -/
theorem quarter_helper_bound_of_density (F : Finset (FiniteMatrix n b))
    (hc : T.CorrectOn F) (D : ℝ) (g : ℕ)
    (hF : (2 : ℝ) ^ ((n * n * b : ℕ) - D) ≤ F.card)
    (hg : (F.image T.helper).card ≤ 2 ^ g) :
    D + g ≥ (b * (n * n / 4) : ℕ) := by
  have hp : 0 < (F.card : ℝ) := lt_of_lt_of_le (by positivity) hF
  have hpn : 0 < F.card := by exact_mod_cast hp
  have : Nonempty F := Finset.Nonempty.to_subtype (Finset.card_pos.mp hpn)
  have h := T.quarter_helper_deficit_bound F hc g hg
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ ((n * n * b : ℕ) - D)) hF
  rw [Real.log_rpow (by norm_num)] at hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : (n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2 ≤ D := by
    have he : (n * n * b : ℕ) - D ≤ Real.log (F.card : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog).mpr hl
    linarith
  linarith

end TwoStageHelper
end TransposeFollowup
