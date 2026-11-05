import TapeStorageRates.PatchPrediction

/-! # Prediction advantage and overlap at near-unit rate -/

namespace TapeStorageRates
open Set TransposeFollowup
open scoped BigOperators

set_option autoImplicit false

private theorem binEntropy_gap_half {e : ℝ} (he : e ∈ Icc 0 (2:ℝ)⁻¹) :
    2 * (2⁻¹-e)^2 ≤ Real.log 2 - Real.binEntropy e := by
  let F (x : ℝ) := Real.binEntropy x + 2 * (2⁻¹-x)^2
  let f' (x : ℝ) := Real.log (1-x) - Real.log x - (2-4*x)
  have hmono : MonotoneOn F (Icc 0 2⁻¹) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc _ _)
    · dsimp [F]; fun_prop
    · intro x hx
      rw [interior_Icc] at hx
      have h0 : x ≠ 0 := hx.1.ne'
      have h1 : x ≠ 1 := by have := hx.2; norm_num at this; linarith
      have hsq : HasDerivAt (fun y : ℝ => 2 * (2⁻¹-y)^2) (-(2-4*x)) x := by
        convert (((hasDerivAt_const x ((2:ℝ)⁻¹)).sub (hasDerivAt_id x)).pow 2).const_mul 2 using 1
        · funext y; rfl
        · dsimp; ring
      exact ((Real.hasDerivAt_binEntropy h0 h1).add hsq).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : x < 1 := by have := hx.2; norm_num at this; linarith
      let z := (1-2*x)/x
      have hz : 0 ≤ z := div_nonneg (by have := hx.2; norm_num at this; linarith) hx0.le
      have hfrac : 2*z/(z+2) = 2-4*x := by
        apply (div_eq_iff (by linarith : z+2 ≠ 0)).mpr
        dsimp [z]; field_simp; ring
      have harg : 1+z = (1-x)/x := by dsimp [z]; field_simp; ring
      have h := Real.le_log_one_add_of_nonneg hz
      rw [hfrac,harg,Real.log_div (sub_ne_zero.mpr hx1.ne') hx0.ne'] at h
      exact sub_nonneg.mpr h
  have h := hmono he (right_mem_Icc.mpr (by norm_num)) he.2
  simp [F] at h
  linarith

/-- Quadratic form of the binary entropy deficit, in nats, on the full unit interval. -/
theorem binEntropy_quadratic_gap {e : ℝ} (he : e ∈ Icc 0 1) :
    2 * (2⁻¹ - e)^2 ≤ Real.log 2 - Real.binEntropy e := by
  by_cases h : e ≤ 2⁻¹
  · exact binEntropy_gap_half ⟨he.1,h⟩
  · have hp : 1-e ∈ Icc 0 (2:ℝ)⁻¹ := ⟨sub_nonneg.mpr he.2, by linarith⟩
    have hc := binEntropy_gap_half hp
    rw [Real.binEntropy_one_sub] at hc
    convert hc using 1
    ring

namespace PatchPredictor

open Finset

variable {Ω V J : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype J] {w r : ℕ}
variable (D : PatchPredictor V J w r)

/-- The squared advantage over a fair guess times the number of scored
occurrences is at most ln(2) times overlap times the binary entropy deficit. -/
theorem advantage_sq_bound (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) :
    D.targetCount * (2⁻¹ - D.meanError p X)^2 ≤
      Real.log 2 * r * (Fintype.card V - observationEntropy p X / Real.log 2) := by
  have hu : D.meanError p X ≤ 1 := by
    apply D.meanError_le_of_mistakeCount p hp hp1 X zero_le_one
    intro x
    rw [one_mul]
    exact_mod_cast card_le_univ (univ.filter fun i => D.missed i (X x) = true)
  have hs := mul_le_mul_of_nonneg_left
    (binEntropy_quadratic_gap ⟨D.meanError_nonneg p hp X,hu⟩) (Nat.cast_nonneg D.targetCount)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := mul_le_mul_of_nonneg_right (D.prediction_deficit p hp hp1 X) hlog.le
  rw [one_sub_div hlog.ne'] at hb
  have ham : D.targetCount * ((Real.log 2 - Real.binEntropy (D.meanError p X)) / Real.log 2)
      * Real.log 2 = D.targetCount * (Real.log 2 - Real.binEntropy (D.meanError p X)) := by
    field_simp
  rw [ham] at hb
  nlinarith only [hs,hb]

/-- The average accuracy of either a predictor or its bitwise complement
deviates from chance by at most the square root of the charged deficit per target. -/
theorem advantage_le_sqrt (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) (hm : 0 < D.targetCount) :
    |2⁻¹ - D.meanError p X| ≤
      Real.sqrt (Real.log 2 * r * (Fintype.card V - observationEntropy p X / Real.log 2)
        / D.targetCount) := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact (le_div_iff₀' (show (0:ℝ) < D.targetCount by exact_mod_cast hm)).mpr
    (D.advantage_sq_bound p hp hp1 X)

/-- For a source whose relative entropy deficit is at most A/s, scoring
a fraction α of target occurrences costs overlap at least α(1-h₂(e))s/(2A)
when A is positive. The product form also permits zero deficit. -/
theorem overlap_of_near_unit_rate (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → V → Bool) {α s A : ℝ}
    (hn : 0 < Fintype.card V) (hs : 0 ≤ s) (hcover : α * Fintype.card V ≤ D.targetCount)
    (hrate : (Fintype.card V - observationEntropy p X / Real.log 2) * s ≤ A * Fintype.card V) :
    α * (1 - Real.binEntropy (D.meanError p X) / Real.log 2) * s ≤ 2 * r * A := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcredit : 0 ≤ 1 - Real.binEntropy (D.meanError p X) / Real.log 2 :=
    sub_nonneg.mpr ((div_le_one hlog).mpr Real.binEntropy_le_log_two)
  have hsc := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right hcover hcredit).trans (D.prediction_deficit p hp hp1 X)) hs
  have hbudget := mul_le_mul_of_nonneg_left hrate (show 0 ≤ 2*(r:ℝ) by positivity)
  apply (mul_le_mul_iff_of_pos_right (show (0:ℝ) < Fintype.card V by exact_mod_cast hn)).mp
  nlinarith only [hsc,hbudget]

end PatchPredictor

end TapeStorageRates
