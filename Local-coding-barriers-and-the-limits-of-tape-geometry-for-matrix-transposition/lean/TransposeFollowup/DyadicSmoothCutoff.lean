import TransposeFollowup.DyadicSchwartzDilation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! A fixed smooth low-frequency cutoff and actual dyadic annular cutoffs.
The definitions carry their Schwartz and compact-support proofs. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped ContDiff
set_option autoImplicit false

def unitFrequencyBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def lowFrequencyCutoff : 𝓢(ℝ, ℂ) :=
  (unitFrequencyBump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp unitFrequencyBump.contDiff)

theorem lowFrequencyCutoff_apply (x : ℝ) :
    lowFrequencyCutoff x = (unitFrequencyBump x : ℂ) := rfl

theorem lowFrequencyCutoff_hasCompactSupport : HasCompactSupport (⇑lowFrequencyCutoff) :=
  unitFrequencyBump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem lowFrequencyCutoff_norm_le (x : ℝ) : ‖lowFrequencyCutoff x‖ ≤ 1 := by
  rw [lowFrequencyCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg unitFrequencyBump.nonneg]
  exact unitFrequencyBump.le_one

theorem lowFrequencyCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : lowFrequencyCutoff x = 1 := by
  rw [lowFrequencyCutoff_apply, unitFrequencyBump.one_of_mem_closedBall]
  · norm_num
  · simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, unitFrequencyBump] using hx

theorem lowFrequencyCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : lowFrequencyCutoff x = 0 := by
  rw [lowFrequencyCutoff_apply, unitFrequencyBump.zero_of_le_dist]
  · norm_num
  · simpa only [Real.dist_eq, sub_zero, unitFrequencyBump] using hx

noncomputable def dyadicLowCutoff (j : ℕ) : 𝓢(ℝ, ℂ) :=
  schwartzDyadicDilate lowFrequencyCutoff j

noncomputable def baseAnnularCutoff : 𝓢(ℝ, ℂ) := dyadicLowCutoff 1 - lowFrequencyCutoff

noncomputable def dyadicAnnularCutoff (j : ℕ) : 𝓢(ℝ, ℂ) :=
  schwartzDyadicDilate baseAnnularCutoff j

theorem dyadicLowCutoff_hasCompactSupport (j : ℕ) : HasCompactSupport (⇑(dyadicLowCutoff j)) :=
  schwartzDyadicDilate_hasCompactSupport _ lowFrequencyCutoff_hasCompactSupport j

theorem baseAnnularCutoff_hasCompactSupport : HasCompactSupport (⇑baseAnnularCutoff) :=
  (dyadicLowCutoff_hasCompactSupport 1).sub lowFrequencyCutoff_hasCompactSupport

theorem dyadicAnnularCutoff_hasCompactSupport (j : ℕ) :
    HasCompactSupport (⇑(dyadicAnnularCutoff j)) :=
  schwartzDyadicDilate_hasCompactSupport _ baseAnnularCutoff_hasCompactSupport j

theorem dyadicLowCutoff_eq_one (j : ℕ) {x : ℝ} (hx : |x| ≤ (2 : ℝ) ^ j) :
    dyadicLowCutoff j x = 1 := by
  apply lowFrequencyCutoff_eq_one
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans_eq (inv_mul_cancel₀ (by positivity))

theorem dyadicLowCutoff_eq_zero (j : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ (j + 1) ≤ |x|) :
    dyadicLowCutoff j x = 0 := by
  apply lowFrequencyCutoff_eq_zero
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  have h := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹)
  simpa only [pow_succ, ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_mul] using h

theorem dyadicAnnularCutoff_difference (j : ℕ) :
    dyadicAnnularCutoff j = dyadicLowCutoff (j + 1) - dyadicLowCutoff j := by
  change schwartzDyadicDilate (schwartzDyadicDilate lowFrequencyCutoff 1 - lowFrequencyCutoff) j = _
  rw [schwartzDyadicDilate_sub, schwartzDyadicDilate_add_index]
  rfl

theorem dyadicAnnularCutoff_eq_zero_low (j : ℕ) {x : ℝ} (hx : |x| ≤ (2 : ℝ) ^ j) :
    dyadicAnnularCutoff j x = 0 := by
  rw [dyadicAnnularCutoff_difference]
  change dyadicLowCutoff (j + 1) x - dyadicLowCutoff j x = 0
  rw [dyadicLowCutoff_eq_one j hx, dyadicLowCutoff_eq_one (j + 1)]
  · exact sub_self _
  · exact hx.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))

theorem dyadicAnnularCutoff_eq_zero_high (j : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ (j + 2) ≤ |x|) :
    dyadicAnnularCutoff j x = 0 := by
  rw [dyadicAnnularCutoff_difference]
  change dyadicLowCutoff (j + 1) x - dyadicLowCutoff j x = 0
  rw [dyadicLowCutoff_eq_zero (j + 1) hx, dyadicLowCutoff_eq_zero j]
  · exact sub_self _
  · apply le_trans _ hx
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

theorem dyadicAnnularCutoff_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, dyadicAnnularCutoff j) = dyadicLowCutoff N - lowFrequencyCutoff := by
  induction N with
  | zero => simp [dyadicLowCutoff, schwartzDyadicDilate_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, dyadicAnnularCutoff_difference]
    abel

end TransposeFollowup
