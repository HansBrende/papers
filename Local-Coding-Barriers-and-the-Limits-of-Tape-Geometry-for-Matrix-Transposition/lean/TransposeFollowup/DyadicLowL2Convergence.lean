import TransposeFollowup.DyadicSmoothCutoff
import TransposeFollowup.SmoothBandLinearIdentities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Convergence of the actual low-frequency bands in L2. The error is
estimated on the Fourier side by dominated convergence, not by a claim
that the frequency-truncated functions retain spatial support. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology
set_option autoImplicit false

theorem dyadicLowCutoff_norm_le (N : ℕ) (ξ : ℝ) : ‖dyadicLowCutoff N ξ‖ ≤ 1 :=
  lowFrequencyCutoff_norm_le _

theorem dyadicLowCutoff_eventually_eq_one (ξ : ℝ) :
    ∀ᶠ N : ℕ in atTop, dyadicLowCutoff N ξ = 1 := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_ge_atTop |ξ|)
  exact h.mono (fun N hN => dyadicLowCutoff_eq_one N hN)

theorem dyadicLowCutoff_sub_one_norm_le (N : ℕ) (ξ : ℝ) : ‖dyadicLowCutoff N ξ - 1‖ ≤ 2 := by
  have h := norm_sub_le (dyadicLowCutoff N ξ) 1
  have hχ := dyadicLowCutoff_norm_le N ξ
  norm_num at h
  linarith

theorem dyadicLowCutoff_error_integral_tendsto_zero (F : ComplexL2) :
    Tendsto (fun N => ∫ ξ, ‖(dyadicLowCutoff N ξ - 1) * F ξ‖ ^ 2) atTop (𝓝 0) := by
  have hF := (Lp.memLp F).aestronglyMeasurable
  have hi := ((Lp.memLp F).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul 4
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume) (F := fun N ξ => ‖(dyadicLowCutoff N ξ - 1) * F ξ‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun ξ => 4 * ‖F ξ‖ ^ 2)
    (fun N => (((dyadicLowCutoff N).continuous.sub continuous_const).aestronglyMeasurable.mul hF).norm.pow 2)
    hi ?_ ?_
  · simpa only [integral_zero] using h
  · intro N
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((pow_le_pow_left₀ (norm_nonneg _) (dyadicLowCutoff_sub_one_norm_le N ξ) 2).trans_eq (by norm_num))
      (sq_nonneg _)
  · filter_upwards [] with ξ
    apply tendsto_const_nhds.congr'
    exact (dyadicLowCutoff_eventually_eq_one ξ).mono (fun N hN => by simp [hN])

theorem dyadicLowBand_tendsto {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    Tendsto (fun N => (smoothBand hf hs (dyadicLowCutoff N)
      (dyadicLowCutoff_hasCompactSupport N)).toLp 2 volume) atTop (𝓝 (hf.toLp f)) := by
  have he : Tendsto (fun N => ‖(smoothBand hf hs (dyadicLowCutoff N)
      (dyadicLowCutoff_hasCompactSupport N)).toLp 2 volume - hf.toLp f‖ ^ 2) atTop (𝓝 0) := by
    simp only [smoothBand_sub_input_norm_sq]
    exact dyadicLowCutoff_error_integral_tendsto_zero (𝓕 (hf.toLp f))
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end TransposeFollowup
