import TransposeFollowup.SchwartzDyadicRegularity

/-! A concrete summable regularity cost for later joint band selection.
It controls the first spatial moment and the derivative terms in the
quadratic Mobius differential transport, at their dyadic scale. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

noncomputable def dyadicBandRegularityCost {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (j : ℕ) : ℝ :=
  schwartzDyadicRegularityCost j
    (smoothBand hf hs (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j))

theorem dyadicBandRegularityCost_nonneg {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (j : ℕ) :
    0 ≤ dyadicBandRegularityCost hf hs j :=
  schwartzDyadicRegularityCost_nonneg j _

noncomputable def dyadicBandRegularityConstant : ℝ :=
  dyadicCutoffDerivativeBound 0 +
    ((2 * Real.pi) ^ 2)⁻¹ *
      (2 * dyadicCutoffDerivativeBound 0 * (2 * Real.pi) ^ 2 + 2 * dyadicCutoffDerivativeBound 1) +
    dyadicFrequencyDerivativeBound 0 +
    ((2 * Real.pi) ^ 4)⁻¹ *
      (3 * dyadicFrequencyDerivativeBound 0 * (2 * Real.pi) ^ 4 +
        12 * dyadicFrequencyDerivativeBound 1 * (2 * Real.pi) ^ 2 + 3 * dyadicFrequencyDerivativeBound 2)

theorem dyadicBandRegularityConstant_nonneg : 0 ≤ dyadicBandRegularityConstant := by
  unfold dyadicBandRegularityConstant dyadicCutoffDerivativeBound dyadicFrequencyDerivativeBound
  positivity

theorem dyadicBandRegularityCost_sum_le (s : Finset ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∑ j ∈ s, dyadicBandRegularityCost hf hs j) ≤ dyadicBandRegularityConstant * ‖hf.toLp f‖ ^ 2 := by
  let u := fun j => smoothBand hf hs (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j)
  have hb (n : ℕ) (ξ : ℝ) : (∑ j ∈ s, (1 : ℝ) * ‖iteratedDeriv n (dyadicAnnularCutoff j) ξ‖ ^ 2) ≤
      dyadicCutoffDerivativeBound n := by
    simpa only [one_mul, dyadicAnnularCutoff, dyadicCutoffDerivativeBound] using
      finite_annular_dilation_derivative_energy_le s baseAnnularCutoff baseAnnularCutoff_tsupport_subset n ξ
  have hq (n : ℕ) (ξ : ℝ) : (∑ j ∈ s, dyadicBandWeight j *
      ‖iteratedDeriv n (schwartzFrequencyDerivative (dyadicAnnularCutoff j)) ξ‖ ^ 2) ≤
      dyadicFrequencyDerivativeBound n := dyadicAnnularCutoff_frequency_derivative_square_sum_le s n ξ
  have hnorm := dyadic_smoothBand_energy_le s hf hs
  have hmoment : (∑ j ∈ s, ∫ x, x ^ 2 * ‖u j x‖ ^ 2) ≤
      (((2 * Real.pi) ^ 2)⁻¹ * (2 * dyadicCutoffDerivativeBound 0 * (2 * Real.pi) ^ 2 +
        2 * dyadicCutoffDerivativeBound 1)) * ‖hf.toLp f‖ ^ 2 := by
    simpa only [one_mul, iteratedDeriv_zero, iteratedDeriv_one] using
      finite_smoothBand_first_moment_energy_le s dyadicAnnularCutoff dyadicAnnularCutoff_hasCompactSupport
        (fun _ => 1) (fun _ _ => by norm_num) hf hs
        (dyadicCutoffDerivativeBound_nonneg 0) (dyadicCutoffDerivativeBound_nonneg 1) (hb 0)
        (by simpa only [iteratedDeriv_one] using hb 1)
  have hd : (∑ j ∈ s, dyadicBandWeight j * ∫ x, ‖deriv (u j) x‖ ^ 2) ≤
      dyadicFrequencyDerivativeBound 0 * ‖hf.toLp f‖ ^ 2 :=
    finite_smoothBand_deriv_energy_le s dyadicAnnularCutoff dyadicAnnularCutoff_hasCompactSupport
      dyadicBandWeight hf hs (hq 0)
  have hdm : (∑ j ∈ s, dyadicBandWeight j * ∫ x, x ^ 4 * ‖deriv (u j) x‖ ^ 2) ≤
      (((2 * Real.pi) ^ 4)⁻¹ *
        (3 * dyadicFrequencyDerivativeBound 0 * (2 * Real.pi) ^ 4 +
          12 * dyadicFrequencyDerivativeBound 1 * (2 * Real.pi) ^ 2 + 3 * dyadicFrequencyDerivativeBound 2)) *
        ‖hf.toLp f‖ ^ 2 :=
    finite_smoothBand_deriv_second_moment_energy_le s dyadicAnnularCutoff dyadicAnnularCutoff_hasCompactSupport
      dyadicBandWeight (fun j _ => dyadicBandWeight_nonneg j) hf hs
      (dyadicFrequencyDerivativeBound_nonneg 0) (dyadicFrequencyDerivativeBound_nonneg 1)
      (dyadicFrequencyDerivativeBound_nonneg 2) (hq 0)
      (by simpa only [iteratedDeriv_one] using hq 1) (hq 2)
  have h := add_le_add (add_le_add hnorm hmoment) (add_le_add hd hdm)
  convert h using 1
  · simp only [dyadicBandRegularityCost, schwartzDyadicRegularityCost, mul_add, Finset.sum_add_distrib, u]
  · unfold dyadicBandRegularityConstant
    ring

end TransposeFollowup
