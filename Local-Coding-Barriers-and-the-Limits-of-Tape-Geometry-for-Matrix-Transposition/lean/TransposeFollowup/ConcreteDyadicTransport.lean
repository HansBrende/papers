import TransposeFollowup.DyadicCoefficientBounds
import TransposeFollowup.FiniteBandTransportEnergy

/-! The transported derivative square sum for the concrete dyadic family.
All cutoff coefficient hypotheses are discharged; constants depend only
on the fixed bump and the displayed SL2 matrix. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

noncomputable def dyadicCutoffDerivativeBound (n : ℕ) : ℝ :=
  3 * (SchwartzMap.seminorm ℝ 0 n baseAnnularCutoff) ^ 2

noncomputable def dyadicFrequencyDerivativeBound (n : ℕ) : ℝ :=
  3 * (SchwartzMap.seminorm ℝ 0 n (schwartzFrequencyDerivative baseAnnularCutoff)) ^ 2

theorem dyadicCutoffDerivativeBound_nonneg (n : ℕ) : 0 ≤ dyadicCutoffDerivativeBound n := by
  unfold dyadicCutoffDerivativeBound
  positivity

theorem dyadicFrequencyDerivativeBound_nonneg (n : ℕ) : 0 ≤ dyadicFrequencyDerivativeBound n := by
  unfold dyadicFrequencyDerivativeBound
  positivity

theorem dyadic_smoothBand_energy_le (s : Finset ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∑ j ∈ s, ‖(smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖ ^ 2) ≤
      dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2 := by
  have hb (x : ℝ) : (∑ j ∈ s, (1 : ℝ) * ‖dyadicAnnularCutoff j x‖ ^ 2) ≤
      dyadicCutoffDerivativeBound 0 := by
    simpa only [one_mul, iteratedDeriv_zero, dyadicAnnularCutoff, dyadicCutoffDerivativeBound] using
      finite_annular_dilation_derivative_energy_le s baseAnnularCutoff
        baseAnnularCutoff_tsupport_subset 0 x
  simpa only [one_mul] using finite_smoothBand_energy_le s dyadicAnnularCutoff
    dyadicAnnularCutoff_hasCompactSupport (fun _ => 1) hf hs hb

namespace RealMobius

noncomputable def dyadicTransportConstant (g : Group) : ℝ :=
  16 * (g 0 0) ^ 4 * dyadicFrequencyDerivativeBound 0 +
  16 * (g 1 0) ^ 4 * (((2 * Real.pi) ^ 4)⁻¹ *
    (3 * dyadicFrequencyDerivativeBound 0 * (2 * Real.pi) ^ 4 +
      12 * dyadicFrequencyDerivativeBound 1 * (2 * Real.pi) ^ 2 +
      3 * dyadicFrequencyDerivativeBound 2)) +
  4 * (g 1 0) ^ 2 * (g 0 0) ^ 2 * dyadicCutoffDerivativeBound 0 +
  4 * (g 1 0) ^ 4 * (((2 * Real.pi) ^ 2)⁻¹ *
    (2 * dyadicCutoffDerivativeBound 0 * (2 * Real.pi) ^ 2 + 2 * dyadicCutoffDerivativeBound 1))

theorem dyadicTransportConstant_nonneg (g : Group) : 0 ≤ dyadicTransportConstant g := by
  unfold dyadicTransportConstant dyadicFrequencyDerivativeBound dyadicCutoffDerivativeBound
  positivity

theorem dyadic_smoothBand_transport_energy_le (s : Finset ℕ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (g : Group) :
    (∑ j ∈ s, dyadicBandWeight j *
      ‖(schwartzDifferentialTransport g (smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j))).toLp 2 volume‖ ^ 2) ≤
      dyadicTransportConstant g * ‖hf.toLp f‖ ^ 2 := by
  apply finite_smoothBand_transport_energy_le s dyadicAnnularCutoff
    dyadicAnnularCutoff_hasCompactSupport dyadicBandWeight (fun j _ => dyadicBandWeight_nonneg j)
    hf hs g (dyadicCutoffDerivativeBound_nonneg 0) (dyadicCutoffDerivativeBound_nonneg 1)
    (dyadicFrequencyDerivativeBound_nonneg 0) (dyadicFrequencyDerivativeBound_nonneg 1)
    (dyadicFrequencyDerivativeBound_nonneg 2)
  · intro x
    simpa only [iteratedDeriv_zero, dyadicCutoffDerivativeBound, dyadicFrequencyDerivativeBound] using dyadicAnnularCutoff_derivative_square_sum_le s 0 x
  · intro x
    simpa only [iteratedDeriv_one, dyadicCutoffDerivativeBound, dyadicFrequencyDerivativeBound] using dyadicAnnularCutoff_derivative_square_sum_le s 1 x
  · intro x
    simpa only [iteratedDeriv_zero, dyadicCutoffDerivativeBound, dyadicFrequencyDerivativeBound] using dyadicAnnularCutoff_frequency_derivative_square_sum_le s 0 x
  · intro x
    simpa only [iteratedDeriv_one, dyadicCutoffDerivativeBound, dyadicFrequencyDerivativeBound] using dyadicAnnularCutoff_frequency_derivative_square_sum_le s 1 x
  · exact dyadicAnnularCutoff_frequency_derivative_square_sum_le s 2

theorem dyadic_smoothBand_highFrequency_energy_le (s : Finset ℕ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (g : Group) (R : ℕ → ℝ) (hR : ∀ j ∈ s, 0 ≤ R j) :
    (∑ j ∈ s, dyadicBandWeight j * ((2 * Real.pi * R j) ^ 2 *
      ‖highFrequency (Icc (-R j) (R j)) measurableSet_Icc
        (schwartzActionL2 g (smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)))‖ ^ 2)) ≤
      dyadicTransportConstant g * ‖hf.toLp f‖ ^ 2 :=
  (finite_schwartzActionL2_highFrequency_energy_le s
    (fun j => smoothBand hf hs (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j))
    dyadicBandWeight R (fun j _ => dyadicBandWeight_nonneg j) hR g).trans
      (dyadic_smoothBand_transport_energy_le s hf hs g)

end RealMobius
end TransposeFollowup
