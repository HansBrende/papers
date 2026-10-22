import TransposeFollowup.ComplexifiedL2Operator
import TransposeFollowup.NormalizedGridFourier

/-! The exact normalized grid input has an actual high-frequency L2
component retaining positive Mobius-average correlation. This connects
the previously separate Fourier and correlation estimates. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped FourierTransform
set_option autoImplicit false

namespace RealMobius

theorem ofRealL2_integrable (f : RealL2)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    Integrable (ofRealL2 f : ℝ → ℂ) := by
  apply integrable_of_unit_supported_L2 (Lp.memLp (ofRealL2 f))
  filter_upwards [ofRealL2_coe f, hsupport] with x hx hs hu
  rw [hx, hs hu, Complex.ofReal_zero]

theorem ofRealL2_lowFrequency_norm_sq (f : RealL2)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (R : ℝ) :
    ‖lowFrequency (Icc (-R) R) measurableSet_Icc (ofRealL2 f)‖ ^ 2 =
      ∫ ξ in Icc (-R) R, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 := by
  rw [lowFrequency_norm_sq_classical _ _ _ (ofRealL2_integrable f hsupport)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2) (Real.fourier_congr_ae (ofRealL2_coe f) ξ))

theorem grid_lowFrequency_norm_le {K : ℕ} (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hscale : 2048 * Real.pi ^ 2 * R ^ 3 ≤ (K : ℝ) ^ 2) :
    ‖lowFrequency (Icc (-R) R) measurableSet_Icc (ofRealL2 f)‖ ≤ 1 / 16 := by
  have hb := normalized_realL2_low_fourier_small hK f hnorm hsupport hzero R hR hscale
  rw [← ofRealL2_lowFrequency_norm_sq f hsupport R] at hb
  nlinarith

theorem grid_highFrequency_correlation {c K : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hscale : 2048 * Real.pi ^ 2 * R ^ 3 ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    let g := highFrequency (Icc (-R) R) measurableSet_Icc (ofRealL2 f)
    95 / 256 ≤ inner ℝ (complexAverage G g) g := by
  apply correlation_survives_small_change (complexAverage G) (complexAverage_norm_le G hc)
    (f := ofRealL2 f)
  · rw [ofRealL2_norm, hnorm]
  · rw [norm_sub_highFrequency]
    exact grid_lowFrequency_norm_le hK f hnorm hsupport hzero R hR hscale
  · rwa [complexAverage_real_correlation]

/-- Explicit grid-frequency separation gives a high-frequency component
with all loss bounded, without assuming a spectral-gap theorem. -/
theorem exists_highFrequency_witness {c K : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hscale : 2048 * Real.pi ^ 2 * R ^ 3 ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    ∃ g : ComplexL2, ‖g‖ ≤ 1 ∧ (∀ᵐ ξ ∂volume, ξ ∈ Icc (-R) R → (𝓕 g : ComplexL2) ξ = 0) ∧
      ‖ofRealL2 f - g‖ ≤ 1 / 16 ∧ 95 / 256 ≤ inner ℝ (complexAverage G g) g := by
  refine ⟨highFrequency (Icc (-R) R) measurableSet_Icc (ofRealL2 f),
    ?_, highFrequency_fourier_zero_on _ _ _, ?_,
    grid_highFrequency_correlation G hc hK f hnorm hsupport hzero R hR hscale hcorr⟩
  · simpa only [ofRealL2_norm, hnorm] using highFrequency_norm_le (Icc (-R) R) measurableSet_Icc (ofRealL2 f)
  · rw [norm_sub_highFrequency]
    exact grid_lowFrequency_norm_le hK f hnorm hsupport hzero R hR hscale

end RealMobius
end TransposeFollowup
