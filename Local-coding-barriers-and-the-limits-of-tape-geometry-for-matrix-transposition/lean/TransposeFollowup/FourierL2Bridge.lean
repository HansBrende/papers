import TransposeFollowup.GridFourierCancellation
import Mathlib.Analysis.Fourier.LpSpace

/-! The classical Fourier integral and the L2 Fourier transform agree on
L1 intersection L2. The identification is proved through smooth tests and
the already formalized tempered-distribution Fourier compatibility. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ContDiff
set_option autoImplicit false

noncomputable abbrev ComplexL2 := Lp ℂ 2 (volume : Measure ℝ)

theorem L2_fourier_pairing (f : ComplexL2) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * (𝓕 f) x) = ∫ x, (𝓕 φ) x * f x := by
  have h := congrArg (fun u : 𝓢'(ℝ, ℂ) => u φ) (Lp.fourier_toTemperedDistribution_eq f)
  simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] using h.symm

theorem classical_fourier_pairing {f : ℝ → ℂ} (hf : Integrable f) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 φ) x * f x) = ∫ x, φ x * 𝓕 f x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner φ.integrable hf

theorem L2_fourier_coe_ae (f : ComplexL2) (hf : Integrable (f : ℝ → ℂ)) :
    ⇑(𝓕 f : ComplexL2) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num))
    (classical_fourier_continuous hf).locallyIntegrable
  intro g hg hc
  have hcomp : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hcomp.toSchwartzMap hdiff
  have he : (∫ x, φ x * (𝓕 f) x) = ∫ x, φ x * 𝓕 (f : ℝ → ℂ) x :=
    (L2_fourier_pairing f φ).trans (classical_fourier_pairing hf φ)
  have hφ : ∀ x, φ x = (g x : ℂ) := fun _ => rfl
  simp_rw [hφ] at he
  simpa only [Complex.real_smul] using he

theorem toLp_fourier_coe_ae {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2 volume) :
    ⇑(𝓕 (hf2.toLp f) : ComplexL2) =ᵐ[volume] 𝓕 f := by
  have hrep := hf2.coeFn_toLp
  have hfi : Integrable (hf2.toLp f : ℝ → ℂ) := hf.congr hrep.symm
  exact (L2_fourier_coe_ae (hf2.toLp f) hfi).trans
    (Filter.Eventually.of_forall (Real.fourier_congr_ae hrep))

end TransposeFollowup
