import TransposeFollowup.FiniteMultiplierEnergy
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Product-rule identities for the actual compact frequency spectrum.
They expose the cutoff derivatives needed for weighted square-sum bounds. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ContDiff
set_option autoImplicit false

theorem smoothBandSpectrum_iteratedDeriv {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (n : ℕ) (ξ : ℝ) :
    iteratedDeriv n (smoothBandSpectrum hf hs χ hc) ξ =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i χ ξ *
        iteratedDeriv (n - i) (𝓕 f) ξ := by
  change iteratedDeriv n ((⇑χ) * 𝓕 f) ξ = _
  exact iteratedDeriv_mul ((χ.smooth n).contDiffAt)
    (((unit_supported_fourier_smooth hf hs).of_le (by simp)).contDiffAt)

theorem smoothBandSpectrum_deriv {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (ξ : ℝ) :
    deriv (smoothBandSpectrum hf hs χ hc) ξ =
      χ ξ * deriv (𝓕 f) ξ + deriv χ ξ * 𝓕 f ξ := by
  simpa [Finset.sum_range_succ, iteratedDeriv_one, iteratedDeriv_zero] using
    smoothBandSpectrum_iteratedDeriv hf hs χ hc 1 ξ

theorem smoothBandSpectrum_secondDeriv {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (ξ : ℝ) :
    iteratedDeriv 2 (smoothBandSpectrum hf hs χ hc) ξ =
      χ ξ * iteratedDeriv 2 (𝓕 f) ξ + 2 * deriv χ ξ * deriv (𝓕 f) ξ +
        iteratedDeriv 2 χ ξ * 𝓕 f ξ := by
  simpa [Finset.sum_range_succ, iteratedDeriv_one, iteratedDeriv_zero] using
    smoothBandSpectrum_iteratedDeriv hf hs χ hc 2 ξ

end TransposeFollowup
