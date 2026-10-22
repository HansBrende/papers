import TransposeFollowup.UniformRegularBandIsolation
import TransposeFollowup.SchwartzL2Normalization

/-! The jointly selected band gives an actual normalized Schwartz witness
with quantitative regularity and exact annular Fourier support. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem smoothDyadicBand_fourier_zero_outside (j : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (ξ : ℝ)
    (hξ : |ξ| ≤ (2 : ℝ) ^ j ∨ (2 : ℝ) ^ (j + 2) ≤ |ξ|) :
    (𝓕 (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)) : 𝓢(ℝ, ℂ)) ξ = 0 := by
  rw [smoothBand_fourier, smoothBandSpectrum_apply]
  rcases hξ with hlo | hhi
  · rw [dyadicAnnularCutoff_eq_zero_low j hlo, zero_mul]
  · rw [dyadicAnnularCutoff_eq_zero_high j hhi, zero_mul]

namespace RealMobius

theorem exists_uniform_normalized_regular_high_band :
    ∃ r : ℝ, 0 < r ∧ ∀ (J : ℕ) {c K : ℕ} (G : Fin c → Group), 0 < c →
      (∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2) →
      0 < K → ∀ (f : RealL2), ‖f‖ = 1 →
      ∀ (_hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0),
      (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
      16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2 →
      1 / 2 ≤ inner ℝ (averageOperator G f) f →
      ∃ (j : ℕ) (F : 𝓢(ℝ, ℂ)), J ≤ j ∧ ‖F.toLp 2 volume‖ = 1 ∧
        r < ‖complexAverage G (F.toLp 2 volume)‖ ∧
        schwartzDyadicRegularityCost j F ≤ dyadicRegularityThreshold ∧
        ∀ ξ : ℝ, |ξ| ≤ (2 : ℝ) ^ j ∨ (2 : ℝ) ^ (j + 2) ≤ |ξ| → (𝓕 F : 𝓢(ℝ, ℂ)) ξ = 0 := by
  obtain ⟨r, hr, hselect⟩ := exists_uniform_grid_regular_high_band
  refine ⟨r, hr, ?_⟩
  intro J c K G hc hG hK f hnorm hs hzero hscale hcorr
  obtain ⟨j, hj, hne, hlarge, hcost⟩ := hselect J G hc hG hK f hnorm hs hzero hscale hcorr
  let u := smoothBand (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
    (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j)
  have hQ : schwartzDyadicRegularityCost j u ≤ dyadicRegularityThreshold * ‖u.toLp 2 volume‖ ^ 2 := hcost
  refine ⟨j, schwartzNormalizeL2 u, hj, schwartzNormalizeL2_norm u hne,
    schwartzNormalizeL2_operator_norm_gt u hne (complexAverage G) hlarge,
    schwartzNormalizeL2_regularity_le j u hne hQ, ?_⟩
  intro ξ hξ
  apply schwartzNormalizeL2_fourier_zero
  exact smoothDyadicBand_fourier_zero_outside j _ _ ξ hξ

end RealMobius
end TransposeFollowup
