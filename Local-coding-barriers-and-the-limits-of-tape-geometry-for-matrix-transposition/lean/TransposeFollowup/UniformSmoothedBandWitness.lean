import TransposeFollowup.NormalizedRegularBandWitness
import TransposeFollowup.MobiusSmoothedDensity
import TransposeFollowup.DyadicSmoothingScale

/-! The selected normalized regular band has a concrete Haar-smoothed walk
with a dyadic length above any prescribed logarithmic flattening threshold,
once the generator scale is sufficiently small. This is a lower bound;
neither flatness nor the spectral-gap contradiction is asserted. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_uniform_smoothed_regular_high_band :
    ∃ r : ℝ, 0 < r ∧ ∀ Nmin : ℕ, ∃ N J₀ : ℕ, 0 < N ∧ Nmin ≤ N ∧ 0 < J₀ ∧
      ∀ C : ℝ, 0 < C → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ J : ℕ, J₀ ≤ J →
      ∀ {c K : ℕ} (G : Fin c → Group), 0 < c →
      (∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2) →
      0 < K → ∀ (f : RealL2), ‖f‖ = 1 →
      ∀ (_hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0),
      (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
      16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2 →
      1 / 2 ≤ inner ℝ (averageOperator G f) f →
      ∃ (j : ℕ) (F : 𝓢(ℝ, ℂ)) (m : ℕ), J ≤ j ∧ ‖F.toLp 2 volume‖ = 1 ∧
        r < ‖complexAverage G (F.toLp 2 volume)‖ ∧
        schwartzDyadicRegularityCost j F ≤ dyadicRegularityThreshold ∧
        (∀ ξ : ℝ, |ξ| ≤ (2 : ℝ) ^ j ∨ (2 : ℝ) ^ (j + 2) ≤ |ξ| →
          (𝓕 F : 𝓢(ℝ, ℂ)) ξ = 0) ∧
        2 * N * 2 ^ m ≤ j ∧
        C * Real.log (1 / (1 / 4 : ℝ) ^ j) / Real.log (1 / ε) < (2 : ℝ) ^ m ∧
        r ^ (2 ^ m) / 2 ≤
          ‖∫ g, (mobiusSmoothedDensity (generatorWalkMeasure G (2 ^ m)) ((1 / 4 : ℝ) ^ j) g).toReal •
            complexPullbackL2 g⁻¹ (F.toLp 2 volume) ∂(Measure.haar : Measure Group)‖ := by
  obtain ⟨r, hr, hselect⟩ := exists_uniform_normalized_regular_high_band
  refine ⟨r, hr, ?_⟩
  intro Nmin
  obtain ⟨N, J₀, hN, hNmin, hJ₀, hscales⟩ := exists_compatible_dyadic_smoothing_scales Nmin
    (by positivity : 0 ≤ 29 * Real.sqrt dyadicRegularityThreshold) hr
  refine ⟨N, J₀, hN, hNmin, hJ₀, ?_⟩
  intro C _hC
  obtain ⟨ε₀, hε₀, hε₀one, hεbound⟩ := exists_small_parameter_log_bound
    (4 * (N : ℝ) * C * Real.log 4)
  refine ⟨ε₀, hε₀, hε₀one, ?_⟩
  intro ε hε hεsmall J hJ c K G hc hG hK f hnorm hs hzero hgrid hcorr
  obtain ⟨j, F, hj, hF, hlarge, hR, hfreq⟩ :=
    hselect J G hc hG hK f hnorm hs hzero hgrid hcorr
  obtain ⟨hL, hscale⟩ := hεbound ε hε hεsmall
  obtain ⟨m, hm, hthreshold, herror, hη⟩ :=
    hscales C (Real.log (1 / ε)) hL hscale j (hJ.trans hj)
  refine ⟨j, F, m, hj, hF, hlarge, hR, hfreq, hm, hthreshold, ?_⟩
  apply generatorWalk_haar_integral_dyadic_norm_lower G hc j F hF hr.le hlarge.le hR
    (by positivity : (0 : ℝ) < (1 / 4 : ℝ) ^ j) hη m
  calc
    29 * (2 : ℝ) ^ j * Real.sqrt dyadicRegularityThreshold * (1 / 4 : ℝ) ^ j =
        (29 * Real.sqrt dyadicRegularityThreshold) * (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j := by ring
    _ ≤ r ^ (2 ^ m) / 2 := herror

end TransposeFollowup.RealMobius
