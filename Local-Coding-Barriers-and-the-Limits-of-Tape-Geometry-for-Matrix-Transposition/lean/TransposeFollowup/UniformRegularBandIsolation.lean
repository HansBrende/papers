import TransposeFollowup.UniformRetainedBandIsolation
import TransposeFollowup.DyadicRegularityDiscard
import TransposeFollowup.RetainedCorrelationLimit

/-! Joint selection of a high band with positive average norm ratio
and controlled relative regularity cost. All selection constants are fixed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap Filter
open scoped Topology
set_option autoImplicit false

theorem exists_uniform_grid_regular_high_band :
    ∃ r : ℝ, 0 < r ∧ ∀ (J : ℕ) {c K : ℕ} (G : Fin c → Group), 0 < c →
      (∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2) →
      0 < K → ∀ (f : RealL2), ‖f‖ = 1 →
      ∀ (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0),
      (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
      16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2 →
      1 / 2 ≤ inner ℝ (averageOperator G f) f →
      ∃ j : ℕ, J ≤ j ∧ let u := (smoothBand (Lp.memLp (ofRealL2 f))
        (ofRealL2_unit_supported f hs) (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
        u ≠ 0 ∧ r * ‖u‖ < ‖complexAverage G u‖ ∧
          dyadicBandRegularityCost (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs) j ≤
            dyadicRegularityThreshold * ‖u‖ ^ 2 := by
  obtain ⟨r, hr, hratio⟩ := exists_uniform_retained_dyadic_band_norm_ratio
  refine ⟨r, hr, ?_⟩
  intro J c K G hc hG hK f hnorm hs hzero hscale hcorr
  let hf := Lp.memLp (ofRealL2 f)
  let hsC := ofRealL2_unit_supported f hs
  let u := fun j => (smoothBand hf hsC (dyadicAnnularCutoff j)
    (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
  let p := fun j => J ≤ j ∧ dyadicBandRegularityCost hf hsC j ≤ dyadicRegularityThreshold * ‖u j‖ ^ 2
  let v := fun N => ∑ j ∈ Finset.range N, u (J + j)
  let w := fun N => ∑ j ∈ Finset.range (J + N), dyadicMaskedBand p hf hsC j
  have hnormC : ‖hf.toLp (ofRealL2 f)‖ = 1 := by
    simpa only [Lp.toLp_coeFn, ofRealL2_norm] using hnorm
  have hnormR : ‖ofRealL2 f‖ = 1 := by rw [ofRealL2_norm, hnorm]
  have hcorrC : 1 / 2 ≤ inner ℝ (complexAverage G (ofRealL2 f)) (ofRealL2 f) := by
    rwa [complexAverage_real_correlation]
  have hdiscard (N : ℕ) : ‖v N - w N‖ ≤ 1 / 1024 := by
    dsimp only [v, w, p, u]
    rw [← dyadicMaskedBand_tail_sum J N hf hsC]
    exact dyadicMaskedBand_regular_discard_norm_le (Finset.range (J + N))
      (fun j => J ≤ j) hf hsC hnormC
  obtain ⟨N, hN⟩ := exists_retained_finite_correlation (complexAverage G)
    (complexAverage_norm_le G hc) hnormR hcorrC
    (gridSmoothHighFrequencyFrom_distance J hK f hnorm hs hzero hscale) v w
    (gridSmoothHighFrequencyFrom_reconstruction J f hs) hdiscard
  obtain ⟨j, hj, hne, hlarge⟩ := hratio G hc hG p hf hsC hnormC ⟨J + N, hN⟩
  exact ⟨j, hj.1, hne, hlarge, hj.2⟩

end TransposeFollowup.RealMobius
