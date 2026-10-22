import TransposeFollowup.UniformBandIsolation
import TransposeFollowup.GridDyadicTail

/-! The universal band ratio holds within any retained family with positive
finite-sum correlation. In particular, it holds above any prescribed level. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap Filter
set_option autoImplicit false

theorem exists_uniform_retained_dyadic_band_norm_ratio :
    ∃ r : ℝ, 0 < r ∧ ∀ {c : ℕ} (G : Fin c → Group), 0 < c →
      (∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2) →
      ∀ (p : ℕ → Prop) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
        (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0),
      ‖hf.toLp f‖ = 1 →
      (∃ N : ℕ, let v := ∑ j ∈ Finset.range N, dyadicMaskedBand p hf hs j
        1 / 3 ≤ inner ℝ (complexAverage G v) v) →
      ∃ j : ℕ, p j ∧ let u := (smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
        u ≠ 0 ∧ r * ‖u‖ < ‖complexAverage G u‖ := by
  obtain ⟨D, r, hr, hconst⟩ := exists_universal_dyadic_isolation_constants
  refine ⟨r, hr, ?_⟩
  intro c G hc hG p f hf hs hnorm hcorr
  obtain ⟨N, hN⟩ := hcorr
  by_contra hnone
  have hsmall : ∀ j, p j → ‖complexAverage G ((smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)‖ ≤
        r * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖ := by
    intro j hj
    by_cases hz : (smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume = 0
    · simp only [hz, map_zero, norm_zero, mul_zero, le_refl]
    · exact le_of_not_gt (fun h => hnone ⟨j, hj, hz, h⟩)
  have hbound := dyadicMaskedBand_small_ratio_finite_correlation_le G hc hG p hf hs D N hr.le hsmall
  simp only [hnorm, one_pow, mul_one] at hbound
  exact (not_le_of_gt hconst) (hN.trans hbound)

theorem exists_uniform_grid_high_dyadic_band_norm_ratio :
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
        u ≠ 0 ∧ r * ‖u‖ < ‖complexAverage G u‖ := by
  obtain ⟨r, hr, hratio⟩ := exists_uniform_retained_dyadic_band_norm_ratio
  refine ⟨r, hr, ?_⟩
  intro J c K G hc hG hK f hnorm hs hzero hscale hcorr
  apply hratio G hc hG (fun j => J ≤ j) (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
  · simpa only [Lp.toLp_coeFn, ofRealL2_norm] using hnorm
  · obtain ⟨N, hN⟩ :=
      (gridSmoothHighFrequencyFrom_finite_correlation_eventually J G hc hK f hnorm hs hzero hscale hcorr).exists
    refine ⟨J + N, ?_⟩
    simpa only [dyadicMaskedBand_tail_sum] using hN

end TransposeFollowup.RealMobius
