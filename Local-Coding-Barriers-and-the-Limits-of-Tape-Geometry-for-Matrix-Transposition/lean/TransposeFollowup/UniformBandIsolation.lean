import TransposeFollowup.DyadicSmallRatioCorrelation
import TransposeFollowup.GridSmoothHighFrequency

/-! A universal positive norm ratio occurs on a nonzero actual dyadic band.
The constant is independent of the input, grid, and bounded generator family.
This does not assert relative spatial-moment bounds for the selected band. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap Filter
open scoped Topology
set_option autoImplicit false

theorem exists_universal_dyadic_isolation_constants :
    ∃ (D : ℕ) (r : ℝ), 0 < r ∧
      2 * ((D : ℝ) * r * dyadicCutoffDerivativeBound 0 +
        ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant) < 1 / 3 := by
  obtain ⟨D, hD⟩ := pow_unbounded_of_one_lt (24 * universalDyadicFarConstant)
    (by norm_num : (1 : ℝ) < 2)
  let B := dyadicCutoffDerivativeBound 0
  have hB : 0 ≤ B := dyadicCutoffDerivativeBound_nonneg 0
  have hDp : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  let r := (24 * ((D : ℝ) + 1) * (B + 1))⁻¹
  have hden : 0 < 24 * ((D : ℝ) + 1) * (B + 1) := by positivity
  have hr : 0 < r := inv_pos.mpr hden
  have hid : (24 * ((D : ℝ) + 1) * (B + 1)) * r = 1 := mul_inv_cancel₀ (ne_of_gt hden)
  have hnear : (D : ℝ) * r * B ≤ 1 / 24 := by
    have hab : (D : ℝ) * B ≤ ((D : ℝ) + 1) * (B + 1) := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hab hr.le
    nlinarith [hid, hp]
  have hfar : ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant < 1 / 24 := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ D)).mpr
    linarith [hD]
  exact ⟨D, r, hr, by change 2 * ((D : ℝ) * r * B + _) < _; linarith⟩

theorem exists_uniform_dyadic_band_norm_ratio :
    ∃ r : ℝ, 0 < r ∧ ∀ {c : ℕ} (G : Fin c → Group), 0 < c →
      (∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2) →
      ∀ {f : ℝ → ℂ} (hf : MemLp f 2 volume)
        (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0),
      ‖hf.toLp f‖ = 1 →
      (∃ N : ℕ, let v := ∑ j ∈ Finset.range N,
        (smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
        1 / 3 ≤ inner ℝ (complexAverage G v) v) →
      ∃ j : ℕ, let u := (smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
        u ≠ 0 ∧ r * ‖u‖ < ‖complexAverage G u‖ := by
  obtain ⟨D, r, hr, hconst⟩ := exists_universal_dyadic_isolation_constants
  refine ⟨r, hr, ?_⟩
  intro c G hc hG f hf hs hnorm hcorr
  obtain ⟨N, hN⟩ := hcorr
  by_contra hnone
  have hsmall : ∀ j, ‖complexAverage G ((smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)‖ ≤
        r * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖ := by
    intro j
    by_cases hz : (smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume = 0
    · simp only [hz, map_zero, norm_zero, mul_zero, le_refl]
    · exact le_of_not_gt (fun h => hnone ⟨j, hz, h⟩)
  have hbound := dyadicBand_small_ratio_finite_correlation_le G hc hG hf hs D N hr.le hsmall
  simp only [hnorm, one_pow, mul_one] at hbound
  exact (not_le_of_gt hconst) (hN.trans hbound)

theorem exists_uniform_grid_dyadic_band_norm_ratio :
    ∃ r : ℝ, 0 < r ∧ ∀ {c K : ℕ} (G : Fin c → Group), 0 < c →
      (∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2) →
      0 < K → ∀ (f : RealL2), ‖f‖ = 1 →
      ∀ (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0),
      (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
      16384 * Real.pi ^ 2 ≤ (K : ℝ) ^ 2 →
      1 / 2 ≤ inner ℝ (averageOperator G f) f →
      ∃ j : ℕ, let u := (smoothBand (Lp.memLp (ofRealL2 f))
        (ofRealL2_unit_supported f hs) (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
        u ≠ 0 ∧ r * ‖u‖ < ‖complexAverage G u‖ := by
  obtain ⟨r, hr, hratio⟩ := exists_uniform_dyadic_band_norm_ratio
  refine ⟨r, hr, ?_⟩
  intro c K G hc hG hK f hnorm hs hzero hscale hcorr
  apply hratio G hc hG (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
  · simpa only [Lp.toLp_coeFn, ofRealL2_norm] using hnorm
  · exact (gridSmoothHighFrequency_finite_correlation_eventually G hc hK f hnorm hs hzero hscale hcorr).exists

end TransposeFollowup.RealMobius
