import TransposeFollowup.SmoothHighFrequencyBounds
import TransposeFollowup.GridHighFrequency

/-! The exact grid input yields the smoothly truncated high-frequency
component reconstructed by the concrete dyadic bands, with quantitative
correlation retained. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology
set_option autoImplicit false

theorem ofRealL2_unit_supported (f : RealL2)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → ofRealL2 f x = 0 := by
  filter_upwards [ofRealL2_coe f, hs] with x hx hsx hu
  rw [hx, hsx hu, Complex.ofReal_zero]

noncomputable def gridSmoothHighFrequency (f : RealL2)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) : ComplexL2 :=
  smoothHighFrequency (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)

theorem gridSmoothHighFrequency_distance {K : ℕ} (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 ≤ (K : ℝ) ^ 2) :
    ‖ofRealL2 f - gridSmoothHighFrequency f hs‖ ≤ 1 / 16 := by
  have h := smoothHighFrequency_distance_le_lowFrequency (Lp.memLp (ofRealL2 f))
    (ofRealL2_unit_supported f hs)
  simp only [Lp.toLp_coeFn] at h
  apply h.trans
  exact grid_lowFrequency_norm_le hK f hnorm hs hzero 2 (by norm_num) (by nlinarith [hscale])

theorem gridSmoothHighFrequency_correlation {c K : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    95 / 256 ≤ inner ℝ (complexAverage G (gridSmoothHighFrequency f hs)) (gridSmoothHighFrequency f hs) := by
  apply correlation_survives_small_change (complexAverage G) (complexAverage_norm_le G hc)
    (f := ofRealL2 f)
  · rw [ofRealL2_norm, hnorm]
  · exact gridSmoothHighFrequency_distance hK f hnorm hs hzero hscale
  · rwa [complexAverage_real_correlation]

theorem gridSmoothHighFrequency_reconstruction (f : RealL2)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
      (smoothBand (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
        (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)
      atTop (𝓝 (gridSmoothHighFrequency f hs)) :=
  dyadicBand_sum_tendsto (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)

theorem gridSmoothHighFrequency_witness {c K : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    let h := gridSmoothHighFrequency f hs
    ‖h‖ ≤ 1 ∧ (∀ᵐ ξ ∂volume, ξ ∈ Icc (-1 : ℝ) 1 → (𝓕 h : ComplexL2) ξ = 0) ∧
      ‖ofRealL2 f - h‖ ≤ 1 / 16 ∧ 95 / 256 ≤ inner ℝ (complexAverage G h) h := by
  refine ⟨?_, smoothHighFrequency_fourier_zero_on _ _,
    gridSmoothHighFrequency_distance hK f hnorm hs hzero hscale,
    gridSmoothHighFrequency_correlation G hc hK f hnorm hs hzero hscale hcorr⟩
  simpa only [gridSmoothHighFrequency, Lp.toLp_coeFn, ofRealL2_norm, hnorm] using
    smoothHighFrequency_norm_le (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)

theorem gridSmoothHighFrequency_finite_correlation_eventually {c K : ℕ}
    (G : Fin c → Group) (hc : 0 < c) (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    ∀ᶠ N : ℕ in atTop,
      let v := ∑ j ∈ Finset.range N,
        (smoothBand (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
          (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
      1 / 3 ≤ inner ℝ (complexAverage G v) v := by
  have hv := gridSmoothHighFrequency_reconstruction f hs
  have hT := ((complexAverage G).continuous.tendsto (gridSmoothHighFrequency f hs)).comp hv
  have hlim := hT.inner (𝕜 := ℝ) hv
  have hpos := gridSmoothHighFrequency_correlation G hc hK f hnorm hs hzero hscale hcorr
  exact hlim.eventually_const_le (by linarith)

end TransposeFollowup.RealMobius
