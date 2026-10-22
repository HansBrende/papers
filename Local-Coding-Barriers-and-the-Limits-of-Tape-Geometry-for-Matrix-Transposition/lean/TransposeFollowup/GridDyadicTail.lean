import TransposeFollowup.DyadicTailReconstruction
import TransposeFollowup.GridSmoothHighFrequency

/-! The grid input retains correlation after removal of all bands below
an arbitrary level J, with an explicit grid-size requirement. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology
set_option autoImplicit false

noncomputable def gridSmoothHighFrequencyFrom (J : ℕ) (f : RealL2)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) : ComplexL2 :=
  smoothHighFrequencyFrom J (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)

theorem gridSmoothHighFrequencyFrom_distance (J : ℕ) {K : ℕ} (hK : 0 < K)
    (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2) :
    ‖ofRealL2 f - gridSmoothHighFrequencyFrom J f hs‖ ≤ 1 / 16 := by
  have h := smoothHighFrequencyFrom_distance_le_lowFrequency J (Lp.memLp (ofRealL2 f))
    (ofRealL2_unit_supported f hs)
  simp only [Lp.toLp_coeFn] at h
  apply h.trans
  apply grid_lowFrequency_norm_le hK f hnorm hs hzero ((2 : ℝ) ^ (J + 1)) (by positivity)
  convert hscale using 1
  rw [pow_succ (2 : ℝ) J, mul_pow, ← pow_mul, Nat.mul_comm J 3]
  ring

theorem gridSmoothHighFrequencyFrom_correlation (J : ℕ) {c K : ℕ}
    (G : Fin c → Group) (hc : 0 < c) (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    95 / 256 ≤ inner ℝ (complexAverage G (gridSmoothHighFrequencyFrom J f hs))
      (gridSmoothHighFrequencyFrom J f hs) := by
  apply correlation_survives_small_change (complexAverage G) (complexAverage_norm_le G hc)
    (f := ofRealL2 f)
  · rw [ofRealL2_norm, hnorm]
  · exact gridSmoothHighFrequencyFrom_distance J hK f hnorm hs hzero hscale
  · rwa [complexAverage_real_correlation]

theorem gridSmoothHighFrequencyFrom_reconstruction (J : ℕ) (f : RealL2)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
      (smoothBand (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
        (dyadicAnnularCutoff (J + j)) (dyadicAnnularCutoff_hasCompactSupport (J + j))).toLp 2 volume)
      atTop (𝓝 (gridSmoothHighFrequencyFrom J f hs)) :=
  dyadicBand_tail_sum_tendsto J (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)

theorem gridSmoothHighFrequencyFrom_finite_correlation_eventually (J : ℕ) {c K : ℕ}
    (G : Fin c → Group) (hc : 0 < c) (hK : 0 < K) (f : RealL2) (hnorm : ‖f‖ = 1)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (hscale : 16384 * Real.pi ^ 2 * (2 : ℝ) ^ (3 * J) ≤ (K : ℝ) ^ 2)
    (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    ∀ᶠ N : ℕ in atTop,
      let v := ∑ j ∈ Finset.range N,
        (smoothBand (Lp.memLp (ofRealL2 f)) (ofRealL2_unit_supported f hs)
          (dyadicAnnularCutoff (J + j)) (dyadicAnnularCutoff_hasCompactSupport (J + j))).toLp 2 volume
      1 / 3 ≤ inner ℝ (complexAverage G v) v := by
  have hv := gridSmoothHighFrequencyFrom_reconstruction J f hs
  have hT := ((complexAverage G).continuous.tendsto (gridSmoothHighFrequencyFrom J f hs)).comp hv
  have hlim := hT.inner (𝕜 := ℝ) hv
  have hpos := gridSmoothHighFrequencyFrom_correlation J G hc hK f hnorm hs hzero hscale hcorr
  exact hlim.eventually_const_le (by linarith)

end TransposeFollowup.RealMobius
