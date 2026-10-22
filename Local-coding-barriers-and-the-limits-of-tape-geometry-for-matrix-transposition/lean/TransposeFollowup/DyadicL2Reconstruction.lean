import TransposeFollowup.DyadicLowL2Convergence

/-! Finite telescoping and actual L2 reconstruction of the smooth
high-frequency component from the concrete Schwartz bands. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology
set_option autoImplicit false

noncomputable def smoothHighFrequency {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) : ComplexL2 :=
  hf.toLp f - (smoothBand hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport).toLp 2 volume

theorem dyadicBand_schwartz_sum {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (N : ℕ) :
    (∑ j ∈ Finset.range N, smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)) =
      smoothBand hf hs (dyadicLowCutoff N) (dyadicLowCutoff_hasCompactSupport N) -
        smoothBand hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, dyadicLowCutoff,
      schwartzDyadicDilate_zero, sub_self]
  | succ N ih =>
    have hb := smoothBand_congr hf hs (dyadicAnnularCutoff N)
      (dyadicLowCutoff (N + 1) - dyadicLowCutoff N) (dyadicAnnularCutoff_hasCompactSupport N)
      ((dyadicLowCutoff_hasCompactSupport (N + 1)).sub (dyadicLowCutoff_hasCompactSupport N))
      (dyadicAnnularCutoff_difference N)
    rw [Finset.sum_range_succ, ih, hb, smoothBand_sub hf hs
      (dyadicLowCutoff (N + 1)) (dyadicLowCutoff N)
      (dyadicLowCutoff_hasCompactSupport (N + 1)) (dyadicLowCutoff_hasCompactSupport N)]
    abel

theorem dyadicBand_toLp_sum {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (N : ℕ) :
    (∑ j ∈ Finset.range N, (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume) =
      (smoothBand hf hs (dyadicLowCutoff N) (dyadicLowCutoff_hasCompactSupport N)).toLp 2 volume -
        (smoothBand hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport).toLp 2 volume := by
  have h := congrArg (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (dyadicBand_schwartz_sum hf hs N)
  simpa only [map_sum, map_sub, SchwartzMap.toLpCLM_apply] using h

theorem dyadicBand_sum_tendsto {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume) atTop (𝓝 (smoothHighFrequency hf hs)) := by
  simp only [dyadicBand_toLp_sum, smoothHighFrequency]
  exact (dyadicLowBand_tendsto hf hs).sub tendsto_const_nhds

theorem smoothHighFrequency_fourier_coe {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ⇑(𝓕 (smoothHighFrequency hf hs) : ComplexL2) =ᵐ[volume]
      (fun ξ => (1 - lowFrequencyCutoff ξ) * (𝓕 (hf.toLp f) : ComplexL2) ξ) := by
  let v := (smoothBand hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport).toLp 2 volume
  have he : (𝓕 (smoothHighFrequency hf hs) : ComplexL2) = -(𝓕 (v - hf.toLp f)) := by
    change 𝓕 (hf.toLp f - v) = _
    rw [show hf.toLp f - v = -(v - hf.toLp f) by abel, FourierTransform.fourier_neg]
  rw [he]
  filter_upwards [Lp.coeFn_neg (𝓕 (v - hf.toLp f) : ComplexL2),
    smoothBand_sub_input_fourier_coe hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport]
    with ξ hneg hband
  rw [hneg]
  change -(𝓕 (v - hf.toLp f) : ComplexL2) ξ = _
  rw [hband]
  ring

theorem norm_sub_smoothHighFrequency {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ‖hf.toLp f - smoothHighFrequency hf hs‖ =
      ‖(smoothBand hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport).toLp 2 volume‖ := by
  simp only [smoothHighFrequency, sub_sub_cancel]

end TransposeFollowup
