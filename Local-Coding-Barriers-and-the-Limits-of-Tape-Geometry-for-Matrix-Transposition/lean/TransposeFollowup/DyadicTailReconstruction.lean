import TransposeFollowup.SmoothHighFrequencyBounds
import TransposeFollowup.DyadicMaskedCorrelation

/-! Exact reconstruction and Fourier support for the dyadic tail beginning
at any prescribed level. The input retains its original support assumption. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology
set_option autoImplicit false

noncomputable def smoothHighFrequencyFrom (J : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) : ComplexL2 :=
  hf.toLp f - (smoothBand hf hs (dyadicLowCutoff J) (dyadicLowCutoff_hasCompactSupport J)).toLp 2 volume

theorem smoothHighFrequencyFrom_zero {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    smoothHighFrequencyFrom 0 hf hs = smoothHighFrequency hf hs := by
  simp only [smoothHighFrequencyFrom, smoothHighFrequency, dyadicLowCutoff, schwartzDyadicDilate_zero]

theorem dyadicBand_toLp_tail_sum (J N : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∑ j ∈ Finset.range N, (smoothBand hf hs (dyadicAnnularCutoff (J + j))
      (dyadicAnnularCutoff_hasCompactSupport (J + j))).toLp 2 volume) =
      (smoothBand hf hs (dyadicLowCutoff (J + N)) (dyadicLowCutoff_hasCompactSupport (J + N))).toLp 2 volume -
        (smoothBand hf hs (dyadicLowCutoff J) (dyadicLowCutoff_hasCompactSupport J)).toLp 2 volume := by
  let u := fun j => (smoothBand hf hs (dyadicAnnularCutoff j)
    (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
  calc
    _ = (∑ j ∈ Finset.range (J + N), u j) - ∑ j ∈ Finset.range J, u j := by
      rw [Finset.sum_range_add]
      abel
    _ = _ := by
      dsimp only [u]
      rw [dyadicBand_toLp_sum, dyadicBand_toLp_sum]
      abel

theorem dyadicBand_tail_sum_tendsto (J : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, (smoothBand hf hs (dyadicAnnularCutoff (J + j))
      (dyadicAnnularCutoff_hasCompactSupport (J + j))).toLp 2 volume)
      atTop (𝓝 (smoothHighFrequencyFrom J hf hs)) := by
  simp only [dyadicBand_toLp_tail_sum, smoothHighFrequencyFrom]
  have hshift : Tendsto (fun N : ℕ => J + N) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat J
  exact ((dyadicLowBand_tendsto hf hs).comp hshift).sub tendsto_const_nhds

theorem dyadicMaskedBand_tail_sum (J N : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∑ j ∈ Finset.range (J + N), dyadicMaskedBand (fun k => J ≤ k) hf hs j) =
      ∑ j ∈ Finset.range N, (smoothBand hf hs (dyadicAnnularCutoff (J + j))
        (dyadicAnnularCutoff_hasCompactSupport (J + j))).toLp 2 volume := by
  rw [Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range J, dyadicMaskedBand (fun k => J ≤ k) hf hs j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact dyadicMaskedBand_of_false _ hf hs j (by simpa only [not_le] using Finset.mem_range.mp hj)
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  exact dyadicMaskedBand_of_true _ hf hs (J + j) (by omega)

theorem smoothHighFrequencyFrom_fourier_coe (J : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ⇑(𝓕 (smoothHighFrequencyFrom J hf hs) : ComplexL2) =ᵐ[volume]
      (fun ξ => (1 - dyadicLowCutoff J ξ) * (𝓕 (hf.toLp f) : ComplexL2) ξ) := by
  let v := (smoothBand hf hs (dyadicLowCutoff J) (dyadicLowCutoff_hasCompactSupport J)).toLp 2 volume
  have he : (𝓕 (smoothHighFrequencyFrom J hf hs) : ComplexL2) = -(𝓕 (v - hf.toLp f)) := by
    change 𝓕 (hf.toLp f - v) = _
    rw [show hf.toLp f - v = -(v - hf.toLp f) by abel, FourierTransform.fourier_neg]
  rw [he]
  filter_upwards [Lp.coeFn_neg (𝓕 (v - hf.toLp f) : ComplexL2),
    smoothBand_sub_input_fourier_coe hf hs (dyadicLowCutoff J) (dyadicLowCutoff_hasCompactSupport J)]
    with ξ hneg hband
  rw [hneg]
  change -(𝓕 (v - hf.toLp f) : ComplexL2) ξ = _
  rw [hband]
  ring

theorem smoothHighFrequencyFrom_norm_le (J : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ‖smoothHighFrequencyFrom J hf hs‖ ≤ ‖hf.toLp f‖ := by
  rw [← Lp.norm_fourier_eq (smoothHighFrequencyFrom J hf hs), ← Lp.norm_fourier_eq (hf.toLp f)]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [smoothHighFrequencyFrom_fourier_coe J hf hs] with ξ hξ
  rw [hξ, norm_mul]
  have hb : ‖(1 : ℂ) - dyadicLowCutoff J ξ‖ ≤ 1 := lowFrequencyCutoff_complement_norm_le _
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

theorem smoothHighFrequencyFrom_fourier_zero_on (J : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ∀ᵐ ξ ∂volume, ξ ∈ Icc (-((2 : ℝ) ^ J)) ((2 : ℝ) ^ J) →
      (𝓕 (smoothHighFrequencyFrom J hf hs) : ComplexL2) ξ = 0 := by
  filter_upwards [smoothHighFrequencyFrom_fourier_coe J hf hs] with ξ hξ hmem
  rw [hξ, dyadicLowCutoff_eq_one J (abs_le.mpr hmem), sub_self, zero_mul]

theorem smoothHighFrequencyFrom_distance_le_lowFrequency (J : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ‖hf.toLp f - smoothHighFrequencyFrom J hf hs‖ ≤
      ‖lowFrequency (Icc (-((2 : ℝ) ^ (J + 1))) ((2 : ℝ) ^ (J + 1))) measurableSet_Icc (hf.toLp f)‖ := by
  simp only [smoothHighFrequencyFrom, sub_sub_cancel]
  apply smoothBand_norm_le_lowFrequency hf hs (dyadicLowCutoff J) (dyadicLowCutoff_hasCompactSupport J)
    _ measurableSet_Icc (dyadicLowCutoff_norm_le J)
  intro ξ hξ
  apply dyadicLowCutoff_eq_zero
  have h : ¬ |ξ| ≤ (2 : ℝ) ^ (J + 1) := fun h => hξ (abs_le.mp h)
  exact (lt_of_not_ge h).le

end TransposeFollowup
