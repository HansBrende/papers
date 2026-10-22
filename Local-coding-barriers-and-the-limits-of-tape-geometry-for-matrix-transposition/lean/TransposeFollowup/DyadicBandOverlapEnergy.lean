import TransposeFollowup.ConcreteDyadicTransport

/-! Removing a family of dyadic bands costs at most three times its
summed energy. The bound uses the actual Fourier supports, not spatial support. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem dyadic_annular_norm_sum_sq_le (s : Finset ℕ) (ξ : ℝ) (a : ℕ → ℂ)
    (hs : ∀ j ∈ s, a j ≠ 0 → (2 : ℝ) ^ j ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (j + 2)) :
    ‖∑ j ∈ s, a j‖ ^ 2 ≤ 3 * ∑ j ∈ s, ‖a j‖ ^ 2 := by
  classical
  let t := s.filter (fun j => (2 : ℝ) ^ j ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (j + 2))
  have he : (∑ j ∈ s, a j) = ∑ j ∈ t, a j := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro j hj hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hj, hs j hj hne⟩)
  have hcard : t.card ≤ 3 := dyadic_annulus_card_le_three s ξ
  have hc : (t.card : ℝ) ≤ 3 := by exact_mod_cast hcard
  have hcs : (∑ j ∈ t, ‖a j‖) ^ 2 ≤ (t.card : ℝ) * ∑ j ∈ t, ‖a j‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) (fun j => ‖a j‖)
  calc
    _ = ‖∑ j ∈ t, a j‖ ^ 2 := by rw [he]
    _ ≤ (∑ j ∈ t, ‖a j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (t.card : ℝ) * ∑ j ∈ t, ‖a j‖ ^ 2 := hcs
    _ ≤ 3 * ∑ j ∈ t, ‖a j‖ ^ 2 := mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)) (by norm_num)

theorem dyadicBand_sum_norm_sq_le_three_energy (s : Finset ℕ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    let u := fun j => (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume
    ‖∑ j ∈ s, u j‖ ^ 2 ≤ 3 * ∑ j ∈ s, ‖u j‖ ^ 2 := by
  classical
  let u := fun j => smoothBand hf hs (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j)
  let v := fun j => smoothBandSpectrum hf hs (dyadicAnnularCutoff j) (dyadicAnnularCutoff_hasCompactSupport j)
  have hnorm : ‖∑ j ∈ s, (u j).toLp 2 volume‖ ^ 2 = ∫ ξ, ‖∑ j ∈ s, v j ξ‖ ^ 2 := by
    have he : (∑ j ∈ s, (u j).toLp 2 volume) = (∑ j ∈ s, u j).toLp 2 volume := by
      exact (map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 volume) u s).symm
    rw [he, ← Lp.norm_fourier_eq ((∑ j ∈ s, u j).toLp 2 volume), SchwartzMap.toLp_fourier_eq,
      FourierTransform.fourier_sum]
    simp only [u, smoothBand_fourier]
    rw [schwartz_toLp_norm_sq]
    simp only [sum_apply, v]
  have heach (j : ℕ) : ‖(u j).toLp 2 volume‖ ^ 2 = ∫ ξ, ‖v j ξ‖ ^ 2 := by
    rw [← Lp.norm_fourier_eq ((u j).toLp 2 volume), smoothBand_toLp_fourier, schwartz_toLp_norm_sq]
  have hi : Integrable (fun ξ => ‖∑ j ∈ s, v j ξ‖ ^ 2) := by
    simpa only [sum_apply] using schwartz_integrable_norm_sq (∑ j ∈ s, v j)
  have hi' : Integrable (fun ξ => 3 * ∑ j ∈ s, ‖v j ξ‖ ^ 2) :=
    (integrable_finsetSum s (fun j _ => schwartz_integrable_norm_sq (v j))).const_mul 3
  change ‖∑ j ∈ s, (u j).toLp 2 volume‖ ^ 2 ≤ 3 * ∑ j ∈ s, ‖(u j).toLp 2 volume‖ ^ 2
  rw [hnorm]
  calc
    _ ≤ ∫ ξ, 3 * ∑ j ∈ s, ‖v j ξ‖ ^ 2 := by
      apply integral_mono hi hi'
      intro ξ
      apply dyadic_annular_norm_sum_sq_le s ξ (fun j => v j ξ)
      intro j _ hne
      apply schwartz_annular_derivative_support baseAnnularCutoff baseAnnularCutoff_tsupport_subset j 0
      intro hz
      apply hne
      change dyadicAnnularCutoff j ξ * (𝓕 f) ξ = 0
      exact mul_eq_zero_of_left hz _
    _ = 3 * ∑ j ∈ s, ‖(u j).toLp 2 volume‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum s (fun j _ => schwartz_integrable_norm_sq (v j))]
      simp only [heach]

end TransposeFollowup
