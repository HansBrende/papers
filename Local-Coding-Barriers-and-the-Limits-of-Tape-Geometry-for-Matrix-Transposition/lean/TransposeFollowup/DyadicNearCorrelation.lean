import TransposeFollowup.ConcreteDyadicTransport

/-! Small norm ratios force small summed correlations at each near offset.
Both shifted energy sums use the same unweighted band estimate. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

theorem dyadicBand_offset_norm_product_sum_le (s : Finset ℕ) (d : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    let u := fun k => (smoothBand hf hs (dyadicAnnularCutoff k)
      (dyadicAnnularCutoff_hasCompactSupport k)).toLp 2 volume
    (∑ j ∈ s, ‖u j‖ * ‖u (j + d)‖) ≤ dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2 := by
  classical
  let u := fun k => (smoothBand hf hs (dyadicAnnularCutoff k)
    (dyadicAnnularCutoff_hasCompactSupport k)).toLp 2 volume
  have ha := dyadic_smoothBand_energy_le s hf hs
  have hb := dyadic_smoothBand_energy_le (s.image (fun j => j + d)) hf hs
  rw [Finset.sum_image] at hb
  · have hab : (∑ j ∈ s, 2 * (‖u j‖ * ‖u (j + d)‖)) ≤
        ∑ j ∈ s, (‖u j‖ ^ 2 + ‖u (j + d)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (‖u j‖ - ‖u (j + d)‖)]
    rw [← Finset.mul_sum, Finset.sum_add_distrib] at hab
    change (∑ j ∈ s, ‖u j‖ * ‖u (j + d)‖) ≤ _
    change (∑ j ∈ s, ‖u j‖ ^ 2) ≤ _ at ha
    change (∑ j ∈ s, ‖u (j + d)‖ ^ 2) ≤ _ at hb
    linarith
  · intro j _ k _ he
    exact Nat.add_right_cancel he

theorem dyadicBand_small_ratio_offset_sum_le (s : Finset ℕ) (d : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (T : ComplexL2 →L[ℝ] ComplexL2) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ∀ j, ‖T ((smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)‖ ≤
        r * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖) :
    let u := fun k => (smoothBand hf hs (dyadicAnnularCutoff k)
      (dyadicAnnularCutoff_hasCompactSupport k)).toLp 2 volume
    (∑ j ∈ s, |inner ℝ (T (u j)) (u (j + d))|) ≤
      r * (dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2) := by
  let u := fun k => (smoothBand hf hs (dyadicAnnularCutoff k)
    (dyadicAnnularCutoff_hasCompactSupport k)).toLp 2 volume
  change (∑ j ∈ s, |inner ℝ (T (u j)) (u (j + d))|) ≤ _
  calc
    _ ≤ ∑ j ∈ s, r * (‖u j‖ * ‖u (j + d)‖) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖T (u j)‖ * ‖u (j + d)‖ := abs_real_inner_le_norm _ _
        _ ≤ (r * ‖u j‖) * ‖u (j + d)‖ :=
          mul_le_mul_of_nonneg_right (hsmall j) (norm_nonneg _)
        _ = _ := mul_assoc _ _ _
    _ = r * (∑ j ∈ s, ‖u j‖ * ‖u (j + d)‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadicBand_offset_norm_product_sum_le s d hf hs) hr

end TransposeFollowup
