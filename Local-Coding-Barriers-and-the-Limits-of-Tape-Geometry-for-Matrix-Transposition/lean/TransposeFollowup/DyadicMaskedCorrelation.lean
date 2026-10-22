import TransposeFollowup.DyadicAverageFarCorrelation
import TransposeFollowup.DyadicNearCorrelation
import TransposeFollowup.FiniteSymmetricCorrelation

/-! The uniform correlation estimate survives removal of any collection
of bands. The norm-ratio hypothesis is needed only on retained bands. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

noncomputable def dyadicMaskedBand (p : ℕ → Prop) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (j : ℕ) : ComplexL2 := by
  classical
  exact if p j then (smoothBand hf hs (dyadicAnnularCutoff j)
    (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume else 0

theorem dyadicMaskedBand_of_true (p : ℕ → Prop) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (j : ℕ) (hj : p j) :
    dyadicMaskedBand p hf hs j = (smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume := by
  simp only [dyadicMaskedBand, ite_eq_left hj]

theorem dyadicMaskedBand_of_false (p : ℕ → Prop) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (j : ℕ) (hj : ¬p j) :
    dyadicMaskedBand p hf hs j = 0 := by
  simp only [dyadicMaskedBand, ite_eq_right hj]

theorem dyadicMaskedBand_inner_abs_le (p : ℕ → Prop) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (T : ComplexL2 →L[ℝ] ComplexL2) (j k : ℕ) :
    |inner ℝ (T (dyadicMaskedBand p hf hs j)) (dyadicMaskedBand p hf hs k)| ≤
      |inner ℝ (T ((smoothBand hf hs (dyadicAnnularCutoff j)
        (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume))
        ((smoothBand hf hs (dyadicAnnularCutoff k)
          (dyadicAnnularCutoff_hasCompactSupport k)).toLp 2 volume)| := by
  classical
  by_cases hj : p j <;> by_cases hk : p k <;>
    simp [dyadicMaskedBand, hj, hk, abs_nonneg]

theorem dyadicMaskedBand_small_ratio_offset_sum_le (p : ℕ → Prop)
    (s : Finset ℕ) (d : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (T : ComplexL2 →L[ℝ] ComplexL2) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ∀ j, p j → ‖T ((smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)‖ ≤
        r * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖) :
    (∑ j ∈ s, |inner ℝ (T (dyadicMaskedBand p hf hs j)) (dyadicMaskedBand p hf hs (j + d))|) ≤
      r * (dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2) := by
  classical
  let u := fun k => (smoothBand hf hs (dyadicAnnularCutoff k)
    (dyadicAnnularCutoff_hasCompactSupport k)).toLp 2 volume
  calc
    _ ≤ ∑ j ∈ s, r * (‖u j‖ * ‖u (j + d)‖) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : p j
      · by_cases hk : p (j + d)
        · rw [dyadicMaskedBand_of_true p hf hs j hj, dyadicMaskedBand_of_true p hf hs (j + d) hk]
          calc
            _ ≤ ‖T (u j)‖ * ‖u (j + d)‖ := abs_real_inner_le_norm _ _
            _ ≤ (r * ‖u j‖) * ‖u (j + d)‖ :=
              mul_le_mul_of_nonneg_right (hsmall j hj) (norm_nonneg _)
            _ = _ := mul_assoc _ _ _
        · rw [dyadicMaskedBand_of_false p hf hs (j + d) hk, inner_zero_right, abs_zero]
          positivity
      · rw [dyadicMaskedBand_of_false p hf hs j hj, map_zero, inner_zero_left, abs_zero]
        positivity
    _ = r * (∑ j ∈ s, ‖u j‖ * ‖u (j + d)‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadicBand_offset_norm_product_sum_le s d hf hs) hr

namespace RealMobius

theorem dyadicMaskedBand_small_ratio_finite_correlation_le {c : ℕ}
    (G : Fin c → Group) (hc : 0 < c)
    (hG : ∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2)
    (p : ℕ → Prop) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (D N : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ∀ j, p j → ‖complexAverage G ((smoothBand hf hs (dyadicAnnularCutoff j)
      (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume)‖ ≤
        r * ‖(smoothBand hf hs (dyadicAnnularCutoff j)
          (dyadicAnnularCutoff_hasCompactSupport j)).toLp 2 volume‖) :
    let v := ∑ j ∈ Finset.range N, dyadicMaskedBand p hf hs j
    inner ℝ (complexAverage G v) v ≤
      2 * ((D : ℝ) * r * dyadicCutoffDerivativeBound 0 +
        ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant) * ‖hf.toLp f‖ ^ 2 := by
  have hfar : (∑ d ∈ Finset.range N, ∑ j ∈ Finset.range N,
      |inner ℝ (complexAverage G (dyadicMaskedBand p hf hs j))
        (dyadicMaskedBand p hf hs (j + (D + d)))|) ≤
      ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant * ‖hf.toLp f‖ ^ 2 := by
    refine le_trans ?_ (dyadicBand_average_upper_far_sum_le G hc hG D N (fun _ => Finset.range N) hf hs)
    exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun j _ =>
      dyadicMaskedBand_inner_abs_le p hf hs (complexAverage G) j (j + (D + d))))
  have h := symmetric_finite_correlation_le_of_offset_bounds (complexAverage G)
    (dyadicMaskedBand p hf hs) (complexAverage_symmetric G) D N
    (r * (dyadicCutoffDerivativeBound 0 * ‖hf.toLp f‖ ^ 2))
    (((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant * ‖hf.toLp f‖ ^ 2)
    (fun d => dyadicMaskedBand_small_ratio_offset_sum_le p (Finset.range N) d hf hs
      (complexAverage G) hr hsmall) hfar
  convert h using 1
  ring

end RealMobius
end TransposeFollowup
