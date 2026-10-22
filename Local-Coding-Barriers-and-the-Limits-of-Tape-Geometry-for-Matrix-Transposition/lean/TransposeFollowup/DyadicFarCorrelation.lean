import TransposeFollowup.DyadicOffsetCorrelation

/-! Summation of the upper-triangular distant-band correlations.
The geometric bound is uniform in both truncation parameters. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

theorem dyadic_inverse_pow_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, ((2 : ℝ) ^ j)⁻¹) = 2 * (1 - ((2 : ℝ) ^ N)⁻¹) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, mul_inv_rev]
    ring

theorem dyadic_inverse_pow_tail_sum_le (D M : ℕ) :
    (∑ r ∈ Finset.range M, ((2 : ℝ) ^ (D + r))⁻¹) ≤ 2 * ((2 : ℝ) ^ D)⁻¹ := by
  have hsum : (∑ r ∈ Finset.range M, ((2 : ℝ) ^ r)⁻¹) ≤ 2 := by
    rw [dyadic_inverse_pow_sum]
    have h : 0 ≤ ((2 : ℝ) ^ M)⁻¹ := by positivity
    linarith
  calc
    _ = ((2 : ℝ) ^ D)⁻¹ * (∑ r ∈ Finset.range M, ((2 : ℝ) ^ r)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add, mul_inv_rev, mul_comm]
    _ ≤ ((2 : ℝ) ^ D)⁻¹ * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := mul_comm _ _

namespace RealMobius

theorem dyadicBand_upper_far_sum_le (D M : ℕ) (indices : ℕ → Finset ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (g : Group) :
    let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
    (∑ r ∈ Finset.range M, ∑ j ∈ indices r,
      |inner ℝ (schwartzActionL2 g (u j)) ((u (j + (D + r))).toLp 2 volume)|) ≤
      (2 * ((2 : ℝ) ^ D)⁻¹ / (2 * Real.pi)) *
        (Real.sqrt (dyadicTransportConstant g) * Real.sqrt (dyadicCutoffDerivativeBound 0) *
          ‖hf.toLp f‖ ^ 2) := by
  let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
  let A := Real.sqrt (dyadicTransportConstant g) * Real.sqrt (dyadicCutoffDerivativeBound 0) * ‖hf.toLp f‖ ^ 2
  change (∑ r ∈ Finset.range M, ∑ j ∈ indices r,
    |inner ℝ (schwartzActionL2 g (u j)) ((u (j + (D + r))).toLp 2 volume)|) ≤
      (2 * ((2 : ℝ) ^ D)⁻¹ / (2 * Real.pi)) * A
  calc
    _ ≤ ∑ r ∈ Finset.range M, (((2 : ℝ) ^ (D + r))⁻¹ / (2 * Real.pi)) * A :=
      Finset.sum_le_sum (fun r _ => dyadicBand_offset_sum_le (indices r) hf hs g (D + r))
    _ = (∑ r ∈ Finset.range M, ((2 : ℝ) ^ (D + r))⁻¹) * (A / (2 * Real.pi)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ (2 * ((2 : ℝ) ^ D)⁻¹) * (A / (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_right (dyadic_inverse_pow_tail_sum_le D M) (by dsimp [A]; positivity)
    _ = _ := by ring

end RealMobius
end TransposeFollowup
