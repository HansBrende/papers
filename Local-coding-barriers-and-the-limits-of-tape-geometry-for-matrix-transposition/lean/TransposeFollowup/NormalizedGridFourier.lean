import TransposeFollowup.GridFourierCancellation
import TransposeFollowup.UnitSupportedL1
import TransposeFollowup.RealMobiusL2

/-! Classical Fourier bounds for the exact normalized inputs in the
restricted-gap statement, including actual real L2 representatives. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped FourierTransform
set_option autoImplicit false

theorem norm_fourier_le_unit_normalized_grid {K : ℕ} (hK : 0 < K) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hnorm : (∫ x, ‖f x‖ ^ 2) = 1)
    (hzero : ∀ i : Fin K, (∫ x in gridCell i, f x) = 0) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ 2 * Real.pi * |ξ| / K := by
  have hb := norm_fourier_le_grid hK (integrable_of_unit_supported_L2 hf hsupport)
    hsupport hzero ξ
  calc
    _ ≤ (2 * Real.pi * |ξ| / K) * ∫ x, ‖f x‖ := hb
    _ ≤ (2 * Real.pi * |ξ| / K) * 1 :=
      mul_le_mul_of_nonneg_left (integral_norm_le_one_of_unit_normalized hf hsupport hnorm)
        (by positivity)
    _ = _ := mul_one _

theorem integral_low_fourier_sq_le_unit_normalized_grid {K : ℕ} (hK : 0 < K)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hnorm : (∫ x, ‖f x‖ ^ 2) = 1)
    (hzero : ∀ i : Fin K, (∫ x in gridCell i, f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, ‖𝓕 f ξ‖ ^ 2) ≤ 8 * Real.pi ^ 2 * R ^ 3 / (K : ℝ) ^ 2 := by
  have hb := integral_low_fourier_sq_le_grid hK (integrable_of_unit_supported_L2 hf hsupport)
    hsupport hzero R hR
  have hm := integral_norm_sq_le_of_unit_supported_L2 hf hsupport
  rw [hnorm] at hm
  exact hb.trans ((mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (mul_one _))

theorem integral_low_fourier_sq_le_real_grid {K : ℕ} (hK : 0 < K) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hnorm : (∫ x, (f x) ^ 2) = 1)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) ≤
      8 * Real.pi ^ 2 * R ^ 3 / (K : ℝ) ^ 2 := by
  have hfc : MemLp (fun x => (f x : ℂ)) 2 volume := hf.ofReal
  apply integral_low_fourier_sq_le_unit_normalized_grid hK hfc _ _ _ R hR
  · filter_upwards [hsupport] with x hx hu
    rw [hx hu, Complex.ofReal_zero]
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hnorm
  · intro i
    rw [integral_complex_ofReal, gridCell_eq_Ioo, ← integral_Icc_eq_integral_Ioo, hzero i]
    exact Complex.ofReal_zero

namespace RealMobius

theorem normalized_realL2_low_fourier_sq {K : ℕ} (hK : 0 < K) (f : RealL2)
    (hnorm : ‖f‖ = 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) ≤
      8 * Real.pi ^ 2 * R ^ 3 / (K : ℝ) ^ 2 := by
  apply integral_low_fourier_sq_le_real_grid hK (Lp.memLp f) hsupport _ hzero R hR
  rw [← realL2_norm_sq, hnorm, one_pow]

theorem normalized_realL2_low_fourier_small {K : ℕ} (hK : 0 < K) (f : RealL2)
    (hnorm : ‖f‖ = 1)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0)
    (R : ℝ) (hR : 0 ≤ R) (hscale : 2048 * Real.pi ^ 2 * R ^ 3 ≤ (K : ℝ) ^ 2) :
    (∫ ξ in Icc (-R) R, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) ≤ 1 / 256 := by
  apply (normalized_realL2_low_fourier_sq hK f hnorm hsupport hzero R hR).trans
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
  nlinarith

/-- The threshold is uniform over all normalized functions in the grid
class. This is still a statement about the classical Fourier integral. -/
theorem exists_grid_threshold_low_fourier_small (R : ℝ) (hR : 0 ≤ R) :
    ∃ K₀ : ℕ, 0 < K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ f : RealL2, ‖f‖ = 1 →
      (∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) →
      (∀ i : Fin K, (∫ x in Icc ((i.val : ℝ) / K) (((i.val : ℝ) + 1) / K), f x) = 0) →
      (∫ ξ in Icc (-R) R, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) ≤ 1 / 256 := by
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (max 1 (2048 * Real.pi ^ 2 * R ^ 3))
  have hk₀ : (1 : ℝ) < K₀ := (le_max_left _ _).trans_lt hK₀
  have hk₀nat : 0 < K₀ := by exact_mod_cast (lt_trans zero_lt_one hk₀)
  refine ⟨K₀, hk₀nat, ?_⟩
  intro K hK f hn hs hz
  apply normalized_realL2_low_fourier_small (hk₀nat.trans_le hK) f hn hs hz R hR
  have hKK : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
  have hsize := (le_max_right 1 (2048 * Real.pi ^ 2 * R ^ 3)).trans_lt hK₀
  nlinarith

end RealMobius
end TransposeFollowup
