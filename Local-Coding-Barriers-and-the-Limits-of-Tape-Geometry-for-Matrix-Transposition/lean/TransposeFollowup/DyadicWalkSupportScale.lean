import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Uniform support growth for every bounded autocorrelation iterate in
the actual dyadic walk-length regime. No support-power bound is assumed. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem quarter_pow_rpow_neg (j : ℕ) (s : ℝ) :
    ((1 / 4 : ℝ) ^ j) ^ (-s) = (4 : ℝ) ^ ((j : ℝ) * s) := by
  calc
    _ = (((1 / 4 : ℝ) ^ j)⁻¹) ^ s := Real.rpow_neg_eq_inv_rpow _ _
    _ = ((4 : ℝ) ^ j) ^ s := by rw [← inv_pow]; norm_num
    _ = _ := (Real.rpow_natCast_mul (by norm_num) j s).symm

theorem dyadic_walk_support_power_bound (ell i : ℕ) :
    32 * ((4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i) + 1) ^ 6 ≤
      (4 : ℝ) ^ (6 + (12 * ell + 18) * 2 ^ i) := by
  let R := (4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i)
  have he : R = (4 : ℝ) ^ ((2 * ell + 3) * 2 ^ i) := by
    dsimp only [R]
    rw [pow_mul]
    congr 1
    rw [pow_add, Nat.mul_comm 2 ell, pow_mul]
    ring
  have hR : 1 ≤ R := he ▸ one_le_pow₀ (by norm_num)
  calc
    32 * (R + 1) ^ 6 ≤ 32 * (2 * R) ^ 6 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 6) (by norm_num)
    _ = (32 * 2 ^ 6) * R ^ 6 := by ring
    _ ≤ (4 : ℝ) ^ 6 * R ^ 6 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (by linarith) 6)
    _ = _ := by
      rw [he, ← pow_mul, ← pow_add]
      congr 1
      ring

theorem exists_dyadic_walk_support_threshold {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∃ N₀ J₀ : ℕ, 0 < N₀ ∧
      ∀ N j ell i : ℕ, N₀ ≤ N → J₀ ≤ j → 2 * N * ell ≤ j → i ≤ k →
        32 * ((4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i) + 1) ^ 6 ≤
          ((1 / 4 : ℝ) ^ j) ^ (-s) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max 1 (12 * (2 : ℝ) ^ k / s))
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt (2 * (6 + 18 * (2 : ℝ) ^ k) / s)
  have hNpos : 0 < N₀ := by exact_mod_cast (zero_lt_one.trans ((le_max_left _ _).trans_lt hN₀))
  refine ⟨N₀, J₀, hNpos, ?_⟩
  intro N j ell i hN hj hlen hi
  have hNscale : 12 * (2 : ℝ) ^ k ≤ s * (N : ℝ) := by
    have hb := (le_max_right _ _).trans hN₀.le
    have hn : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hh := (div_le_iff₀ hs).mp (hb.trans hn)
    nlinarith
  have hJscale : 2 * (6 + 18 * (2 : ℝ) ^ k) ≤ s * (j : ℝ) := by
    have hj' : (J₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hh := (div_le_iff₀ hs).mp (hJ₀.le.trans hj')
    nlinarith
  have hlen' : 2 * (N : ℝ) * (ell : ℝ) ≤ (j : ℝ) := by exact_mod_cast hlen
  have hmain : 6 + (12 * (ell : ℝ) + 18) * (2 : ℝ) ^ k ≤ (j : ℝ) * s := by
    nlinarith [mul_le_mul_of_nonneg_right hNscale (Nat.cast_nonneg ell),
      mul_le_mul_of_nonneg_left hlen' hs.le]
  have hi' : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hi
  have he : ((6 + (12 * ell + 18) * 2 ^ i : ℕ) : ℝ) ≤ (j : ℝ) * s := by
    push_cast
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hi' (by positivity))).trans hmain
  calc
    _ ≤ (4 : ℝ) ^ (6 + (12 * ell + 18) * 2 ^ i) := dyadic_walk_support_power_bound ell i
    _ = (4 : ℝ) ^ (((6 + (12 * ell + 18) * 2 ^ i : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
    _ ≤ (4 : ℝ) ^ ((j : ℝ) * s) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = _ := (quarter_pow_rpow_neg j s).symm

theorem exists_quarter_scale_threshold {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j → (1 / 4 : ℝ) ^ j ≤ η₀ := by
  obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hη₀ (by norm_num : (1 / 4 : ℝ) < 1)
  exact ⟨J₀, fun j hj => (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hJ₀.le⟩

end TransposeFollowup
