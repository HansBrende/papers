import TransposeFollowup.CoveringPolynomialLoss
import Mathlib.Basic.ENNReal.Real

/-! Convert the actual finite ENNReal separation budget to a real power
bound. All coefficient and cardinal finiteness obligations are discharged. -/
namespace TransposeFollowup
open scoped ENNReal NNReal
set_option autoImplicit false

theorem separated_cardinality_power_bound {h Q α θ W : ℝ} {N n : ℕ}
    (hlarge : 2 ^ 100 ≤ h) (hN : (N : ℝ) ≤ h) (hQ0 : 0 ≤ Q) (hQ : Q ≤ h)
    (hα : 0 < α) (hαinv : α⁻¹ ^ 4 ≤ h) (hθ : 0 < θ) (hθinv : θ⁻¹ ≤ h) (hW : 0 ≤ W) :
    let q := ENNReal.ofReal θ
    let K₀ := 64 * (N : ℝ≥0∞) ^ 4
    let L := 8 * (K₀ ^ 2 / q ^ 2)
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    q ^ 2 ≤ 32768 * K₀ * L ^ 2 * K ^ 4 * M * (n : ℝ≥0∞) * ENNReal.ofReal W →
      1 ≤ h ^ 1140 * (n : ℝ) * W := by
  dsimp only
  let q := ENNReal.ofReal θ
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  intro hmass
  have hq0 : q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hθ
  have hK₀t : K₀ ≠ ⊤ := by dsimp only [K₀]; finiteness
  have hLt : L ≠ ⊤ := by dsimp only [L]; finiteness
  have hKt : K ≠ ⊤ := by dsimp only [K]; finiteness
  have hMt : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm := ENNReal.toReal_mono
    (show 32768 * K₀ * L ^ 2 * K ^ 4 * M * (n : ℝ≥0∞) * ENNReal.ofReal W ≠ ⊤ by finiteness) hmass
  have hM0 : 0 ≤ 33 ^ 4 * Q ^ 8 / α ^ 4 := by positivity
  dsimp only [K₀, L, K, M, q] at hm
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hθ.le,
    ENNReal.toReal_ofReal hM0, ENNReal.toReal_ofReal hW] at hm
  have hp := mul_le_mul_of_nonneg_right hm (sq_nonneg θ⁻¹)
  have he : θ ^ 2 * (θ⁻¹) ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hθ.ne', one_pow]
  rw [he] at hp
  have hc := localized_separation_coefficient_bound hlarge hN hQ0 hQ hα hαinv hθ hθinv
  have hc' := mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg n) hW)
  exact hp.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hc')

end TransposeFollowup
