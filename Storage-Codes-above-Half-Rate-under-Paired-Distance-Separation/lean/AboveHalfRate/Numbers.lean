import AboveHalfRate.Fluid
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The numbers of the explicit instance

The explicit instance of Theorem A uses the prime `p = 127`, the weight `k = 91`, the base level
`ℓ = 509` and the base graph with `n = 2 197 862` vertices, regular of degree `δ = 127² + 1 = 16130`.
This file checks the numerical facts used in the proofs, by `norm_num` on exact rational bounds.

* `params`: `127` and `509` are prime, `127 ≡ 2` and `509 ≡ 4 (mod 5)` (so `127` is inert and `509`
  splits in `ℚ(√5)`), `509 > 4 · 127`, `|PSL₂(𝔽₅₀₉)| = 65 935 860`, its sixtieth part is
  `1 098 931`, and `n = 2 · 1 098 931`; the local code has degree `m = 91 · 126 = 11466` and
  redundancy `t = 127² − m = 4663`; the rate `8100/16130` exceeds `0.5021`, hence `1/2`; and the
  exponent `4n` of the bound `Δ < 127^(4n)` is `8 791 448`.
* `base_degeneracy`: `⌈τ δ + 317⌉ = 4640` for `τ = 2 − √3`, and `4640 ≤ 4663`.
* `base_bernstein`: Bernstein's condition of Theorem D holds at `λ = 317`:
  `2 n exp(−λ² / (2 (τ (1 − τ) δ + λ / 3))) < 1`.
* `binary_rate`: `(8100 / 16130) · log₂ (127²) / 14 > 0.5013 > 1/2`, and `127² ≤ 2¹⁴`.
-/

namespace AboveHalf.Numbers

open Real AboveHalf.Fluid

set_option autoImplicit false

/-- The arithmetic parameters of the explicit instance. -/
theorem params :
    Nat.Prime 127 ∧ Nat.Prime 509 ∧ 127 % 5 = 2 ∧ 509 % 5 = 4 ∧ 4 * 127 < 509 ∧
    509 * (509 ^ 2 - 1) / 2 = 65935860 ∧ 65935860 % 60 = 0 ∧ 65935860 / 60 = 1098931 ∧
    2 * 1098931 = 2197862 ∧ 127 ^ 2 + 1 = 16130 ∧ 91 * (127 - 1) = 11466 ∧
    127 ^ 2 - 91 * (127 - 1) = 4663 ∧ (91 - 1) ^ 2 = 8100 ∧ 2 * 8100 > 16130 ∧
    5021 * 16130 < 8100 * 10000 ∧ 4 * 2197862 = 8791448 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

theorem sqrt_three_bounds : (17320508 : ℝ) / 10 ^ 7 < √3 ∧ √3 < 17320509 / 10 ^ 7 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The degeneracy of the base: `⌈τ δ + 317⌉ = 4640 ≤ 4663`. -/
theorem base_degeneracy :
    ⌈tau * 16130 + 317⌉₊ = 4640 ∧ (4640 : ℕ) ≤ 4663 := by
  obtain ⟨h1, h2⟩ := sqrt_three_bounds
  refine ⟨?_, by norm_num⟩
  rw [Nat.ceil_eq_iff (by norm_num)]
  unfold tau
  constructor <;> push_cast <;> nlinarith

/-- **Bernstein's condition at `λ = 317`** for the base graph of the explicit instance. -/
theorem base_bernstein :
    2 * (2197862 : ℝ) *
      Real.exp (-((317 : ℝ) ^ 2 / (2 * (tau * (1 - tau) * 16130 + 317 / 3)))) < 1 := by
  obtain ⟨h1, h2⟩ := sqrt_three_bounds
  -- the exponent is at least `15.36`
  have hv : tau * (1 - tau) * 16130 + 317 / 3 ≤ 100489 / (2 * (1536 / 100)) := by
    unfold tau
    have : (2 - √3) * (1 - (2 - √3)) = 3 * √3 - 5 := by
      ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
    rw [this]
    nlinarith
  have hvpos : 0 < tau * (1 - tau) * 16130 + 317 / 3 := by
    have := tau_pos
    have := tau_lt_one
    positivity
  have hA : (1536 : ℝ) / 100 ≤ (317 : ℝ) ^ 2 / (2 * (tau * (1 - tau) * 16130 + 317 / 3)) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2 * (1536 / 100))
    rw [mul_div_cancel₀ _ (by norm_num)] at this
    nlinarith
  -- `exp 15.36 ≥ e¹⁵ · 1.36 > 2n`
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexp : 2 * (2197862 : ℝ) < Real.exp (1536 / 100) := by
    have hsplit : Real.exp (1536 / 100) = Real.exp 1 ^ 15 * Real.exp (36 / 100) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hpow : (2.7182818283 : ℝ) ^ 15 < Real.exp 1 ^ 15 :=
      pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have hlin : (136 : ℝ) / 100 ≤ Real.exp (36 / 100) := by
      have := Real.add_one_le_exp (36 / 100 : ℝ); linarith
    rw [hsplit]
    calc 2 * (2197862 : ℝ) < (2.7182818283 : ℝ) ^ 15 * (136 / 100) := by norm_num
      _ ≤ Real.exp 1 ^ 15 * Real.exp (36 / 100) := by
        apply mul_le_mul hpow.le hlin (by norm_num) (by positivity)
  have hmono : Real.exp (-((317 : ℝ) ^ 2 / (2 * (tau * (1 - tau) * 16130 + 317 / 3)))) ≤
      Real.exp (-(1536 / 100)) := Real.exp_le_exp.2 (by linarith)
  have hinv : Real.exp (-(1536 / 100 : ℝ)) = (Real.exp (1536 / 100))⁻¹ := Real.exp_neg _
  calc 2 * (2197862 : ℝ) * Real.exp (-((317 : ℝ) ^ 2 / (2 * (tau * (1 - tau) * 16130 + 317 / 3))))
      ≤ 2 * (2197862 : ℝ) * Real.exp (-(1536 / 100)) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 2 * (2197862 : ℝ) / Real.exp (1536 / 100) := by rw [hinv, ← div_eq_mul_inv]
    _ < 1 := by rw [div_lt_one (Real.exp_pos _)]; exact hexp

/-- **The binary rate.** Fourteen bits encode `𝔽_{127²}`, and the binary blow-up keeps the rate
above `0.5013`: `(8100 / 16130) · log₂ (127²) / 14 > 0.5013`, from `log₂ (127²) > 615/44`. -/
theorem binary_rate :
    127 ^ 2 ≤ 2 ^ 14 ∧ (5013 : ℝ) / 10000 < 8100 / 16130 * Real.logb 2 (127 ^ 2) / 14 := by
  refine ⟨by norm_num, ?_⟩
  -- `log₂ 16129 > 615 / 44`, since `2 ^ 615 < 16129 ^ 44`
  have hlog : (615 : ℝ) / 44 < Real.logb 2 (127 ^ 2) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    have hpow : ((2 : ℝ) ^ ((615 : ℝ) / 44)) ^ (44 : ℕ) = (2 : ℝ) ^ (615 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        show ((615 : ℝ) / 44) * ((44 : ℕ) : ℝ) = ((615 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    -- split the power to stay below the evaluation threshold of `norm_num`
    have hnat : (2 : ℕ) ^ 615 < (127 ^ 2) ^ 44 := by
      have h3 : (2 : ℕ) ^ 615 = 2 ^ 205 * 2 ^ 205 * 2 ^ 205 := by rw [← pow_add, ← pow_add]
      rw [h3]
      norm_num
    have h44 : ((2 : ℝ) ^ ((615 : ℝ) / 44)) ^ (44 : ℕ) < ((127 : ℝ) ^ 2) ^ (44 : ℕ) := by
      rw [hpow]
      exact_mod_cast hnat
    exact lt_of_pow_lt_pow_left₀ 44 (by positivity) h44
  nlinarith

end AboveHalf.Numbers
