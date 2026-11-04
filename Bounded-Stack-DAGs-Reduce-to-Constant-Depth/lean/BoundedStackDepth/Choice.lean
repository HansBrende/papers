import Mathlib

/-!
# The choice of the parameters

For `n` heads and `ε > 0`, the cut is bounded by `εT` once each of four error terms is at most `ε/4` per
unit of time:
* the terms paid by the grid offset (lost hops, charged hops, shown-set changes): `C₁ / h₀`;
* truncation: `2n² (1 − Q^{−n²})^j`;
* exposure: `2n² / Q`;
* the digit wraps: `C_K / K`.

* `le_natCeil_add_one_mul`: `C ≤ (⌈C/δ⌉ + 1) δ`, which fixes `h₀`, `Q` and `K`.
* `one_sub_pow_le_inv`, `one_sub_pow_natCeil_le_inv`: if `x ≤ 1`, `A ≥ 1` and `log A ≤ x j`, then
  `(1 − x)^j ≤ A⁻¹`; with `j = ⌈log A / x⌉` this fixes the number of blocks of Lemma D.
* `trunc_term_le`: with `j = ⌈ln A / Q^{−n²}⌉`, `A = max 1 (8n²/ε)`, the truncation term is at most `ε/4`.
-/

namespace BoundedStackDepth

/-- A constant is at most `N · δ` for `N = ⌈C/δ⌉ + 1`. -/
theorem le_natCeil_add_one_mul {C δ : ℝ} (hδ : 0 < δ) : C ≤ ((⌈C / δ⌉₊ + 1 : ℕ) : ℝ) * δ := by
  have h1 : C / δ ≤ ⌈C / δ⌉₊ := Nat.le_ceil _
  rw [div_le_iff₀ hδ] at h1
  push_cast
  nlinarith

/-- **Geometric tail.** If `x ≤ 1`, `1 ≤ A` and `log A ≤ x j`, then `(1 − x)^j ≤ A⁻¹`. -/
theorem one_sub_pow_le_inv {x A : ℝ} {j : ℕ} (hx1 : x ≤ 1) (hA : 1 ≤ A)
    (hj : Real.log A ≤ x * j) : (1 - x) ^ j ≤ A⁻¹ := by
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  calc (1 - x) ^ j ≤ (Real.exp (-x)) ^ j :=
        pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-x); linarith) j
    _ = Real.exp (-(x * j)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-Real.log A) := Real.exp_le_exp.mpr (by linarith)
    _ = A⁻¹ := by rw [Real.exp_neg, Real.exp_log hApos]

/-- With `j = ⌈log A / x⌉` and `0 < x ≤ 1`, `1 ≤ A`: `(1 − x)^j ≤ A⁻¹`. -/
theorem one_sub_pow_natCeil_le_inv {x A : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hA : 1 ≤ A) :
    (1 - x) ^ ⌈Real.log A / x⌉₊ ≤ A⁻¹ := by
  refine one_sub_pow_le_inv hx1 hA ?_
  have h := Nat.le_ceil (Real.log A / x)
  calc Real.log A = x * (Real.log A / x) := by field_simp
    _ ≤ x * ⌈Real.log A / x⌉₊ := mul_le_mul_of_nonneg_left h hx0.le

/-- The truncation term. With `x = (Q^{n²})⁻¹` and `j = ⌈ln A / x⌉` for `A = max 1 (8n²/ε)`,
`2n² (1 − x)^j ≤ ε/4`. -/
theorem trunc_term_le {ε : ℝ} (hε : 0 < ε) (n Q : ℕ) (hQ : 1 ≤ Q) :
    2 * (n : ℝ) ^ 2 * (1 - ((Q : ℝ) ^ (n * n))⁻¹) ^
        ⌈Real.log (max 1 (8 * (n : ℝ) ^ 2 / ε)) / ((Q : ℝ) ^ (n * n))⁻¹⌉₊ ≤ ε / 4 := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpow : (1 : ℝ) ≤ (Q : ℝ) ^ (n * n) := one_le_pow₀ hQ'
  have hx0 : (0 : ℝ) < ((Q : ℝ) ^ (n * n))⁻¹ := inv_pos.mpr (by linarith)
  have hx1 : ((Q : ℝ) ^ (n * n))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
  have hA : (1 : ℝ) ≤ max 1 (8 * (n : ℝ) ^ 2 / ε) := le_max_left _ _
  have h := one_sub_pow_natCeil_le_inv hx0 hx1 hA
  have hn : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by positivity
  calc 2 * (n : ℝ) ^ 2 * (1 - ((Q : ℝ) ^ (n * n))⁻¹) ^
        ⌈Real.log (max 1 (8 * (n : ℝ) ^ 2 / ε)) / ((Q : ℝ) ^ (n * n))⁻¹⌉₊
      ≤ 2 * (n : ℝ) ^ 2 * (max 1 (8 * (n : ℝ) ^ 2 / ε))⁻¹ := mul_le_mul_of_nonneg_left h hn
    _ ≤ ε / 4 := by
        rcases le_total (8 * (n : ℝ) ^ 2 / ε) 1 with hle | hle
        · rw [max_eq_left hle, inv_one, mul_one]
          rw [div_le_iff₀ hε] at hle
          linarith
        · rw [max_eq_right hle, inv_div]
          rcases eq_or_ne (n : ℝ) 0 with h0 | h0
          · rw [h0]; norm_num; positivity
          · have : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 h0
            rw [show 2 * (n : ℝ) ^ 2 * (ε / (8 * (n : ℝ) ^ 2)) = ε / 4 by field_simp; ring]

end BoundedStackDepth
