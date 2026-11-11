import AdaptiveTransfer.GetterFinite

/-! Explicit density estimate matching the stated gamma condition. One
weighted generating parameter treats the whole sparse support/value menu,
including J=0, without an independence premise or a division by J.
-/

namespace AdaptiveTransfer.Getter
open Finset LeanMachine
open scoped BigOperators

theorem sparse_explicit_density {n J P k a A : ℕ} {c γ : ℝ}
    (hk : 1 ≤ k) (hc : 1 ≤ c) (hγ : 0 < γ) (hγhalf : γ ≤ 1 / 2)
    (hA : A ≤ 2 ^ a) (hn : (n : ℝ) ≤ 2 * k * c * P) (hJ : (J : ℝ) ≤ γ * P) :
    Real.logb 2 (∑ j ∈ range (min n J + 1), n.choose j * A ^ j : ℕ) ≤
      γ * ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) * P := by
  let x := γ / (2 * (k : ℝ) * c * (2 : ℝ) ^ a)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hd : 0 < 2 * (k : ℝ) * c * (2 : ℝ) ^ a := by positivity
  have hx : 0 < x := div_pos hγ hd
  have hx1 : x ≤ 1 := by
    apply (div_le_one hd).mpr
    have hkc : (1 : ℝ) ≤ (k : ℝ) * c := hk'.trans (le_mul_of_one_le_right (by positivity) hc)
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (k : ℝ) * c by positivity)
    nlinarith
  have hAr : (A : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast hA
  have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hlog : Real.log (1 + (A : ℝ) * x) ≤ (A : ℝ) * x := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + (A : ℝ) * x by positivity)
    linarith
  have hfirst : (n : ℝ) * Real.log (1 + (A : ℝ) * x) ≤ γ * P := by
    calc
      _ ≤ (n : ℝ) * ((A : ℝ) * x) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
      _ ≤ (2 * (k : ℝ) * c * P) * ((2 : ℝ) ^ a * x) := by gcongr
      _ = _ := by dsimp [x]; field_simp
  have hsecond : -(J : ℝ) * Real.log x ≤ -(γ * P) * Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_right hJ (neg_nonneg.mpr hlogx)]
  have hbound := weightedSparseMenu_log_le n J (Nat.cast_nonneg A) hx hx1
  have hb : Real.log (weightedSparseMenu n J (A : ℝ)) ≤ γ * (1 - Real.log x) * P := by
    nlinarith
  have heq : 2 * Real.exp 1 * k * c / γ = Real.exp 1 / (x * (2 : ℝ) ^ a) := by
    dsimp [x]
    field_simp
  have hlogid : Real.log (2 * Real.exp 1 * k * c / γ) =
      1 - Real.log x - (a : ℝ) * Real.log 2 := by
    rw [heq, Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_mul hx.ne' (by positivity), Real.log_pow]
    ring
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) * Real.log 2 =
      1 - Real.log x := by
    rw [Real.logb, add_mul, div_mul_cancel₀ _ hl2.ne', hlogid]
    ring
  rw [Real.logb, div_le_iff₀ hl2]
  have he : γ * ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) * P * Real.log 2 =
      γ * (1 - Real.log x) * P := by
    rw [show γ * ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) * P * Real.log 2 =
      γ * (((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) * Real.log 2) * P by ring, hcoef]
  rw [he]
  simpa only [weightedSparseMenu, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using hb

theorem getter_sparse_budget {k a P J A N : ℕ} {c γ : ℝ}
    (hk : 1 ≤ k) (hP : 1 ≤ P) (hc : 1 ≤ c) (hγ : 0 < γ) (hγhalf : γ ≤ 1 / 2)
    (hA : A ≤ 2 ^ a) (hJ : (J : ℝ) ≤ γ * P)
    (hbudget : γ * ((a : ℝ) + Real.logb 2 (2 * Real.exp 1 * k * c / γ)) ≤ 1 / (64 * (N : ℝ))) :
    Real.logb 2 (returnSparseMenu k (returnTime P c) J A : ℕ) ≤ (P : ℝ) / (64 * (N : ℝ)) := by
  have ht : (returnTime P c : ℝ) ≤ c * ((P : ℝ) + 1) := Nat.floor_le (by positivity)
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hn : ((k * returnTime P c : ℕ) : ℝ) ≤ 2 * k * c * P := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k)
    have hh' := mul_le_mul_of_nonneg_left hPr (show 0 ≤ (k : ℝ) * c by positivity)
    nlinarith
  exact (sparse_explicit_density hk hc hγ hγhalf hA hn hJ).trans
    (by simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg P))

end AdaptiveTransfer.Getter
