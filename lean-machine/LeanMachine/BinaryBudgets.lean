import LeanMachine.PolynomialMenus
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Exact binary bit budgets for polynomial records and finite-state
products. These are cardinality bounds, independent of any machine compiler. -/

namespace LeanMachine

theorem clog_two_le_logb_add_one {m : ℕ} (hm : 1 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ Real.logb 2 m + 1 := by
  rw [← Real.natCeil_logb_natCast]
  apply (Nat.ceil_lt_add_one ?_).le
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  exact_mod_cast hm

/-- Adding a default state costs at most one bit beyond the product bill. -/
theorem clog_state_product {Q q : ℕ} (hQ : Q ≤ 2 ^ q) (menu bits : ℕ) :
    Nat.clog 2 (1 + Q * menu * 2 ^ bits) ≤ 1 + q + Nat.clog 2 menu + bits := by
  apply Nat.clog_le_of_le_pow
  have hm := Nat.le_pow_clog (by decide : 1 < 2) menu
  have hproduct : Q * menu * 2 ^ bits ≤ 2 ^ (q + Nat.clog 2 menu + bits) := by
    calc
      _ ≤ 2 ^ q * 2 ^ Nat.clog 2 menu * 2 ^ bits := by gcongr
      _ = _ := by rw [pow_add, pow_add]
  have hpos : 1 ≤ 2 ^ (q + Nat.clog 2 menu + bits) := Nat.one_le_pow _ _ (by decide)
  calc
    _ ≤ 2 ^ (q + Nat.clog 2 menu + bits) + 2 ^ (q + Nat.clog 2 menu + bits) := by omega
    _ = 2 ^ (1 + q + Nat.clog 2 menu + bits) := by
      rw [show 1 + q + Nat.clog 2 menu + bits = (q + Nat.clog 2 menu + bits) + 1 by omega,
        pow_succ]
      omega

/-- Polynomial menus have small *integer* bit budgets, including the ceiling. -/
theorem polynomial_menu_clog_small {A B e : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ m : ℕ, 1 ≤ m → m ≤ A * (B * (P + 1)) ^ e →
      (Nat.clog 2 m : ℝ) ≤ ε * P := by
  obtain ⟨P₁, hr⟩ := polynomial_menu_logb_small hA hB (half_pos hε)
  refine ⟨max P₁ ⌈2 / ε⌉₊, ?_⟩
  intro P hP m hm hbound
  have hceil : 2 / ε ≤ (P : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right P₁ ⌈2 / ε⌉₊).trans hP)
  have hlin := (div_le_iff₀ hε).mp hceil
  have hsmall := hr P ((le_max_left _ _).trans hP) m hm hbound
  have hc := clog_two_le_logb_add_one hm
  linarith

end LeanMachine
