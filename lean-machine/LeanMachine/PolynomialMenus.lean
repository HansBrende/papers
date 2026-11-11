import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Fixed polynomial cardinality menus have sublinear logarithmic cost.
The finite threshold is uniform over all menu cardinalities below the stated
polynomial envelope, including parameters subsequently selected by an input. -/

namespace LeanMachine
open Filter

/-- A finite length threshold for every positive menu bounded by one fixed
polynomial in `P+1`. No asymptotic hypothesis on the menu itself is supplied. -/
theorem polynomial_menu_log_small {A B e : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ m : ℕ, 1 ≤ m → m ≤ A * (B * (P + 1)) ^ e →
      Real.log (m : ℝ) ≤ ε * P := by
  have hlog : Tendsto (fun P : ℕ => Real.log ((P : ℝ) + 1) / (P : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  let C : ℝ := Real.log A + (e : ℝ) * Real.log B
  have hconst : Tendsto (fun P : ℕ => C / (P : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htotal : Tendsto (fun P : ℕ => C / (P : ℝ) +
      (e : ℝ) * (Real.log ((P : ℝ) + 1) / (P : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hconst.add (hlog.const_mul (e : ℝ))
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp (htotal.eventually (gt_mem_nhds hε))
  refine ⟨max 1 P₀, ?_⟩
  intro P hP m hm hbound
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl : Real.log (m : ℝ) ≤ C + (e : ℝ) * Real.log ((P : ℝ) + 1) := by
    have hh : (m : ℝ) ≤ (A : ℝ) * ((B : ℝ) * ((P : ℝ) + 1)) ^ e := by exact_mod_cast hbound
    have hhlog := Real.log_le_log hmpos hh
    rw [Real.log_mul hApos.ne' (by positivity), Real.log_pow,
      Real.log_mul hBpos.ne' (by positivity)] at hhlog
    dsimp [C]
    linarith
  have hr : (C + (e : ℝ) * Real.log ((P : ℝ) + 1)) / (P : ℝ) < ε := by
    convert hP₀ P ((le_max_right _ _).trans hP) using 1; ring
  exact hl.trans ((div_lt_iff₀ hPpos).mp hr).le

/-- The same uniform finite threshold in bits. -/
theorem polynomial_menu_logb_small {A B e : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ m : ℕ, 1 ≤ m → m ≤ A * (B * (P + 1)) ^ e →
      Real.logb 2 (m : ℝ) ≤ ε * P := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₀, hh⟩ := polynomial_menu_log_small hA hB (mul_pos hε hlog2)
  refine ⟨P₀, fun P hP m hm hbound => ?_⟩
  rw [Real.logb, div_le_iff₀ hlog2]
  convert hh P hP m hm hbound using 1; ring

end LeanMachine
