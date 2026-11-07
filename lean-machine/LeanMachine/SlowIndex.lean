import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # A slowly growing family index below the square-root size budget

An arbitrary sequence of finite sizes can be sampled at indices tending
to infinity while keeping the selected size at most the square root of
the requested length. Monotonicity of the original sequence is unnecessary.
-/

namespace LeanMachine.SlowIndex

open Filter
open scoped Topology
set_option autoImplicit false

/-- The latest eligible index among the first `M + 1` indices. -/
def index (n : ℕ → ℕ) (M : ℕ) : ℕ :=
  Nat.findGreatest (fun j => n j ≤ Nat.sqrt M) M

theorem size_le_sqrt (n : ℕ → ℕ) {M : ℕ} (hM : n 0 * n 0 ≤ M) :
    n (index n M) ≤ Nat.sqrt M :=
  Nat.findGreatest_spec (P := fun j => n j ≤ Nat.sqrt M)
    (Nat.zero_le M) (Nat.le_sqrt.mpr hM)

/-- Every fixed index eventually becomes eligible, so the selected index diverges. -/
theorem tendsto_index (n : ℕ → ℕ) : Tendsto (index n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [eventually_ge_atTop j, eventually_ge_atTop (n j * n j)] with M hj hn
  exact Nat.le_findGreatest hj (Nat.le_sqrt.mpr hn)

theorem eventually_size_le_sqrt (n : ℕ → ℕ) :
    ∀ᶠ M in atTop, n (index n M) ≤ Nat.sqrt M :=
  (eventually_ge_atTop (n 0 * n 0)).mono (fun _ => size_le_sqrt n)

/-- Repeating the selected block leaves fewer than a square root of the
requested coordinates uncovered. -/
theorem remainder_le_sqrt (n : ℕ → ℕ) (hn : ∀ j, 0 < n j)
    {M : ℕ} (hM : n 0 * n 0 ≤ M) :
    M % n (index n M) ≤ Nat.sqrt M :=
  (Nat.mod_lt M (hn _)).le.trans (size_le_sqrt n hM)

/-- The square-root padding charge has vanishing normalized cost. -/
theorem sqrt_div_tendsto :
    Tendsto (fun M : ℕ => Real.sqrt (M : ℝ) / M) atTop (𝓝 0) := by
  simp_rw [Real.sqrt_div_self]
  simpa only [Function.comp_def, Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg _)] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop

/-- A normalized square-root charge is eventually below any positive allowance. -/
theorem eventually_sqrt_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, Real.sqrt (M : ℝ) ≤ ε * M := by
  filter_upwards [sqrt_div_tendsto.eventually_lt_const hε,
    eventually_gt_atTop (0 : ℕ)] with M h hM
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  exact ((div_lt_iff₀ hMR).mp h).le

end LeanMachine.SlowIndex
