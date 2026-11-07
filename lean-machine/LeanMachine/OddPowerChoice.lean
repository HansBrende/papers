import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Choosing an odd exponent under an arbitrary power cap

The integer logarithm selects the largest positive odd exponent whose power
does not exceed a natural cap. The loss of fewer than two exponents converts
exponential error into a power of the cap with factor `exp (2 * a)`.
-/

namespace LeanMachine.OddPowerChoice

open Filter

set_option autoImplicit false

/-- The largest positive odd integer at most `Nat.log p Δ` when `p ≤ Δ`
and `1 < p`. It is set to one outside that range as well. -/
def exponent (p Δ : ℕ) : ℕ := 2 * ((Nat.log p Δ - 1) / 2) + 1

theorem exponent_pos (p Δ : ℕ) : 0 < exponent p Δ := by
  unfold exponent
  omega

theorem exponent_odd (p Δ : ℕ) : Odd (exponent p Δ) := by
  refine ⟨(Nat.log p Δ - 1) / 2, ?_⟩
  unfold exponent
  omega

theorem exponent_le_log {p Δ : ℕ} (hp : 1 < p) (hΔ : p ≤ Δ) :
    exponent p Δ ≤ Nat.log p Δ := by
  have := Nat.log_pos hp hΔ
  unfold exponent
  omega

theorem log_lt_exponent_add_two {p Δ : ℕ} (hp : 1 < p) (hΔ : p ≤ Δ) :
    Nat.log p Δ < exponent p Δ + 2 := by
  have := Nat.log_pos hp hΔ
  unfold exponent
  omega

/-- The explicit threshold is `Δ ≥ p`, stronger than an unspecified eventual
existence statement. -/
theorem power_bounds {p Δ : ℕ} (hp : 1 < p) (hΔ : p ≤ Δ) :
    p ^ exponent p Δ ≤ Δ ∧ Δ < p ^ (exponent p Δ + 2) := by
  exact ⟨Nat.pow_le_of_le_log (by omega) (exponent_le_log hp hΔ),
    Nat.lt_pow_of_log_lt hp (log_lt_exponent_add_two hp hΔ)⟩

/-- The scalar conversion needs only an upper bound by the next odd power.
The decay parameter may be zero, and the base and cap may be arbitrary reals. -/
theorem exp_le_rpow_of_le_pow {p x a : ℝ} {m : ℕ}
    (hp : 1 < p) (hx : 0 < x) (ha : 0 ≤ a) (hcap : x ≤ p ^ (m + 2)) :
    Real.exp (-a * m) ≤ Real.exp (2 * a) * x ^ (-a / Real.log p) := by
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlog := Real.log_le_log hx hcap
  rw [Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog ha
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply (mul_le_mul_iff_right₀ hlogp).mp
  field_simp
  push_cast at hmul
  nlinarith

/-- The selected odd exponent has the required power-law decay for every cap
at least the natural base. -/
theorem exponent_exp_le_rpow {p Δ : ℕ} (hp : 1 < p) (hΔ : p ≤ Δ)
    {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a * exponent p Δ) ≤
      Real.exp (2 * a) * (Δ : ℝ) ^ (-a / Real.log (p : ℝ)) := by
  apply exp_le_rpow_of_le_pow (by exact_mod_cast hp)
    (by exact_mod_cast (show 0 < Δ by omega)) ha
  exact_mod_cast (power_bounds hp hΔ).2.le

/-- One positive odd exponent simultaneously meets the degree and decay caps. -/
theorem exists_odd_power_and_decay {p Δ : ℕ} (hp : 1 < p) (hΔ : p ≤ Δ)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ p ^ m ≤ Δ ∧ Δ < p ^ (m + 2) ∧
      Real.exp (-a * m) ≤ Real.exp (2 * a) * (Δ : ℝ) ^ (-a / Real.log (p : ℝ)) :=
  ⟨exponent p Δ, exponent_pos p Δ, exponent_odd p Δ,
    (power_bounds hp hΔ).1, (power_bounds hp hΔ).2, exponent_exp_le_rpow hp hΔ ha⟩

theorem eventually_exists_odd_power_and_decay {p : ℕ} (hp : 1 < p)
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ᶠ Δ : ℕ in atTop, ∃ m : ℕ, 0 < m ∧ Odd m ∧ p ^ m ≤ Δ ∧ Δ < p ^ (m + 2) ∧
      Real.exp (-a * m) ≤ Real.exp (2 * a) * (Δ : ℝ) ^ (-a / Real.log (p : ℝ)) :=
  (eventually_ge_atTop p).mono fun _ hΔ => exists_odd_power_and_decay hp hΔ ha

end LeanMachine.OddPowerChoice
