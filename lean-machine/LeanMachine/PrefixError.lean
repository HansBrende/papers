import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Normalizing the finite prefix error

The runtime bound controls the full movement and residual-payment terms.
Ceilings and the maximum with an independently vanishing normalized size
have the expected limits. No geometry or limiting tail premise is used.
-/

namespace LeanMachine.PrefixError

open Filter
open scoped Topology

/-- Normalize the complete finite error, keeping the protected-hop term
exact. No sign condition on `H`, or positivity of `M-R`, is needed here. -/
theorem finite_error_le {d b w T J q M R N a : ℕ} {c β C H : ℝ}
    (hd : 0 < d) (hb : 0 < b) (hw : 0 < w)
    (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hT : (T : ℝ) ≤ c * (d * d * b)) :
    2 * C * ((T - 1 : ℕ) : ℝ) / (d * (d * d * b)) +
      2 * ((w : ℝ) - 1) / (d * d * b) +
      ((d : ℝ) * b - b + 1) / (2 * (d * d * b)) +
      β / (d * d * b) *
        (J + q + ((d * d * b : ℝ) * H) / ((M - R : ℕ) : ℝ) +
          (1 + (N : ℝ) * a) * C * ((T - 1 : ℕ) : ℝ) / w) ≤
    (2 * C * c + 1) / d + 2 * ((w : ℝ) / (d * d * b)) +
      β * (J + q) / (d * d * b) + β * H / ((M - R : ℕ) : ℝ) +
      β * C * c *
        ((1 / (d * d * b) + (N : ℝ) * ((a : ℝ) / (d * d * b))) /
          ((w : ℝ) / (d * d * b))) := by
  let L : ℝ := d * d * b
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hL : 0 < L := mul_pos (mul_pos hdR hdR) hbR
  have ht : ((T - 1 : ℕ) : ℝ) ≤ c * L :=
    le_trans (by exact_mod_cast Nat.sub_le T 1) hT
  have hmove : 2 * C * ((T - 1 : ℕ) : ℝ) / (d * L) ≤ 2 * C * c / d := by
    calc
      _ ≤ 2 * C * (c * L) / (d * L) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht (by positivity)) (by positivity)
      _ = _ := by field_simp
  have hwidth : 2 * ((w : ℝ) - 1) / L ≤ 2 * ((w : ℝ) / L) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (by linarith : (w : ℝ) - 1 ≤ w) hL.le) (by norm_num)
  have hstripe : ((d : ℝ) * b - b + 1) / (2 * L) ≤ 1 / d := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    calc
      _ ≤ ((d : ℝ) * b) / (2 * L) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / (2 * (d : ℝ)) := by dsimp [L]; field_simp
      _ ≤ 1 / d := one_div_le_one_div_of_le hdR (by linarith)
  have hres : (1 + (N : ℝ) * a) * C * ((T - 1 : ℕ) : ℝ) / w ≤
      (1 + (N : ℝ) * a) * C * (c * L) / w :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by positivity)) hwR.le
  have hpaid : β / L *
      ((J : ℝ) + q + (L * H) / ((M - R : ℕ) : ℝ) +
        (1 + (N : ℝ) * a) * C * ((T - 1 : ℕ) : ℝ) / w) ≤
      β * (J + q) / L + β * H / ((M - R : ℕ) : ℝ) +
        β * C * c * ((1 / L + (N : ℝ) * ((a : ℝ) / L)) / ((w : ℝ) / L)) := by
    calc
      _ ≤ β / L *
          ((J : ℝ) + q + (L * H) / ((M - R : ℕ) : ℝ) +
            (1 + (N : ℝ) * a) * C * (c * L) / w) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hres) (div_nonneg hβ hL.le)
      _ = _ := by
        by_cases hm : ((M - R : ℕ) : ℝ) = 0
        · simp only [hm, div_zero, add_zero]
          field_simp
        · field_simp
  change _ ≤ (2 * C * c + 1) / d + 2 * ((w : ℝ) / L) +
    β * (J + q) / L + β * H / ((M - R : ℕ) : ℝ) +
      β * C * c * ((1 / L + (N : ℝ) * ((a : ℝ) / L)) / ((w : ℝ) / L))
  change 2 * C * ((T - 1 : ℕ) : ℝ) / (d * L) +
    2 * ((w : ℝ) - 1) / L + ((d : ℝ) * b - b + 1) / (2 * L) +
    β / L * ((J : ℝ) + q + (L * H) / ((M - R : ℕ) : ℝ) +
      (1 + (N : ℝ) * a) * C * ((T - 1 : ℕ) : ℝ) / w) ≤ _
  rw [add_div (2 * C * c) 1 (d : ℝ)]
  linarith

/-- A ceiling does not change a fixed normalized slope. -/
theorem ceil_scaled_tendsto {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun n => (Nat.ceil (θ * (L n : ℝ)) : ℝ) / L n) atTop (𝓝 θ) :=
  (tendsto_nat_ceil_mul_div_atTop hθ).comp
    (tendsto_natCast_atTop_atTop.comp hL)

/-- A vanishing normalized outside-family bound does not change the fixed
ceiling slope. The lengths need not be positive at every initial index. -/
theorem max_ceil_scaled_tendsto {L a₀ : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (ha₀ : Tendsto (fun n => (a₀ n : ℝ) / L n) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun n => (max (a₀ n) (Nat.ceil (θ * (L n : ℝ))) : ℝ) / L n)
      atTop (𝓝 θ) := by
  have h := ha₀.max (ceil_scaled_tendsto hL hθ)
  simpa only [max_eq_right hθ, Nat.cast_max,
    max_div_div_right (Nat.cast_nonneg _)] using h

end LeanMachine.PrefixError
