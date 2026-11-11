import SharedDecoders.CapacitySetCounting
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed

/-! # All-dimension rates for arbitrary cyclic correctness sets -/

namespace SharedDecoders.SetCapacity

open scoped BigOperators Topology
open Filter

variable {d : ℕ} [NeZero d] {A : Type*} [Fintype A]

/-- Exact relative error; `(d + 1) / 2` is the integer ceiling of `d / 2`. -/
theorem relative_error (hd : 2 ≤ d) (hq : 2 ≤ Fintype.card A) :
    |(d : ℝ) * (capacity (d := d) (A := A) : ℝ) / (Fintype.card A : ℝ) ^ (d * d) - 1| ≤
      ((d : ℝ) - 1) / (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) := by
  have hqpos : 0 < (Fintype.card A : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hq)
  have hN : 0 < (Fintype.card A : ℝ) ^ (d * d) := pow_pos hqpos _
  have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have he := errorSum_le (d := d) (A := A) (by omega)
  have hlo := (capacity_two_sided (d := d) (A := A)).1
  have hhi := (capacity_two_sided (d := d) (A := A)).2
  have hlow : (Fintype.card A : ℝ) ^ (d * d) ≤
      (d : ℝ) * (capacity (d := d) (A := A) : ℝ) +
        ((d : ℝ) - 1) * (Fintype.card A : ℝ) ^ (d * (d / 2)) := by
    have hh := hlo.trans (Nat.add_le_add_left he _)
    rw [← hsub]
    exact_mod_cast hh
  have hhigh : (d : ℝ) * (capacity (d := d) (A := A) : ℝ) ≤
      (Fintype.card A : ℝ) ^ (d * d) +
        ((d : ℝ) - 1) * (Fintype.card A : ℝ) ^ (d * (d / 2)) := by
    have hh := hhi.trans (Nat.add_le_add_left he _)
    rw [← hsub]
    exact_mod_cast hh
  have habs : |(d : ℝ) * (capacity (d := d) (A := A) : ℝ) -
        (Fintype.card A : ℝ) ^ (d * d)| ≤
      ((d : ℝ) - 1) * (Fintype.card A : ℝ) ^ (d * (d / 2)) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hexp : d * d = d * (d / 2) + d * ((d + 1) / 2) := by
    have hh : d / 2 + (d + 1) / 2 = d := by omega
    nlinarith [congrArg (d * ·) hh]
  have hsplit : (Fintype.card A : ℝ) ^ (d * d) =
      (Fintype.card A : ℝ) ^ (d * (d / 2)) *
      (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) := by rw [hexp, pow_add]
  calc
    |(d : ℝ) * (capacity (d := d) (A := A) : ℝ) /
        (Fintype.card A : ℝ) ^ (d * d) - 1| =
      |(d : ℝ) * (capacity (d := d) (A := A) : ℝ) -
        (Fintype.card A : ℝ) ^ (d * d)| / (Fintype.card A : ℝ) ^ (d * d) := by
        rw [div_sub_one hN.ne', abs_div, abs_of_pos hN]
    _ ≤ (((d : ℝ) - 1) * (Fintype.card A : ℝ) ^ (d * (d / 2))) /
        (Fintype.card A : ℝ) ^ (d * d) := div_le_div_of_nonneg_right habs hN.le
    _ = ((d : ℝ) - 1) / (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) := by
      rw [hsplit]
      field_simp

/-- Elementary exponential domination needed for the uniform factor-two lower bound. -/
theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  exact Nat.mul_le_pow (by decide) n

omit [NeZero d] in
theorem relative_bound_le_half (hd : 2 ≤ d) (hq : 2 ≤ Fintype.card A) :
    ((d : ℝ) - 1) / (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) ≤ 1 / 2 := by
  have hq : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hq
  have hpow : (2 : ℝ) ^ d ≤ (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) := by
    calc
      (2 : ℝ) ^ d ≤ (Fintype.card A : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) hq _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by
        have hc : 1 ≤ (d + 1) / 2 := by omega
        nlinarith)
  have htwo : (2 : ℝ) * d ≤ (2 : ℝ) ^ d := by exact_mod_cast two_mul_le_two_pow d
  have hp : 0 < (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) := pow_pos (by linarith) _
  apply (div_le_iff₀ hp).mpr
  linarith

/-- Uniform all-dimension lower bound, with the advertised constant one half. -/
theorem capacity_lower (hd : 2 ≤ d) (hq : 2 ≤ Fintype.card A) :
    (Fintype.card A : ℝ) ^ (d * d) / (2 * d) ≤ (capacity (d := d) (A := A) : ℝ) := by
  have h := (abs_le.mp ((relative_error hd hq).trans (relative_bound_le_half hd hq))).1
  have hqpos : 0 < (Fintype.card A : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hq)
  have hN : 0 < (Fintype.card A : ℝ) ^ (d * d) := pow_pos hqpos _
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  apply (div_le_iff₀ (mul_pos (by norm_num) hdpos)).mpr
  have hh : (1 / 2 : ℝ) ≤ (d : ℝ) * (capacity (d := d) (A := A) : ℝ) /
      (Fintype.card A : ℝ) ^ (d * d) := by linarith
  have hh := (le_div_iff₀ hN).mp hh
  nlinarith

omit [NeZero d] in
theorem relative_bound_le_geometric (hd : 2 ≤ d) (hq : 2 ≤ Fintype.card A) :
    ((d : ℝ) - 1) / (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) ≤
      (d : ℝ) / (2 : ℝ) ^ d := by
  have hq : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hq
  have hpow : (2 : ℝ) ^ d ≤ (Fintype.card A : ℝ) ^ (d * ((d + 1) / 2)) := by
    calc
      (2 : ℝ) ^ d ≤ (Fintype.card A : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) hq _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by
        have hc : 1 ≤ (d + 1) / 2 := by omega
        nlinarith)
  exact div_le_div₀ (Nat.cast_nonneg d) (by linarith) (pow_pos (by norm_num) _) hpow

/-- All positive integer dimensions in their natural order, with no prime restriction. -/
noncomputable def positiveCapacity (A : Type*) [Fintype A] (n : ℕ) : ℕ :=
  capacity (d := n + 1) (A := A)

/-- The normalized count converges to one along every positive integer dimension. -/
theorem normalized_capacity_tendsto (hq : 2 ≤ Fintype.card A) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (positiveCapacity A n : ℝ) /
      (Fintype.card A : ℝ) ^ ((n + 1) * (n + 1))) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_one, Function.comp_def] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [Real.norm_eq_abs, positiveCapacity] using
    (relative_error (d := n + 1) (A := A) (by omega) hq).trans
      (relative_bound_le_geometric (d := n + 1) (A := A) (by omega) hq)

/-- Precise meaning of the fixed-alphabet `o(1)` logarithmic remainder. -/
theorem logarithmic_rate_tendsto (hq : 2 ≤ Fintype.card A) :
    Tendsto (fun n : ℕ => Real.logb (Fintype.card A : ℝ) (positiveCapacity A n : ℝ) -
      (((n + 1 : ℕ) : ℝ) ^ 2 - Real.logb (Fintype.card A : ℝ) (n + 1))) atTop (𝓝 0) := by
  have hqreal : (1 : ℝ) < Fintype.card A := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hq)
  have hqpos : 0 < (Fintype.card A : ℝ) := by linarith
  have hlog := (Real.continuousAt_logb (b := (Fintype.card A : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (normalized_capacity_tendsto (A := A) hq)
  rw [Real.logb_one] at hlog
  apply hlog.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hdpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNpos : 0 < (Fintype.card A : ℝ) ^ ((n + 1) * (n + 1)) := pow_pos hqpos _
  have hcpos : 0 < (positiveCapacity A n : ℝ) := by
    apply lt_of_lt_of_le (div_pos hNpos (mul_pos (by norm_num : (0 : ℝ) < 2) hdpos))
    exact capacity_lower (d := n + 1) (A := A) (by omega) hq
  dsimp only [Function.comp_def]
  rw [Real.logb_div (mul_ne_zero hdpos.ne' hcpos.ne') hNpos.ne',
    Real.logb_mul hdpos.ne' hcpos.ne', Real.logb_pow, Real.logb_self_eq_one hqreal]
  push_cast
  ring

end SharedDecoders.SetCapacity
