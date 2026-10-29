import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic

/-! Limits for fixed-size subset capacities. Reuse Mathlib's binomial
asymptotic instead of rebuilding falling-factorial expansions. -/

namespace LeanMachine.FixedSubsetLimits

open Filter Asymptotics
open scoped Topology

/-- A positive limiting density forces a natural-valued size to diverge. -/
theorem atTop_of_ratio {s : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hs : Tendsto (fun N => (s N : ℝ) / N) atTop (𝓝 c)) : Tendsto s atTop atTop := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hc hs
  have ht' : Tendsto (fun N => (s N : ℝ)) atTop atTop := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  apply tendsto_atTop.2
  intro K
  exact (ht'.eventually_ge_atTop (K : ℝ)).mono fun N hN => by exact_mod_cast hN

/-- Fixed-size subset ratios converge to the corresponding density power. -/
theorem choose_ratio {s : ℕ → ℕ} {c : ℝ} (k : ℕ) (hc : 0 < c)
    (hs : Tendsto (fun N => (s N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => ((s N).choose k : ℝ) / N.choose k) atTop (𝓝 (c ^ k)) := by
  have he := ((isEquivalent_choose k).comp_tendsto (atTop_of_ratio hc hs)).div
    (isEquivalent_choose k)
  apply he.tendsto_nhds_iff.mpr
  convert hs.pow k using 1
  funext N
  simp only [Pi.div_apply, Function.comp_apply]
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp
  rw [div_pow]

/-- Natural rounding changes a normalized capacity by at most `1/N`. -/
theorem floor_successor_ratio {x : ℕ → ℝ} {c : ℝ}
    (hx : ∀ᶠ N in atTop, 0 ≤ x N)
    (ht : Tendsto (fun N => x N / N) atTop (𝓝 c)) :
    Tendsto (fun N => ((⌊x N⌋₊ : ℝ) + 1) / N) atTop (𝓝 c) := by
  have hu : Tendsto (fun N => (x N + 1) / N) atTop (𝓝 c) := by
    simpa only [add_zero, add_div] using ht.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ht hu
  · exact Eventually.of_forall fun N =>
      div_le_div_of_nonneg_right (Nat.lt_floor_add_one (x N)).le (Nat.cast_nonneg N)
  · filter_upwards [hx] with N hN
    exact div_le_div_of_nonneg_right (by linarith [Nat.floor_le hN]) (Nat.cast_nonneg N)

/-- A bank of `m` rounded balls has the expected capped limiting density. -/
theorem capped_capacity_ratio {x : ℕ → ℝ} {c : ℝ} (m : ℕ)
    (hx : ∀ᶠ N in atTop, 0 ≤ x N)
    (ht : Tendsto (fun N => x N / N) atTop (𝓝 c)) :
    Tendsto (fun N => ((min N (m * (⌊x N⌋₊ + 1)) : ℕ) : ℝ) / N)
      atTop (𝓝 (min 1 (m * c))) := by
  have hs := (tendsto_const_nhds (x := (1 : ℝ))).min
    ((floor_successor_ratio hx ht).const_mul (m : ℝ))
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Nat.cast_min, Nat.cast_mul, Nat.cast_add, Nat.cast_one, ← min_div_div_right hNR.le]
  simp [hNR.ne', mul_div_assoc]

/-- The inverse-power barrier diverges at small positive radii whenever
the fixed subset size exceeds one. -/
theorem inverse_power_diverges {k : ℕ} (hk : 2 ≤ k) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ => a * x * (1 / (c * x) ^ k - 1)) (𝓝[>] 0) atTop := by
  have hn : k - 1 ≠ 0 := by omega
  have hp := (tendsto_pow_atTop (α := ℝ) hn).comp tendsto_inv_nhdsGT_zero
  have ht := hp.const_mul_atTop (show 0 < a / c ^ k by positivity)
  have hz : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  apply (ht.atTop_add ((hz.const_mul a).neg)).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  have he : k = (k - 1) + 1 := by omega
  have hpx : x ^ k = x ^ (k - 1) * x := by
    nth_rw 1 [he]
    exact pow_succ x (k - 1)
  simp only [Function.comp_apply, inv_pow, mul_pow, hpx]
  field_simp
  ring

end LeanMachine.FixedSubsetLimits
