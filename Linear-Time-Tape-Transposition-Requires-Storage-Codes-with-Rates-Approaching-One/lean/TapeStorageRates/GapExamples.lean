import TapeStorageRates.RateGap

/-! # Concrete gap rates in the exclusion criteria -/

namespace TapeStorageRates

open Filter
open scoped Topology

set_option autoImplicit false

/-- An eventual inverse power with exponent below `1/(4k²+1)` makes the ratio in the fixed-k
exclusion criterion tend to infinity. -/
theorem ratio_tendsto_of_power_gap {k : ℕ} {ρ : ℕ → ℝ} {a c₀ : ℝ} (hc : 0<c₀)
    (ha : a < 1/(4*(k : ℝ)^2+1))
    (hlower : ∀ᶠ Δ : ℕ in atTop, c₀ / degreeLogLog Δ ^ a ≤ ρ Δ) :
    Tendsto (fun Δ => ρ Δ / deficitScale k Δ) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  let m := max K 1
  have hm : 0 < m := zero_lt_one.trans_le (le_max_right _ _)
  filter_upwards [hlower, tendsto_degreeLogLog.eventually_gt_atTop 1,
    (tendsto_power_mul_deficitScale ha).eventually_lt_const (div_pos hc hm)] with Δ hρ hy hsmall
  have hf : 0 < degreeLogLog Δ ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hy) _
  have hg : 0 < deficitScale k Δ :=
    Real.rpow_pos_of_pos (div_pos (Real.logb_pos (by norm_num) hy) (zero_lt_one.trans hy)) _
  have h₁ := (div_le_iff₀ hf).1 hρ
  have h₂ := (lt_div_iff₀ hm).1 hsmall
  have hprod : m * deficitScale k Δ ≤ ρ Δ := (mul_le_mul_iff_of_pos_right hf).1 (by linarith only [h₁,h₂])
  exact (le_div_iff₀ hg).2 ((mul_le_mul_of_nonneg_right (le_max_left K 1) hg.le).trans hprod)

/-- A gap bounded below by a constant over the triple logarithm passes the all-powers
criterion, with an actual limit of infinity for each positive exponent. -/
theorem all_powers_tendsto_of_triple_log_gap {ρ : ℕ → ℝ} {c₀ : ℝ} (hc : 0<c₀)
    (hlower : ∀ᶠ Δ : ℕ in atTop, c₀ / Real.logb 2 (degreeLogLog Δ) ≤ ρ Δ)
    {a : ℝ} (ha : 0<a) :
    Tendsto (fun Δ => ρ Δ * degreeLogLog Δ ^ a) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  let m := max K 1
  have hm : 0 < m := zero_lt_one.trans_le (le_max_right _ _)
  have ht := (logb_div_power ha).comp tendsto_degreeLogLog
  filter_upwards [hlower,tendsto_degreeLogLog.eventually_gt_atTop 1,
    ht.eventually_lt_const (div_pos hc hm)] with Δ hρ hy hsmall
  have hf : 0 < degreeLogLog Δ ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hy) _
  have hl : 0 < Real.logb 2 (degreeLogLog Δ) := Real.logb_pos (by norm_num) hy
  have h₁ := (div_le_iff₀ hl).1 hρ
  have h₂ := (div_lt_div_iff₀ hf hm).1 hsmall
  apply (le_max_left K 1).trans
  apply (mul_le_mul_iff_of_pos_right hl).1
  nlinarith only [h₂, mul_le_mul_of_nonneg_right h₁ hf.le]

private theorem eventually_doubleLog_le_log :
    ∀ᶠ Δ : ℕ in atTop, degreeLogLog Δ ≤ Real.logb 2 Δ := by
  have hlog : Tendsto (fun Δ : ℕ => Real.logb 2 Δ) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hr := (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero.comp hlog
  filter_upwards [hlog.eventually_gt_atTop 0, hr.eventually_lt_const (zero_lt_one : (0 : ℝ)<1)]
    with Δ hp h
  simpa only [degreeLogLog,one_mul] using ((div_lt_iff₀ hp).1 h).le

/-- The elementary gap `1/(Δ+1)` times each positive power of the double logarithm tends to zero. -/
theorem elementary_gap_power_tendsto_zero {a : ℝ} (ha : 0<a) :
    Tendsto (fun Δ : ℕ => (1/((Δ : ℝ)+1)) * degreeLogLog Δ ^ a) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => Real.logb 2 t ^ a / t) atTop (𝓝 0) := by
    apply ((logb_div_power (one_div_pos.2 ha)).rpow_const_nhds_zero ha).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t h
    rw [Real.div_rpow (Real.logb_pos (by norm_num) h).le (Real.rpow_nonneg (zero_lt_one.trans h).le _),
      ← Real.rpow_mul (zero_lt_one.trans h).le, one_div_mul_cancel ha.ne', Real.rpow_one]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ht.comp tendsto_natCast_atTop_atTop)
  · filter_upwards [tendsto_degreeLogLog.eventually_gt_atTop 0] with Δ hΔ
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hΔ.le _)
  · filter_upwards [eventually_doubleLog_le_log, tendsto_degreeLogLog.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℕ)] with Δ hlog hy hΔ
    change _ ≤ Real.logb 2 (Δ : ℝ) ^ a / Δ
    rw [one_div_mul_eq_div]
    exact div_le_div₀ (Real.rpow_nonneg (hy.le.trans hlog) _) (Real.rpow_le_rpow hy.le hlog ha.le)
      (by exact_mod_cast hΔ) (by linarith)

/-- The elementary gap also has vanishing ratio to the fixed-k deficit scale. -/
theorem elementary_gap_ratio_tendsto_zero (k : ℕ) :
    Tendsto (fun Δ : ℕ => (1/((Δ : ℝ)+1)) / deficitScale k Δ) atTop (𝓝 0) := by
  have h := elementary_gap_power_tendsto_zero (a := 1) zero_lt_one
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards [tendsto_degreeLogLog.eventually_gt_atTop 1] with Δ hy
    have hg : 0 < deficitScale k Δ :=
      Real.rpow_pos_of_pos (div_pos (Real.logb_pos (by norm_num) hy) (zero_lt_one.trans hy)) _
    exact div_nonneg (by positivity) hg.le
  · filter_upwards [tendsto_degreeLogLog.eventually_ge_atTop 2] with Δ hy
    let y := degreeLogLog Δ
    have hy₁ : 1 ≤ y := by linarith
    have hlog : 1 ≤ Real.logb 2 y := by
      simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using
        Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by norm_num) hy
    have hypos := zero_lt_one.trans_le hy₁
    let p := 4 * (k : ℝ)^2 + 1
    have hp : 1 ≤ p := by dsimp [p]; nlinarith [sq_nonneg (k : ℝ)]
    have hbound : (deficitScale k Δ)⁻¹ ≤ y := calc
      _ = (y / Real.logb 2 y) ^ (1/p : ℝ) := by
        change ((Real.logb 2 y / y) ^ (1/p : ℝ))⁻¹ = _
        rw [← Real.inv_rpow (div_nonneg (zero_le_one.trans hlog) hypos.le), inv_div]
      _ ≤ y ^ (1/p : ℝ) := Real.rpow_le_rpow (div_nonneg hypos.le (zero_le_one.trans hlog))
        (div_le_self hypos.le hlog) (by positivity)
      _ ≤ y := Real.rpow_le_self_of_one_le hy₁ ((div_le_one (zero_lt_one.trans_le hp)).2 hp)
    simpa only [div_eq_mul_inv, Real.rpow_one] using
      mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1/((Δ : ℝ)+1) by positivity)

end TapeStorageRates
