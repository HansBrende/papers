import TapeStorageRates.DegreeInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Degree-dependent upper bounds on binary storage rates

The conclusions in this file assume the quantitative transfer. Unbounded upper limit is
expressed as exceeding each fixed real threshold at arbitrarily large natural degree caps.
-/

namespace TapeStorageRates

open Filter DirectedRecovery
open scoped Topology

set_option autoImplicit false

/-- An eventual upper bound on the limiting upper rates of all admissible families. -/
def FamilyRateGap (ρ : ℕ → ℝ) : Prop :=
  ∀ᶠ Δ : ℕ in atTop, 0 ≤ ρ Δ ∧ ∀ F : SeparatedBinaryFamily Δ,
    limsup (fun i => storageCodeRate (F.code i)) atTop ≤ 1 - ρ Δ

/-- Nonempty binary codes have rates in `[0,1]`, so the lower limit is at most the upper limit. -/
theorem SeparatedBinaryFamily.liminf_le_limsup {Δ : ℕ} (F : SeparatedBinaryFamily Δ) :
    liminf (fun i => storageCodeRate (F.code i)) atTop ≤
      limsup (fun i => storageCodeRate (F.code i)) atTop :=
  Filter.liminf_le_limsup
    (isBoundedUnder_of ⟨1, fun i => MergeDepth.storageCodeRate_le_one (by simp) (F.code i)⟩)
    (isBoundedUnder_of ⟨0, fun i => MergeDepth.storageCodeRate_nonneg (by simp) (F.nonempty i)⟩)

private theorem eventually_pos_scale (k : ℕ) :
    ∀ᶠ Δ : ℕ in atTop, 0 < deficitScale k Δ := by
  filter_upwards [tendsto_degreeLogLog.eventually_gt_atTop 1] with Δ hΔ
  exact Real.rpow_pos_of_pos (div_pos (Real.logb_pos (by norm_num) hΔ) (zero_lt_one.trans hΔ)) _

private theorem eventually_scale_mono {j k : ℕ} (hjk : j ≤ k) :
    ∀ᶠ Δ : ℕ in atTop, deficitScale j Δ ≤ deficitScale k Δ := by
  have hr := (Real.isLittleO_logb_id_atTop (b := 2)).tendsto_div_nhds_zero.comp tendsto_degreeLogLog
  filter_upwards [tendsto_degreeLogLog.eventually_gt_atTop 1,
    hr.eventually_lt_const (zero_lt_one : (0 : ℝ) < 1)] with Δ hΔ hratio
  apply Real.rpow_le_rpow_of_exponent_ge
    (div_pos (Real.logb_pos (by norm_num) hΔ) (zero_lt_one.trans hΔ)) hratio.le
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  nlinarith [sq_nonneg ((k : ℝ) - j), mul_nonneg (sub_nonneg.mpr hjk') (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- A witness for a smaller tape count satisfies the weaker rate requirement at a larger one. -/
theorem RateWitnesses.mono {j k : ℕ} (hj : RateWitnesses j) (hjk : j ≤ k) : RateWitnesses k := by
  obtain ⟨K, hK, h⟩ := hj
  refine ⟨K, hK, ?_⟩
  filter_upwards [h, eventually_scale_mono hjk] with Δ ⟨F, hF⟩ hscale
  exact ⟨F, (sub_le_sub_left (mul_le_mul_of_nonneg_left hscale hK.le) 1).trans hF⟩

/-- An upper bound is needed only at caps where it beats the indicated loss.
It suffices there to bound each family's lower limiting rate. -/
theorem no_witnesses_of_sparse_rate_bounds {k : ℕ} {ρ : ℕ → ℝ}
    (hsparse : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ ∧
      ∀ F : SeparatedBinaryFamily Δ, liminf (fun i => storageCodeRate (F.code i)) atTop ≤ 1-ρ Δ) :
    ¬ RateWitnesses k := by
  rintro ⟨K, _, hfamilies⟩
  obtain ⟨Δ, ⟨⟨hgap,hupper⟩,⟨F,hF⟩⟩,hpos⟩ :=
    (((hsparse K).and_eventually hfamilies).and_eventually (eventually_pos_scale k)).exists
  have := (lt_div_iff₀ hpos).mp hgap
  linarith [hupper F]

/-- An eventual upper bound at all caps supplies the sparse criterion. -/
theorem FamilyRateGap.sparse_bounds {ρ : ℕ → ℝ} (hgap : FamilyRateGap ρ) {k : ℕ}
    (hu : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ) (K : ℝ) :
    ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ ∧
      ∀ F : SeparatedBinaryFamily Δ, liminf (fun i => storageCodeRate (F.code i)) atTop ≤ 1-ρ Δ :=
  ((hu K).and_eventually hgap).mono fun _ ⟨h,_,hub⟩ => ⟨h, fun F => F.liminf_le_limsup.trans (hub F)⟩

/-- A degree gap whose ratio to the prescribed deficit is unbounded rules out all witnesses. -/
theorem FamilyRateGap.no_witnesses {ρ : ℕ → ℝ} (hgap : FamilyRateGap ρ) {k : ℕ}
    (hunbounded : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ) : ¬ RateWitnesses k :=
  no_witnesses_of_sparse_rate_bounds (hgap.sparse_bounds hunbounded)

/-- If the gap divided by the fixed-`k` deficit scale has unbounded upper limit, every machine
with at most `k` work tapes fails at all sufficiently large dimensions for each positive time
coefficient. This deduction assumes the quantitative transfer. -/
theorem no_transposer_of_unbounded_ratio (hquant : QuantitativeTarget) {ρ : ℕ → ℝ}
    (hgap : FamilyRateGap ρ) {k : ℕ} (hk : 1 ≤ k)
    (hunbounded : ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ / deficitScale k Δ)
    (M : Transpose.TM) (htapes : M.k ≤ k) (c : ℝ) (hc : 0 < c) :
    ¬ (∀ d₀ : ℕ, ∃ d ≥ d₀, MergeDepth.TransposesAt M d c) :=
  fun hgood => hgap.no_witnesses hunbounded ((hquant M c hc hgood).mono (max_le hk htapes))

theorem logb_div_power {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ => Real.logb 2 y / y ^ a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.div_const (Real.log 2)
  simpa only [Real.logb, div_right_comm (Real.log _) (Real.log 2), zero_div] using h

/-- At fixed tape count, multiplying the quantitative deficit scale by any double-log power
strictly below the endpoint still gives a quantity tending to zero. -/
theorem tendsto_power_mul_deficitScale {k : ℕ} {a : ℝ}
    (ha : a < 1 / (4 * (k : ℝ) ^ 2 + 1)) :
    Tendsto (fun Δ => degreeLogLog Δ ^ a * deficitScale k Δ) atTop (𝓝 0) := by
  let p := 4 * (k : ℝ) ^ 2 + 1
  have hp : 0 < p := by dsimp [p]; positivity
  have hgap : 0 < 1 - a * p := sub_pos.mpr ((lt_div_iff₀ hp).mp ha)
  have h := ((logb_div_power hgap).comp tendsto_degreeLogLog).rpow_const_nhds_zero (one_div_pos.2 hp)
  apply h.congr'
  filter_upwards [tendsto_degreeLogLog.eventually_gt_atTop 1] with Δ hy
  let y := degreeLogLog Δ
  have hpos : 0 < y := zero_lt_one.trans hy
  have hl := (Real.logb_pos (by norm_num : (1 : ℝ)<2) hy).le
  have he : (1-a*p)*(1/p) = 1/p-a := by field_simp
  change (Real.logb 2 y / y ^ (1-a*p)) ^ (1/p) = y ^ a * (Real.logb 2 y / y) ^ (1/p)
  rw [Real.div_rpow hl (Real.rpow_nonneg hpos.le _), ← Real.rpow_mul hpos.le, he,
    Real.rpow_sub hpos, Real.div_rpow hl hpos.le, div_div_eq_mul_div]
  ring

/-- Any exponent strictly below the endpoint is eventually dominated by the inverse
degree scale, including the half-endpoint used for the all-powers criterion. -/
theorem eventually_power_le_inv_scale_of_lt {k : ℕ} {a : ℝ}
    (ha : a < 1 / (4 * (k : ℝ) ^ 2 + 1)) :
    ∀ᶠ Δ : ℕ in atTop, degreeLogLog Δ ^ a ≤ 1 / deficitScale k Δ := by
  filter_upwards [(tendsto_power_mul_deficitScale ha).eventually_lt_const zero_lt_one,
    eventually_pos_scale k] with Δ h hpos
  exact (le_div_iff₀ hpos).mpr h.le

theorem eventually_power_le_inv_scale (k : ℕ) :
    ∀ᶠ Δ : ℕ in atTop,
      degreeLogLog Δ ^ (1 / (2 * (4 * (k : ℝ) ^ 2 + 1)) : ℝ) ≤ 1 / deficitScale k Δ :=
  eventually_power_le_inv_scale_of_lt (one_div_lt_one_div_of_lt (by positivity) (by nlinarith [sq_nonneg (k:ℝ)]))

/-- If the gap times every positive power of the double logarithm has unbounded upper limit,
every fixed finite machine fails the unbounded-dimension transposition premise. -/
theorem no_transposer_of_all_powers (hquant : QuantitativeTarget) {ρ : ℕ → ℝ}
    (hgap : FamilyRateGap ρ)
    (hpowers : ∀ a : ℝ, 0 < a → ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ * degreeLogLog Δ ^ a)
    (M : Transpose.TM) (c : ℝ) (hc : 0 < c) :
    ¬ (∀ d₀ : ℕ, ∃ d ≥ d₀, MergeDepth.TransposesAt M d c) := by
  let k := max 1 M.k
  apply no_transposer_of_unbounded_ratio hquant hgap (le_max_left 1 M.k) _ M (le_max_right 1 M.k) c hc
  intro K
  have h := hpowers (1 / (2 * (4 * (k : ℝ) ^ 2 + 1))) (by positivity) K
  refine ((h.and_eventually (eventually_power_le_inv_scale k)).and_eventually hgap).mono ?_
  rintro Δ ⟨⟨hlarge, hle⟩, hgapΔ⟩
  exact hlarge.trans_le (by simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hle hgapΔ.1)

/-- The all-powers criterion excludes the first paper's exact frozen (T). -/
theorem not_linearTimeTransposable_of_all_powers (hquant : QuantitativeTarget) {ρ : ℕ → ℝ}
    (hgap : FamilyRateGap ρ)
    (hpowers : ∀ a : ℝ, 0 < a → ∀ K : ℝ, ∃ᶠ Δ : ℕ in atTop, K < ρ Δ * degreeLogLog Δ ^ a) :
    ¬ Transpose.LinearTimeTransposable := by
  intro hlinear
  obtain ⟨M, c, hc, hgood⟩ := unbounded_success_of_linear hlinear
  exact no_transposer_of_all_powers hquant hgap hpowers M c hc hgood

end TapeStorageRates
