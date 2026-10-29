import SourceCovers.SubsetColumnMovement
import LeanMachine.FixedSubsetLimits
import LeanMachine.ExtendedTradeoff

/-! Dimension limits for actual subset-code queries. Both the raw-point
width and the repetition penalty vanish with the reciprocal dimension.
Replication and entry width may vary arbitrarily with the bin count. -/

namespace SourceCovers.SubsetMovement

open Filter LeanMachine
open scoped Topology ENNReal
noncomputable section

theorem side_inverse_limit (k : ℕ) {h : ℕ → ℕ} (hh : ∀ N, 0 < h N) :
    Tendsto (fun N => (1 : ℝ) / SubsetHelper.side N k (h N)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [eventually_ge_atTop (max k 1)] with N hN
    have hn : 0 < N := by omega
    have hF : 1 ≤ N.choose k := Nat.choose_pos (by omega)
    have hd : N ≤ SubsetHelper.side N k (h N) := by
      unfold SubsetHelper.side
      calc
        N = N * 1 * 1 := by simp
        _ ≤ N * N.choose k * h N := Nat.mul_le_mul (Nat.mul_le_mul_left N hF) (hh N)
    exact one_div_le_one_div_of_le (by exact_mod_cast hn) (by exact_mod_cast hd)

theorem capacity_ratio (k m : ℕ) {h : ℕ → ℕ} {lam tau sigma : ℝ}
    (hh : ∀ N, 0 < h N) (hsum : 0 < lam + tau + sigma) :
    Tendsto (fun N => (subsetCapacity N k m (h N) lam tau sigma : ℝ) / N)
      atTop (𝓝 (min 1 (2 * m * (lam + tau + sigma)))) := by
  have ht : Tendsto
      (fun N => (2 * (lam + tau + sigma + 1 / SubsetHelper.side N k (h N)) * N) / N)
      atTop (𝓝 (2 * (lam + tau + sigma))) := by
    have ha := ((side_inverse_limit k hh).const_add (lam + tau + sigma)).const_mul 2
    simp only [add_zero] at ha
    apply ha.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp [hn]
  simpa only [subsetCapacity, mul_assoc, mul_left_comm] using
    FixedSubsetLimits.capped_capacity_ratio m (Eventually.of_forall fun N => by positivity) ht

theorem choose_capacity_ratio (k : ℕ) {m : ℕ} {h : ℕ → ℕ} {lam tau sigma : ℝ}
    (hm : 0 < m) (hh : ∀ N, 0 < h N) (hsum : 0 < lam + tau + sigma) :
    Tendsto (fun N => ((subsetCapacity N k m (h N) lam tau sigma).choose k : ℝ) /
      N.choose k) atTop (𝓝 ((min 1 (2 * m * (lam + tau + sigma))) ^ k)) :=
  FixedSubsetLimits.choose_ratio k (lt_min (by norm_num) (by positivity))
    (capacity_ratio k m hh hsum)

theorem quarter_barrier_diverges {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) :
    Tendsto (fun lam : ℝ => lam / 4 * (1 / (5 * m * lam / 2) ^ k - 1))
      (𝓝[>] 0) atTop := by
  convert FixedSubsetLimits.inverse_power_diverges hk (a := 1 / 4)
    (c := 5 * m / 2) (by norm_num) (by positivity) using 1
  funext lam
  congr 2 <;> ring

namespace ColumnQueries

variable {k m : ℕ} [NeZero m] {h b : ℕ → ℕ} {lam tau sigma : ℝ}

/-- Dimension first: for any fixed positive discard and clock widths,
the exact finite-column bound passes to an extended lower limit. -/
theorem fixed_width_liminf (Q : ∀ N, ColumnQueries N k m (h N) (b N) lam)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N)
    (hlam : 0 < lam) (htau : 0 < tau) (hsigma : 0 < sigma) :
    ENNReal.ofReal (tau * (1 / (min 1 (2 * m * (lam + tau + sigma))) ^ k - 1)) ≤
      liminf (fun N => ENNReal.ofReal ((Q N).maxCost /
        SubsetHelper.inputBits N k (h N) (b N))) atTop := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hq := choose_capacity_ratio k hm hh (show 0 < lam + tau + sigma by positivity)
  have hp : 0 < (min 1 (2 * m * (lam + tau + sigma))) ^ k := by positivity
  have he : Tendsto (fun N => tau / (sigma * SubsetHelper.side N k (h N)))
      atTop (𝓝 0) := by
    convert (side_inverse_limit k hh).const_mul (tau / sigma) using 1 <;> simp [div_mul_eq_div_mul_one_div]
  have ht := (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).div
    (hq.add he) (by simpa using hp.ne')).const_mul tau
  simp only [add_zero] at ht
  have ha : (1 - (min 1 (2 * m * (lam + tau + sigma))) ^ k) /
      (min 1 (2 * m * (lam + tau + sigma))) ^ k =
      1 / (min 1 (2 * m * (lam + tau + sigma))) ^ k - 1 := by
    rw [sub_div, div_self hp.ne']
  rw [ha] at ht
  apply ExtendedTradeoff.ofReal_le_liminf ht
  filter_upwards [eventually_ge_atTop (max k 1)] with N hN
  exact ENNReal.ofReal_le_ofReal
    ((Q N).finite_lower (by omega) (by omega) (hh N) (hb N) hlam htau hsigma)

/-- After the dimension limit, the discard width can tend to zero.
This removes the extra interval-query loss without changing the clock. -/
theorem liminf_lower (Q : ∀ N, ColumnQueries N k m (h N) (b N) lam)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N)
    (hlam : 0 < lam) (htau : 0 < tau) :
    ENNReal.ofReal (tau * (1 / (min 1 (2 * m * (lam + tau))) ^ k - 1)) ≤
      liminf (fun N => ENNReal.ofReal ((Q N).maxCost /
        SubsetHelper.inputBits N k (h N) (b N))) atTop := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hp : 0 < (min 1 (2 * m * (lam + tau))) ^ k := by positivity
  have hs : Tendsto (fun sigma : ℝ => sigma) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hc : Tendsto (fun sigma : ℝ => (min 1 (2 * m * (lam + tau + sigma))) ^ k)
      (𝓝[>] 0) (𝓝 ((min 1 (2 * m * (lam + tau))) ^ k)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).min
        ((hs.const_add (lam + tau)).const_mul (2 * (m : ℝ)))).pow k
  apply le_of_tendsto (ENNReal.tendsto_ofReal
    (((tendsto_const_nhds.div hc hp.ne').sub tendsto_const_nhds).const_mul tau))
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  exact fixed_width_liminf Q hh hb hlam htau hsigma

/-- The sharper common centre/interval bound; the maximum-step charge is
no larger than total variation. The positive radius restriction is needed
only to remove the capacity cap and obtain a positive bound. -/
theorem quarter_liminf (Q : ∀ N, ColumnQueries N k m (h N) (b N) lam)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N)
    (hlam : 0 < lam) (hsmall : lam < 2 / (5 * m)) :
    ENNReal.ofReal (lam / 4 * (1 / (5 * m * lam / 2) ^ k - 1)) ≤
      liminf (fun N => ENNReal.ofReal ((Q N).maxCost /
        SubsetHelper.inputBits N k (h N) (b N))) atTop := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hx : 2 * m * (lam + lam / 4) < 1 := by
    have hs := (lt_div_iff₀ (by positivity : (0 : ℝ) < 5 * m)).mp hsmall
    nlinarith
  have he : 2 * (m : ℝ) * (lam + lam / 4) = 5 * m * lam / 2 := by ring
  have hx' : 5 * (m : ℝ) * lam / 2 ≤ 1 := by rw [← he]; exact hx.le
  simpa only [he, min_eq_right hx'] using
    liminf_lower Q hh hb hlam (show 0 < lam / 4 by positivity)

theorem quarter_total_liminf (Q : ∀ N, ColumnQueries N k m (h N) (b N) lam)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N)
    (hlam : 0 < lam) (hsmall : lam < 2 / (5 * m)) :
    ENNReal.ofReal (lam / 4 * (1 / (5 * m * lam / 2) ^ k - 1)) ≤
      liminf (fun N => ENNReal.ofReal ((Q N).totalCost /
        SubsetHelper.inputBits N k (h N) (b N))) atTop :=
  (quarter_liminf Q hh hb hlam hsmall).trans (liminf_le_liminf
    (Eventually.of_forall fun N => ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (Q N).maxCost_le_total (by positivity))))

/-- At every sufficiently small fixed positive radius, every admissible
family exceeds any proposed fixed variation constant in the dimension limit. -/
theorem eventually_exceeds (hk : 2 ≤ k) (C : ℝ) (hC : 0 ≤ C)
    (hh : ∀ N, 0 < h N) (hb : ∀ N, 0 < b N) :
    ∀ᶠ lam : ℝ in 𝓝[>] 0, ∀ Q : ∀ N, ColumnQueries N k m (h N) (b N) lam,
      ENNReal.ofReal C < liminf (fun N => ENNReal.ofReal ((Q N).maxCost /
        SubsetHelper.inputBits N k (h N) (b N))) atTop := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hz : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  filter_upwards [(quarter_barrier_diverges hk hm).eventually (eventually_gt_atTop C),
    self_mem_nhdsWithin, hz.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 / (5 * m)))]
    with lam hlarge hlam hsmall
  intro Q
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC).mpr hlarge).trans_le
    (quarter_liminf Q hh hb hlam hsmall)

end ColumnQueries
end
end SourceCovers.SubsetMovement
