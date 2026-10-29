import SourceCovers.CausalTapeBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

/-! Corollary 8.4: arbitrary sequences of actual native tape codes, with
dimension-independent runtime and capacity constants and arbitrary widths. -/

namespace SourceCovers.CausalGroups

open LeanMachine Transpose Transpose.Tape Transpose.Tape.Impl TransposeFollowup Finset
open Filter Asymptotics
open scoped BigOperators Classical Topology
noncomputable section

universe u

/-- A single native diagram with the full causal typing and probability law.
Only the tape count, block scale and runtime constant are fixed in a family. -/
structure CausalTapeCode (k G : ℕ) (c : ℝ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  width : ℕ
  width_pos : 0 < width
  scale_pos : 0 < G
  groups : ℕ
  partition : ColumnPartition dimension groups
  diagram : TSDiagram k
  valid : diagram.Valid (dimension * dimension * width)
  time_bound : (diagram.T : ℝ) ≤ c * (dimension * dimension * width : ℕ)
  capacity : NativeEdge diagram (nativeBlockSize G dimension width) → ℝ
  capacity_nonneg : ∀ e, 0 ≤ capacity e
  capacity_bound : ∑ e, capacity e ≤
    (4 * k * diagram.nodes (nativeBlockSize G dimension width) * nativeBlockSize G dimension width * G : ℕ)
  groupWidth : ℕ
  group_width : ∀ a, Fintype.card {j : Fin dimension // partition.group j = a} ≤ groupWidth
  domain : Set (Input dimension width)
  Helper : Type u
  helper : Input dimension width → Helper
  weight : domain → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_sum : ∑ x, weight x = 1
  typing : (nativeNetwork diagram valid
    (nativeBlockSize_bounds dimension_pos width_pos scale_pos).1
    partition capacity capacity_nonneg).CausalGroupTyping domain helper

namespace CausalTapeCode

variable {k G : ℕ} {c : ℝ} (Q : CausalTapeCode.{u} k G c)

def network := nativeNetwork Q.diagram Q.valid
  (nativeBlockSize_bounds Q.dimension_pos Q.width_pos Q.scale_pos).1
  Q.partition Q.capacity Q.capacity_nonneg

def inputLength : ℝ := (Q.dimension * Q.dimension * Q.width : ℕ)

def groupEntropy : ℝ := Q.network.conditionalGroupEntropy Q.domain Q.helper Q.weight

def inputEntropy : ℝ := entropy Q.weight / Real.log 2

def helperEntropy : ℝ := observationEntropy Q.weight (Network.helperValue Q.domain Q.helper) / Real.log 2

def deficit : ℝ := Q.inputLength - Q.inputEntropy

theorem inputLength_pos : 0 < Q.inputLength := by
  dsimp [inputLength]
  exact_mod_cast Nat.mul_pos (Nat.mul_pos Q.dimension_pos Q.dimension_pos) Q.width_pos

theorem domain_nonempty : Nonempty Q.domain := by
  cases isEmpty_or_nonempty Q.domain with
  | inl he => have h := Q.weight_sum; simp at h
  | inr he => exact he

theorem groupEntropy_nonneg : 0 ≤ Q.groupEntropy := by
  let := Q.domain_nonempty
  let : Nonempty (Network.AttainedHelper Q.domain Q.helper) :=
    Nonempty.map (Network.helperValue Q.domain Q.helper) Q.domain_nonempty
  unfold groupEntropy Network.conditionalGroupEntropy
  apply sum_nonneg
  intro a _
  exact div_nonneg (conditionalObservationEntropy_nonneg Q.weight Q.weight_nonneg _ _)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem deficit_helper_ge : Q.inputLength - Q.groupEntropy ≤ Q.deficit + Q.helperEntropy := by
  have hc := Q.network.groupTotalCorrelation_nonneg Q.domain Q.helper Q.weight Q.weight_nonneg
  dsimp [Network.groupTotalCorrelation] at hc
  dsimp [deficit, inputEntropy, helperEntropy, groupEntropy]
  rw [sub_div] at hc
  linarith

theorem groupEntropy_le_explicit (hc : 0 ≤ c) (hd : (2 * k + 3) ^ 4 ≤ Q.dimension) :
    Q.groupEntropy ≤
      2 * ((c + 1) * G) * Q.inputLength / Real.sqrt Q.dimension +
        4 * Real.log (2 * k + 3) * ((c + 1) * G) * (4 * k + 2 * Q.groupWidth) *
          Q.inputLength / Real.log Q.dimension := by
  have hr := nativeBlockSize_bounds Q.dimension_pos Q.width_pos Q.scale_pos
  exact NativeNetwork.entropy_le_explicit Q.diagram Q.valid hr.1 Q.partition Q.capacity
    Q.capacity_nonneg Q.dimension_pos Q.width_pos hc hr.2.1 hr.2.2 Q.time_bound
    Q.capacity_bound Q.groupWidth Q.group_width Q.domain Q.helper Q.typing
    Q.weight Q.weight_nonneg Q.weight_sum hd

/-- A common constant for every width, probability law, helper and group
partition. Its arguments are exactly the fixed parameters of the corollary. -/
def uniformConstant (k G : ℕ) (c : ℝ) : ℝ :=
  2 * ((c + 1) * G) + 4 * Real.log (2 * k + 3) * ((c + 1) * G) * (4 * k + 2)

theorem groupEntropy_le_uniform (hc : 0 ≤ c) (hd : (2 * k + 3) ^ 4 ≤ Q.dimension) :
    Q.groupEntropy ≤ uniformConstant k G c *
      (Q.inputLength / Real.sqrt Q.dimension +
        (1 + Q.groupWidth) * Q.inputLength / Real.log Q.dimension) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hg : (0 : ℝ) ≤ Q.groupWidth := Nat.cast_nonneg _
  have hlogA : 0 ≤ Real.log (2 * (k : ℝ) + 3) := Real.log_nonneg (by linarith)
  have hdim : (1 : ℝ) < Q.dimension := by
    exact_mod_cast (one_lt_pow₀ (by omega : 1 < 2 * k + 3)
      (by decide : (4 : ℕ) ≠ 0)).trans_le hd
  have hlog : 0 ≤ Real.log (Q.dimension : ℝ) := (Real.log_pos hdim).le
  let a : ℝ := 2 * ((c + 1) * G)
  let q : ℝ := 4 * Real.log (2 * k + 3) * ((c + 1) * G)
  let X := Q.inputLength / Real.sqrt Q.dimension
  let Y := (1 + (Q.groupWidth : ℝ)) * Q.inputLength / Real.log Q.dimension
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hX : 0 ≤ X := div_nonneg Q.inputLength_pos.le (Real.sqrt_nonneg _)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity [Q.inputLength_pos]
  have hcoeff : 4 * (k : ℝ) + 2 * Q.groupWidth ≤
      (4 * k + 2) * (1 + Q.groupWidth) := by nlinarith [mul_nonneg hk hg]
  have hsecond : q * (4 * k + 2 * Q.groupWidth) * Q.inputLength / Real.log Q.dimension ≤
      q * (4 * k + 2) * Y := by
    calc
      _ ≤ q * ((4 * k + 2) * (1 + Q.groupWidth)) * Q.inputLength / Real.log Q.dimension := by
        gcongr
        exact Q.inputLength_pos.le
      _ = _ := by dsimp [Y]; ring
  have hq' : 0 ≤ q * (4 * k + 2) := by positivity
  calc
    Q.groupEntropy ≤ a * X + q * (4 * k + 2 * Q.groupWidth) *
        Q.inputLength / Real.log Q.dimension := by
      simpa only [a, q, X, mul_div_assoc] using Q.groupEntropy_le_explicit hc hd
    _ ≤ a * X + q * (4 * k + 2) * Y := add_le_add le_rfl hsecond
    _ ≤ (a + q * (4 * k + 2)) * X + (a + q * (4 * k + 2)) * Y :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith) hX)
        (mul_le_mul_of_nonneg_right (by linarith) hY)
    _ = _ := by dsimp [uniformConstant, a, q, X, Y]; ring

section Limits

variable {ι : Type*} {l : Filter ι} (F : ι → CausalTapeCode.{u} k G c)
  (hc : 0 ≤ c) (hd : Tendsto (fun i => (F i).dimension) l atTop)

include hc hd in
/-- The big-O estimate has a constant depending only on the fixed parameters,
even along arbitrary dimension-cofinal sequences of widths and laws. -/
theorem groupEntropy_isBigO :
    (fun i => (F i).groupEntropy) =O[l]
      (fun i => (F i).inputLength / Real.sqrt (F i).dimension +
        (1 + (F i).groupWidth) * (F i).inputLength / Real.log (F i).dimension) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨uniformConstant k G c, ?_⟩
  filter_upwards [hd.eventually_ge_atTop ((2 * k + 3) ^ 4)] with i hi
  have hdim : (1 : ℝ) < (F i).dimension := by
    exact_mod_cast (one_lt_pow₀ (by omega : 1 < 2 * k + 3)
      (by decide : (4 : ℕ) ≠ 0)).trans_le hi
  have hlog : 0 ≤ Real.log ((F i).dimension : ℝ) := (Real.log_pos hdim).le
  rw [Real.norm_of_nonneg (F i).groupEntropy_nonneg,
    Real.norm_of_nonneg (by positivity [(F i).inputLength_pos])]
  exact (F i).groupEntropy_le_uniform hc hi

include hd in
/-- The entire comparison scale is sublinear once group width is sublogarithmic.
There is no regularity or upper bound on the varying entry width. -/
theorem comparison_isLittleO
    (hg : (fun i => ((F i).groupWidth : ℝ)) =o[l] (fun i => Real.log (F i).dimension)) :
    (fun i => (F i).inputLength / Real.sqrt (F i).dimension +
      (1 + (F i).groupWidth) * (F i).inputLength / Real.log (F i).dimension) =o[l]
        (fun i => (F i).inputLength) := by
  apply Asymptotics.isLittleO_of_tendsto (fun i hi => False.elim ((F i).inputLength_pos.ne' hi))
  have hdR : Tendsto (fun i => ((F i).dimension : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hroot : Tendsto (fun i => (1 : ℝ) / Real.sqrt (F i).dimension) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hdR)
  have hlog : Tendsto (fun i => (1 : ℝ) / Real.log (F i).dimension) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hdR)
  have hlim : Tendsto (fun i => (1 : ℝ) / Real.sqrt (F i).dimension +
      (1 + (F i).groupWidth) / Real.log (F i).dimension) l (𝓝 0) := by
    simpa only [add_div, zero_add, add_zero] using hroot.add (hlog.add hg.tendsto_div_nhds_zero)
  apply hlim.congr
  intro i
  symm
  rw [add_div, div_right_comm (F i).inputLength, div_self (F i).inputLength_pos.ne',
    div_right_comm ((1 + ((F i).groupWidth : ℝ)) * (F i).inputLength),
    mul_div_cancel_right₀ _ (F i).inputLength_pos.ne']

include hc hd in
theorem groupEntropy_isLittleO
    (hg : (fun i => ((F i).groupWidth : ℝ)) =o[l] (fun i => Real.log (F i).dimension)) :
    (fun i => (F i).groupEntropy) =o[l] (fun i => (F i).inputLength) :=
  (groupEntropy_isBigO F hc hd).trans_isLittleO (comparison_isLittleO F hd hg)

include hc hd in
/-- The `L-o(L)` conclusion, with an actual nonnegative error function and a
pointwise lower bound. The error is the sum of group conditional entropies. -/
theorem helper_deficit
    (hg : (fun i => ((F i).groupWidth : ℝ)) =o[l] (fun i => Real.log (F i).dimension)) :
    ∃ E : ι → ℝ, E =o[l] (fun i => (F i).inputLength) ∧
      (∀ i, 0 ≤ E i) ∧ ∀ i, (F i).inputLength - E i ≤ (F i).deficit + (F i).helperEntropy :=
  ⟨fun i => (F i).groupEntropy, groupEntropy_isLittleO F hc hd hg,
    fun i => (F i).groupEntropy_nonneg, fun i => (F i).deficit_helper_ge⟩

include hc hd in
/-- A cofinal family cannot have both a sublinear correctness deficit and a
sublinear-entropy helper under the fixed narrow causal typing. -/
theorem not_both_small [NeBot l]
    (hg : (fun i => ((F i).groupWidth : ℝ)) =o[l] (fun i => Real.log (F i).dimension)) :
    ¬ ((fun i => (F i).deficit) =o[l] (fun i => (F i).inputLength) ∧
      (fun i => (F i).helperEntropy) =o[l] (fun i => (F i).inputLength)) := by
  rintro ⟨hδ, hZ⟩
  have hsmall := (hδ.add hZ).add (groupEntropy_isLittleO F hc hd hg)
  have hge (i) : (1 : ℝ) ≤
      ((F i).deficit + (F i).helperEntropy + (F i).groupEntropy) / (F i).inputLength := by
    apply (le_div_iff₀ (F i).inputLength_pos).mpr
    have := (F i).deficit_helper_ge
    linarith
  have := ge_of_tendsto hsmall.tendsto_div_nhds_zero (Eventually.of_forall hge)
  norm_num at this

end Limits

end CausalTapeCode
end
end SourceCovers.CausalGroups
