import SourceCovers.CausalGroups
import LeanMachine.CausalCollector

/-! The collector in Theorem Q on the actual column groups and memory
spine. This is the support-to-cut step, not yet a flow or routing theorem. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)

theorem groupBit_nonempty (hb : 0 < b) (a : Fin h) : Nonempty (G.GroupBit a) := by
  obtain ⟨j, hj⟩ := G.partition.onto a
  exact ⟨⟨(j, j, ⟨0, hb⟩), hj⟩⟩

theorem card_groupBit (a : Fin h) :
    Fintype.card (G.GroupBit a) = d * Fintype.card (G.GroupColumn a) * b := by
  simpa [rowData] using G.card_rowData a Set.univ

/-- This support bound needs no causal code, only a nonempty input set. -/
theorem projection_log_support_le (a : Fin h) {C : Set (Input d b)} [Nonempty C] :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ≤
      Fintype.card (G.GroupBit a) := by
  have hp : (0 : ℝ) < Fintype.card (Set.range (fun x : C => G.projection a x.val)) := by
    exact_mod_cast Fintype.card_pos
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).mpr
  rw [Real.rpow_natCast]
  have hc : Fintype.card (Set.range (fun x : C => G.projection a x.val)) ≤
      Fintype.card (G.GroupBit a → Bool) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Fintype.card_fun, Fintype.card_bool] at hc
  exact_mod_cast hc

def firstOutput (a : Fin h) [Nonempty (G.GroupBit a)] : Fin n :=
  univ.inf' univ_nonempty (fun i : G.GroupBit a => G.output i.val)

def lastOutput (a : Fin h) [Nonempty (G.GroupBit a)] : Fin n :=
  univ.sup' univ_nonempty (fun i : G.GroupBit a => G.output i.val)

theorem firstOutput_le (a : Fin h) [Nonempty (G.GroupBit a)] (i : G.GroupBit a) :
    G.firstOutput a ≤ G.output i.val := inf'_le _ (mem_univ i)

theorem le_lastOutput (a : Fin h) [Nonempty (G.GroupBit a)] (i : G.GroupBit a) :
    G.output i.val ≤ G.lastOutput a :=
  le_sup' (fun i : G.GroupBit a => G.output i.val) (mem_univ i)

def collector (a : Fin h) [Nonempty (G.GroupBit a)] : CausalFields.Collector (G.layout a) where
  first := G.firstOutput a
  last := G.lastOutput a
  ordered := by
    let i : G.GroupBit a := Classical.choice inferInstance
    exact (G.firstOutput_le a i).trans (G.le_lastOutput a i)
  output_ge := G.firstOutput_le a
  output_le := G.le_lastOutput a
  forward := G.earlier

/-- Consecutive groups may share endpoints but their collector intervals
have disjoint edges. The order is the original transposed output order. -/
theorem lastOutput_le_firstOutput {a a' : Fin h}
    [Nonempty (G.GroupBit a)] [Nonempty (G.GroupBit a')] (ha : a < a') :
    G.lastOutput a ≤ G.firstOutput a' := by
  apply sup'_le
  intro i _
  apply le_inf'
  intro j _
  exact G.group_output_order ha i j

theorem collector_intervals_disjoint {a a' : Fin h}
    [Nonempty (G.GroupBit a)] [Nonempty (G.GroupBit a')] (ha : a < a') :
    Disjoint (Set.Ico (G.firstOutput a) (G.lastOutput a))
      (Set.Ico (G.firstOutput a') (G.lastOutput a')) := by
  apply Set.disjoint_left.mpr
  intro v hv hv'
  exact (not_lt_of_ge ((G.lastOutput_le_firstOutput ha).trans hv'.1)) hv.2

def collectorSpineIndex (a : Fin h) [Nonempty (G.GroupBit a)]
    (v : (G.collector a).Link) : Fin (n - 1) := ⟨v.val.val, by
  have hv : v.val.val < (G.lastOutput a).val := v.property.2
  have hn := (G.lastOutput a).isLt
  omega⟩

/-- Collector copies are parallel to actual memory edges, so subsequently
forgetting the copy never changes a walk's physical endpoints. -/
def collectorPhysical (a : Fin h) [Nonempty (G.GroupBit a)] :
    Edge ⊕ (G.collector a).Link → Edge :=
  Sum.elim id (fun v => G.spine (G.collectorSpineIndex a v))

theorem collectorPhysical_source (a : Fin h) [Nonempty (G.GroupBit a)]
    (e : Edge ⊕ (G.collector a).Link) :
    G.source (G.collectorPhysical a e) = (G.collector a).layout.source e := by
  rcases e with e | v
  · rfl
  · apply Fin.ext
    exact G.spine_source (G.collectorSpineIndex a v)

theorem collectorPhysical_target (a : Fin h) [Nonempty (G.GroupBit a)]
    (e : Edge ⊕ (G.collector a).Link) :
    G.target (G.collectorPhysical a e) = (G.collector a).layout.target e := by
  rcases e with e | v
  · rfl
  · apply Fin.ext
    exact G.spine_target (G.collectorSpineIndex a v)

theorem collectorPhysical_injective (a : Fin h) [Nonempty (G.GroupBit a)] :
    Function.Injective (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v)) := by
  intro v w hvw
  apply Subtype.ext
  simpa only [G.collectorPhysical_source, CausalFields.Collector.layout, Sum.elim_inr]
    using congrArg G.source hvw

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)
variable (a : Fin h) [Nonempty (G.GroupBit a)]

/-- The complete local collector on the same correctness set. -/
def collectedEvaluation := (G.collector a).evaluation (F.evaluation a)

/-- Exact bit capacity after adding only already-output coordinates. -/
def collectedCost := (G.collector a).cost (fun e => F.allocation e a)

theorem collectedCost_nonneg (e : Edge ⊕ (G.collector a).Link) :
    0 ≤ F.collectedCost a e := (G.collector a).cost_nonneg _ (fun e => F.allocation_nonneg e a) e

theorem collectedCost_sum :
    ∑ e, F.collectedCost a e = (∑ e, F.allocation e a) +
      ∑ i : G.GroupBit a, ((G.lastOutput a).val - (G.output i.val).val : ℕ) :=
  (G.collector a).sum_cost _

/-- A cut containing the last output now suffices; the other original
outputs may lie outside. The collector capacity is explicitly charged. -/
theorem collected_cut_support_bound [Nonempty C] (U : Set (Fin n)) (B : Set (Fin d))
    (hrows : ∀ i v, v ∈ U → v ∈ G.attached i → i ∈ B)
    (hsink : G.lastOutput a ∈ U) :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ≤
      (Fintype.card B * Fintype.card (G.GroupColumn a) * b : ℕ) +
        ∑ e : {e // (G.collector a).layout.target e ∈ U ∧
          (G.collector a).layout.source e ∉ U}, F.collectedCost a e.val := by
  let : ∀ e, Fintype (F.Alphabet e a) := fun e => F.finite_alphabet e a
  have he := (G.collector a).log_support_le_collected_cut (F.evaluation a)
    (fun e => F.allocation e a) (fun e => F.alphabet_bound e a) U (G.rowData a B)
    (fun v hv i hi => hrows i.val.1 v hv hi) hsink
  simp only [G.card_rowData, ← Nat.card_eq_fintype_card] at he ⊢
  exact he

/-- Capacity of a supersource/collector-sink cut. `B` consists of its
sink-side row vertices, and `U` of its sink-side physical vertices.
The three terms count source-to-row arcs, row attachments, and physical
or collector arcs, respectively. -/
def sourceCutCapacity (attachmentCapacity : ℝ) (U : Set (Fin n)) (B : Set (Fin d)) : ℝ :=
  (Fintype.card B * Fintype.card (G.GroupColumn a) * b : ℕ) +
    attachmentCapacity * Fintype.card {p : Fin d × Fin n //
      p.1 ∉ B ∧ p.2 ∈ U ∧ p.2 ∈ G.attached p.1} +
    ∑ e : {e // (G.collector a).layout.target e ∈ U ∧
      (G.collector a).layout.source e ∉ U}, F.collectedCost a e.val

/-- Every source/sink cut pays for the projected support. The artificial
attachment capacity need only dominate the support logarithm, not the
whole input length plus one. -/
theorem log_support_le_sourceCutCapacity [Nonempty C] (M : ℝ) (hM : 0 ≤ M)
    (hbig : Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ≤ M)
    (U : Set (Fin n)) (B : Set (Fin d)) (hsink : G.lastOutput a ∈ U) :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ≤
      F.sourceCutCapacity a M U B := by
  have hphys : 0 ≤ ∑ e : {e // (G.collector a).layout.target e ∈ U ∧
      (G.collector a).layout.source e ∉ U}, F.collectedCost a e.val :=
    sum_nonneg fun e _ => F.collectedCost_nonneg a e.val
  by_cases hrows : ∀ i v, v ∈ U → v ∈ G.attached i → i ∈ B
  · have he := F.collected_cut_support_bound a U B hrows hsink
    have ha : 0 ≤ M * Fintype.card {p : Fin d × Fin n //
        p.1 ∉ B ∧ p.2 ∈ U ∧ p.2 ∈ G.attached p.1} := mul_nonneg hM (Nat.cast_nonneg _)
    dsimp [sourceCutCapacity]
    linarith
  · push Not at hrows
    obtain ⟨i, v, hv, hi, hb⟩ := hrows
    let : Nonempty {p : Fin d × Fin n //
        p.1 ∉ B ∧ p.2 ∈ U ∧ p.2 ∈ G.attached p.1} := ⟨⟨(i, v), hb, hv, hi⟩⟩
    have ha : (1 : ℝ) ≤ Fintype.card {p : Fin d × Fin n //
        p.1 ∉ B ∧ p.2 ∈ U ∧ p.2 ∈ G.attached p.1} := by
      exact_mod_cast Fintype.card_pos
    have hm := mul_le_mul_of_nonneg_left ha hM
    have hb0 : (0 : ℝ) ≤ (Fintype.card B * Fintype.card (G.GroupColumn a) * b : ℕ) :=
      Nat.cast_nonneg _
    dsimp [sourceCutCapacity]
    linarith

theorem collected_source_cut_bound [Nonempty C]
    (U : Set (Fin n)) (B : Set (Fin d)) (hsink : G.lastOutput a ∈ U) :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ≤
      F.sourceCutCapacity a (Fintype.card (G.GroupBit a)) U B :=
  F.log_support_le_sourceCutCapacity a _ (Nat.cast_nonneg _)
    (G.projection_log_support_le a) U B hsink

end FibreTyping
end
end SourceCovers.CausalGroups.Network
