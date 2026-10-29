import SourceCovers.CausalCollector
import LeanMachine.FiniteFlow

/-! The supersource augmentation in Theorem Q, with its actual row
attachments. Every cut agrees with the verified collector cut formula,
so the real-capacity flow theorem supplies the exact support logarithm. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)

abbrev Attachment := {p : Fin d × Fin n // p.2 ∈ G.attached p.1}
abbrev FlowNode (d n : ℕ) := Unit ⊕ (Fin d ⊕ Fin n)

def flowSource : FlowNode d n := .inl ()
def rowNode (i : Fin d) : FlowNode d n := .inr (.inl i)
def physicalNode (v : Fin n) : FlowNode d n := .inr (.inr v)

def attachmentCutEquiv (U : Set (Fin n)) (B : Set (Fin d)) :
    {e : G.Attachment // e.val.1 ∉ B ∧ e.val.2 ∈ U} ≃
      {p : Fin d × Fin n // p.1 ∉ B ∧ p.2 ∈ U ∧ p.2 ∈ G.attached p.1} where
  toFun e := ⟨e.val.val, e.property.1, e.property.2, e.val.property⟩
  invFun p := ⟨⟨p.val, p.property.2.2⟩, p.property.1, p.property.2.1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem attachment_cut_sum (U : Set (Fin n)) (B : Set (Fin d)) (M : ℝ) :
    (∑ e : G.Attachment, if e.val.1 ∉ B ∧ e.val.2 ∈ U then M else 0) =
      M * Fintype.card {p : Fin d × Fin n //
        p.1 ∉ B ∧ p.2 ∈ U ∧ p.2 ∈ G.attached p.1} := by
  have hc := Fintype.card_congr (G.attachmentCutEquiv U B)
  calc
    _ = M * Fintype.card {e : G.Attachment // e.val.1 ∉ B ∧ e.val.2 ∈ U} := by
      simp [Fintype.card_subtype, ← sum_filter, mul_comm]
    _ = _ := by rw [hc]

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)
variable (a : Fin h) [Nonempty (G.GroupBit a)]

abbrev FlowEdge := Fin d ⊕ (G.Attachment ⊕ (Edge ⊕ (G.collector a).Link))

/-- The three arc classes are source-to-row, actual row attachments, and
the collected physical network. Absent attachments create no arcs. -/
def flowNetwork : FiniteFlow.Network (FlowNode d n) (FlowEdge (G := G) a) where
  source := Sum.elim (fun _ => flowSource)
    (Sum.elim (fun e => rowNode e.val.1)
      (fun e => physicalNode ((G.collector a).layout.source e)))
  target := Sum.elim rowNode
    (Sum.elim (fun e => physicalNode e.val.2)
      (fun e => physicalNode ((G.collector a).layout.target e)))
  capacity := Sum.elim (fun _ => (Fintype.card (G.GroupColumn a) * b : ℕ))
    (Sum.elim (fun _ => Fintype.card (G.GroupBit a)) (F.collectedCost a))
  capacity_nonneg := by
    rintro (i | (e | e))
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
    · exact F.collectedCost_nonneg a e

def flowSink : FlowNode d n := physicalNode (G.lastOutput a)

theorem source_ne_sink : (flowSource : FlowNode d n) ≠ flowSink (G := G) a := by
  simp [flowSource, flowSink, physicalNode]

def flowRank : FlowNode d n → ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun v => v.val + 2))

theorem flowNetwork_forward (e : FlowEdge (G := G) a) :
    flowRank ((F.flowNetwork a).source e) < flowRank ((F.flowNetwork a).target e) := by
  rcases e with i | (e | e)
  · simp [flowNetwork, flowRank, flowSource, rowNode]
  · simp [flowNetwork, flowRank, rowNode, physicalNode]
  · have he := (G.collector a).layout.earlier e
    change ((G.collector a).layout.source e).val + 2 <
      ((G.collector a).layout.target e).val + 2
    exact Nat.add_lt_add_right he 2

def sinkRows (S : Set (FlowNode d n)) : Set (Fin d) := {i | rowNode i ∉ S}
def sinkNodes (S : Set (FlowNode d n)) : Set (Fin n) := {v | physicalNode v ∉ S}

/-- The actual directed cut equals the previously verified expression.
The flow theorem uses the source side `S`; the collector bound uses its
sink-side physical nodes and row vertices. -/
theorem flowNetwork_cut (S : Set (FlowNode d n)) (hs : flowSource ∈ S) :
    (F.flowNetwork a).cutCapacity S =
      F.sourceCutCapacity a (Fintype.card (G.GroupBit a)) (sinkNodes S) (sinkRows S) := by
  have hrows : (∑ i : Fin d, if rowNode i ∉ S then
      ((Fintype.card (G.GroupColumn a) * b : ℕ) : ℝ) else 0) =
      (Fintype.card (sinkRows S) * Fintype.card (G.GroupColumn a) * b : ℕ) := by
    have he := sum_congr_set (sinkRows S)
      (fun i : Fin d => if rowNode i ∉ S then
        ((Fintype.card (G.GroupColumn a) * b : ℕ) : ℝ) else 0)
      (fun _ : sinkRows S => ((Fintype.card (G.GroupColumn a) * b : ℕ) : ℝ))
      (fun i hi => by simp_all [sinkRows]) (fun i hi => by simp_all [sinkRows])
    rw [he]
    simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]
    ring
  have hatt := G.attachment_cut_sum (sinkNodes S) (sinkRows S)
    (Fintype.card (G.GroupBit a))
  simp only [sinkNodes, sinkRows, Set.mem_ofPred_eq, not_not] at hatt
  have hphys : (∑ e : Edge ⊕ (G.collector a).Link,
      if physicalNode ((G.collector a).layout.source e) ∈ S ∧
        physicalNode ((G.collector a).layout.target e) ∉ S then F.collectedCost a e else 0) =
      ∑ e : {e // (G.collector a).layout.target e ∈ sinkNodes S ∧
        (G.collector a).layout.source e ∉ sinkNodes S}, F.collectedCost a e.val := by
    have he := sum_subtype (p := fun e : Edge ⊕ (G.collector a).Link =>
        (G.collector a).layout.target e ∈ sinkNodes S ∧
        (G.collector a).layout.source e ∉ sinkNodes S)
      (F := inferInstance)
      (univ.filter fun e : Edge ⊕ (G.collector a).Link =>
        (G.collector a).layout.target e ∈ sinkNodes S ∧
        (G.collector a).layout.source e ∉ sinkNodes S)
      (by simp) (F.collectedCost a)
    simpa only [sum_filter, sinkNodes, Set.mem_ofPred_eq, not_not, and_comm] using he
  unfold FiniteFlow.Network.cutCapacity FiniteFlow.Network.crossingSum
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  change ((∑ i : Fin d, if flowSource ∈ S ∧ rowNode i ∉ S then
      ((Fintype.card (G.GroupColumn a) * b : ℕ) : ℝ) else 0) +
    ((∑ e : G.Attachment, if rowNode e.val.1 ∈ S ∧ physicalNode e.val.2 ∉ S then
      (Fintype.card (G.GroupBit a) : ℝ) else 0) +
    ∑ e : Edge ⊕ (G.collector a).Link,
      if physicalNode ((G.collector a).layout.source e) ∈ S ∧
        physicalNode ((G.collector a).layout.target e) ∉ S then F.collectedCost a e else 0)) = _
  simp only [hs, true_and]
  rw [hrows, hatt, hphys]
  simp only [sourceCutCapacity, sinkRows, sinkNodes, Set.mem_ofPred_eq, not_not]
  ring

/-- The required real flow exists on the actual augmented network, with
exactly the support logarithm as its net source value. -/
theorem exists_support_flow [Nonempty C] :
    ∃ f, (F.flowNetwork a).Feasible flowSource (flowSink (G := G) a) f ∧
      (F.flowNetwork a).divergence f flowSource =
        Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) := by
  apply (F.flowNetwork a).exists_flow_of_cut_bound flowSource (flowSink (G := G) a)
    (source_ne_sink a) _ ?_ ?_
  · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast Fintype.card_pos
  · intro S hs ht
    rw [F.flowNetwork_cut a S hs]
    exact F.collected_source_cut_bound a (sinkNodes S) (sinkRows S) ht

theorem flow_source_value (f : FlowEdge (G := G) a → ℝ) :
    (F.flowNetwork a).divergence f flowSource = ∑ i : Fin d, f (.inl i) := by
  simp [FiniteFlow.Network.divergence, FiniteFlow.Network.incidence,
    flowNetwork, flowSource, rowNode, physicalNode, Fintype.sum_sum_type]

theorem flow_row_divergence (f : FlowEdge (G := G) a → ℝ) (i : Fin d) :
    (F.flowNetwork a).divergence f (rowNode i) =
      (∑ e : G.Attachment, if e.val.1 = i then f (.inr (.inl e)) else 0) - f (.inl i) := by
  simp [FiniteFlow.Network.divergence, FiniteFlow.Network.incidence,
    flowNetwork, flowSource, rowNode, physicalNode, Fintype.sum_sum_type,
    ite_mul, sum_neg_distrib, sub_eq_add_neg]
  ring

theorem row_flow_eq {f : FlowEdge (G := G) a → ℝ}
    (hf : (F.flowNetwork a).Feasible flowSource (flowSink (G := G) a) f) (i : Fin d) :
    f (.inl i) = ∑ e : G.Attachment, if e.val.1 = i then f (.inr (.inl e)) else 0 := by
  have hc := hf.2 (rowNode i) (by simp [rowNode, flowSource])
    (by simp [rowNode, flowSink, physicalNode])
  rw [F.flow_row_divergence a f i] at hc
  linarith

theorem row_flow_bounds {f : FlowEdge (G := G) a → ℝ}
    (hf : (F.flowNetwork a).Feasible flowSource (flowSink (G := G) a) f) (i : Fin d) :
    0 ≤ f (.inl i) ∧ f (.inl i) ≤ (Fintype.card (G.GroupColumn a) * b : ℕ) :=
  ⟨hf.1.1 (.inl i), hf.1.2 (.inl i)⟩

/-- With no actual attachment, row conservation forces zero source mass. -/
theorem unattached_row_zero {f : FlowEdge (G := G) a → ℝ}
    (hf : (F.flowNetwork a).Feasible flowSource (flowSink (G := G) a) f)
    (i : Fin d) (hi : G.attached i = ∅) : f (.inl i) = 0 := by
  rw [F.row_flow_eq a hf i]
  apply sum_eq_zero
  intro e _
  split_ifs with he
  · exfalso
    have hm := e.property
    simp [he, hi] at hm
  · rfl

end FibreTyping
end
end SourceCovers.CausalGroups.Network
