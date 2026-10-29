import SourceCovers.CausalFlow
import LeanMachine.FlowPaths

/-! Actual finite weighted paths in the causal-group augmentation. The
packing preserves the support logarithm and all physical and row caps.
Removing artificial arcs and allocating mass to bits are separate steps. -/

namespace SourceCovers.CausalGroups.Network.FibreTyping

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge]
variable {G : Network d b h n Edge} {C : Set (Input d b)} (F : G.FibreTyping C)
variable (a : Fin h) [Nonempty (G.GroupBit a)]

/-- Weighted path mass is distributed among the actual source-to-row arcs. -/
theorem packing_row_mass
    (P : List (ℝ × (F.flowNetwork a).Path flowSource (flowSink (G := G) a))) :
    (∑ i : Fin d, (F.flowNetwork a).packingLoad P (.inl i)) =
      (F.flowNetwork a).packingMass P := by
  rw [← F.flow_source_value a, (F.flowNetwork a).packingLoad_divergence]
  simp [source_ne_sink a]

/-- Each attained group fibre admits a finite family of actual directed
paths carrying its exact support logarithm. The path loads themselves are
feasible, and their row supplies satisfy the original caps, including zero
supply from unattached rows. No path-existence assumption is introduced. -/
theorem exists_support_path_packing [Nonempty C] :
    ∃ P : List (ℝ × (F.flowNetwork a).Path flowSource (flowSink (G := G) a)),
      (∀ q ∈ P, 0 < q.1) ∧
      (F.flowNetwork a).packingMass P =
        Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ∧
      (F.flowNetwork a).Feasible flowSource (flowSink (G := G) a)
        ((F.flowNetwork a).packingLoad P) ∧
      P.length ≤ Fintype.card (FlowEdge (G := G) a) ∧
      ∀ i : Fin d,
        0 ≤ (F.flowNetwork a).packingLoad P (.inl i) ∧
        (F.flowNetwork a).packingLoad P (.inl i) ≤
          (Fintype.card (G.GroupColumn a) * b : ℕ) ∧
        (G.attached i = ∅ → (F.flowNetwork a).packingLoad P (.inl i) = 0) := by
  obtain ⟨f, hf, hvalue⟩ := F.exists_support_flow a
  have hR : 0 ≤ (F.flowNetwork a).divergence f flowSource := by
    rw [F.flow_source_value a]
    exact sum_nonneg (fun i _ => hf.1.1 (.inl i))
  obtain ⟨P, hP, hmass, hload, hlen⟩ :=
    (F.flowNetwork a).exists_path_packing (source_ne_sink a) hf hR
  have hpf := (F.flowNetwork a).packing_feasible P (fun q hq => (hP q hq).le)
    (fun e => (hload e).trans (hf.1.2 e))
  refine ⟨P, hP, hmass.trans hvalue, hpf, ?_, fun i => ?_⟩
  · exact hlen.trans (card_filter_le _ _)
  · exact ⟨(F.row_flow_bounds a hpf i).1, (F.row_flow_bounds a hpf i).2,
      F.unattached_row_zero a hpf i⟩

end
end SourceCovers.CausalGroups.Network.FibreTyping
