import SourceCovers.CausalBitAllocation
import LeanMachine.FlowWalks

/-! Return walks to the original bit outputs, charged to original physical
edges. The collector and return charges retain the exact prefix sizes. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine FiniteFlow.Network Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)

def physicalFlow : FiniteFlow.Network (Fin n) Edge where
  source := G.source
  target := G.target
  capacity := G.capacity
  capacity_nonneg := G.capacity_nonneg

def memorySpine : G.physicalFlow.Spine where
  edge := G.spine
  source := G.spine_source
  target := G.spine_target

variable (a : Fin h) [Nonempty (G.GroupBit a)]

/-- One prefix charge on its actual original memory edge. -/
def copyCharge (e : Edge) : ℝ :=
  ∑ v : (G.collector a).Link, if G.collectorPhysical a (.inr v) = e then
    Fintype.card ((G.collector a).Prefix v.val) else 0

theorem copyCharge_nonneg (e : Edge) : 0 ≤ G.copyCharge a e := by
  apply sum_nonneg
  intro v _
  split_ifs <;> positivity

theorem copyCharge_on_link (v : (G.collector a).Link) :
    G.copyCharge a (G.collectorPhysical a (.inr v)) =
      Fintype.card ((G.collector a).Prefix v.val) := by
  simp [copyCharge, (G.collectorPhysical_injective a).eq_iff]

theorem copyCharge_outside (e : Edge)
    (he : e ∉ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v))) :
    G.copyCharge a e = 0 := by
  apply sum_eq_zero
  intro v _
  exact ite_eq_right (fun h => he ⟨v, h⟩)

theorem copyCharge_le (e : Edge) : G.copyCharge a e ≤ Fintype.card (G.GroupBit a) := by
  by_cases he : e ∈ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v))
  · obtain ⟨v, rfl⟩ := he
    rw [G.copyCharge_on_link]
    exact_mod_cast (G.collector a).prefix_card_le v.val
  · rw [G.copyCharge_outside a e he]
    positivity

theorem sum_copyCharge :
    ∑ e, G.copyCharge a e =
      ∑ ξ : G.GroupBit a, ((G.lastOutput a).val - (G.output ξ.val).val : ℕ) := by
  calc
    _ = ∑ v : (G.collector a).Link,
        (Fintype.card ((G.collector a).Prefix v.val) : ℝ) := by
      simp only [copyCharge]
      rw [sum_comm]
      simp
    _ = _ := by exact_mod_cast (G.collector a).sum_prefix_card

/-- The actual return traverses each edge between the bit's output and
the collector sink exactly once, and no other physical edge. -/
theorem exists_output_return (ξ : G.GroupBit a) :
    ∃ p : G.physicalFlow.bidirected.Path (G.lastOutput a) (G.output ξ.val),
      (∀ v : (G.collector a).Link,
        G.physicalFlow.walkLoad p (G.collectorPhysical a (.inr v)) =
          if G.output ξ.val ≤ v.val then 1 else 0) ∧
      (∀ e, e ∉ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v)) →
        G.physicalFlow.walkLoad p e = 0) := by
  obtain ⟨p, hp, hout⟩ := G.memorySpine.exists_return
    (G.lastOutput a) (G.output ξ.val) (G.le_lastOutput a ξ)
  dsimp only [memorySpine] at hp hout
  refine ⟨p, ?_, ?_⟩
  · intro v
    change G.physicalFlow.walkLoad p (G.spine (G.collectorSpineIndex a v)) = _
    rw [hp]
    have hv : v.val < G.lastOutput a := v.property.2
    simp only [collectorSpineIndex, Fin.le_def, Fin.lt_def] at hv ⊢
    simp [hv]
  · intro e he
    by_cases hs : e ∈ Set.range G.spine
    · obtain ⟨v, rfl⟩ := hs
      rw [hp]
      apply ite_eq_right
      rintro ⟨hlo, hhi⟩
      let u : (G.collector a).Link :=
        ⟨⟨v.val, by omega⟩, (G.firstOutput_le a ξ).trans hlo, hhi⟩
      apply he
      refine ⟨u, ?_⟩
      change G.spine (G.collectorSpineIndex a u) = G.spine v
      rfl
    · exact hout e hs

def outputReturn (ξ : G.GroupBit a) :
    G.physicalFlow.bidirected.Path (G.lastOutput a) (G.output ξ.val) :=
  Classical.choose (G.exists_output_return a ξ)

theorem outputReturn_on_link (ξ : G.GroupBit a) (v : (G.collector a).Link) :
    G.physicalFlow.walkLoad (G.outputReturn a ξ) (G.collectorPhysical a (.inr v)) =
      if G.output ξ.val ≤ v.val then 1 else 0 :=
  (Classical.choose_spec (G.exists_output_return a ξ)).1 v

theorem outputReturn_outside (ξ : G.GroupBit a) (e : Edge)
    (he : e ∉ Set.range (fun v : (G.collector a).Link => G.collectorPhysical a (.inr v))) :
    G.physicalFlow.walkLoad (G.outputReturn a ξ) e = 0 :=
  (Classical.choose_spec (G.exists_output_return a ξ)).2 e he

namespace FibreTyping

variable {G} {C : Set (Input d b)} (F : G.FibreTyping C)

/-- Copies and original edges can merge. Their traversal loads must add. -/
def collectorMap : (F.collectedFlow a).Map G.physicalFlow where
  node := id
  edge := G.collectorPhysical a
  source := G.collectorPhysical_source a
  target := G.collectorPhysical_target a

theorem collectorMap_load {s t : Fin n} (p : (F.collectedFlow a).Path s t) (e : Edge) :
    G.physicalFlow.pathFlow ((F.collectorMap a).path p) e =
      (F.collectedFlow a).pathFlow p (.inl e) +
        ∑ v : (G.collector a).Link, if G.collectorPhysical a (.inr v) = e then
          (F.collectedFlow a).pathFlow p (.inr v) else 0 := by
  rw [(F.collectorMap a).pathFlow_map_sum, Fintype.sum_sum_type]
  simp only [collectorMap, collectorPhysical, Sum.elim_inl, Sum.elim_inr, id_eq]
  congr 1
  change (∑ e' : Edge, if e' = e then (F.collectedFlow a).pathFlow p (.inl e') else 0) =
    (F.collectedFlow a).pathFlow p (.inl e)
  simp

end FibreTyping
end
end SourceCovers.CausalGroups.Network
