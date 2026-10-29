import SourceCovers.CausalPaths
import LeanMachine.FlowPathMap

/-! Removing the two artificial initial arcs from the actual augmentation,
while retaining the row, its attachment and every physical traversal. -/

namespace SourceCovers.CausalGroups.Network.FibreTyping

open LeanMachine FiniteFlow.Network Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge]
variable {G : Network d b h n Edge} {C : Set (Input d b)} (F : G.FibreTyping C)
variable (a : Fin h) [Nonempty (G.GroupBit a)]

def collectedFlow : FiniteFlow.Network (Fin n) (Edge ⊕ (G.collector a).Link) where
  source := (G.collector a).layout.source
  target := (G.collector a).layout.target
  capacity := F.collectedCost a
  capacity_nonneg := F.collectedCost_nonneg a

def physicalMap : (F.collectedFlow a).Map (F.flowNetwork a) where
  node := physicalNode
  edge := fun e => .inr (.inr e)
  source := fun _ => rfl
  target := fun _ => rfl

theorem lift_physical {s t : Fin n}
    (p : (F.flowNetwork a).Path (physicalNode s) (physicalNode t)) :
    ∃ q : (F.collectedFlow a).Path s t, (F.physicalMap a).path q = p := by
  apply (F.physicalMap a).lift_path
  · intro u v he
    simpa [physicalMap, physicalNode] using he
  · intro u e he
    rcases e with i | (e | e)
    · simp [flowNetwork, flowSource, physicalMap, physicalNode] at he
    · simp [flowNetwork, rowNode, physicalMap, physicalNode] at he
    · refine ⟨e, ?_, rfl⟩
      simpa [flowNetwork, physicalMap, physicalNode, collectedFlow] using he

def sourceStep (i : Fin d) : (F.flowNetwork a).Path flowSource (rowNode i) :=
  @Quiver.Hom.toPath _ (F.flowNetwork a).quiver _ _ ⟨.inl i, rfl, rfl⟩

def attachmentStep (e : G.Attachment) :
    (F.flowNetwork a).Path (rowNode e.val.1) (physicalNode e.val.2) :=
  @Quiver.Hom.toPath _ (F.flowNetwork a).quiver _ _ ⟨.inr (.inl e), rfl, rfl⟩

theorem split_source {v : Fin n}
    (p : (F.flowNetwork a).Path flowSource (physicalNode v)) :
    ∃ i : Fin d, ∃ q : (F.flowNetwork a).Path (rowNode i) (physicalNode v),
      p = pathComp (F.sourceStep a i) q := by
  let := (F.flowNetwork a).quiver
  have hn : p.length ≠ 0 := by
    intro hz
    have he := p.eq_of_length_zero hz
    simp [flowSource, physicalNode] at he
  obtain ⟨u, e, q, hp, _⟩ := p.length_ne_zero_iff_eq_comp.mp hn
  rcases e with ⟨e, hs, ht⟩
  rcases e with i | (e | e)
  · change rowNode i = u at ht
    subst u
    exact ⟨i, q, hp⟩
  · simp [flowNetwork, rowNode, flowSource] at hs
  · simp [flowNetwork, physicalNode, flowSource] at hs

theorem split_row {i : Fin d} {v : Fin n}
    (p : (F.flowNetwork a).Path (rowNode i) (physicalNode v)) :
    ∃ u : Fin n, ∃ hu : u ∈ G.attached i,
      ∃ q : (F.flowNetwork a).Path (physicalNode u) (physicalNode v),
        p = pathComp (F.attachmentStep a ⟨(i, u), hu⟩) q := by
  let := (F.flowNetwork a).quiver
  have hn : p.length ≠ 0 := by
    intro hz
    have he := p.eq_of_length_zero hz
    simp [rowNode, physicalNode] at he
  obtain ⟨w, e, q, hp, _⟩ := p.length_ne_zero_iff_eq_comp.mp hn
  rcases e with ⟨e, hs, ht⟩
  rcases e with j | (e | e)
  · simp [flowNetwork, rowNode, flowSource] at hs
  · rcases e with ⟨⟨j, u⟩, hu⟩
    have hji : j = i := by simpa [flowNetwork, rowNode] using hs
    subst j
    change physicalNode u = w at ht
    subst w
    exact ⟨u, hu, q, hp⟩
  · simp [flowNetwork, physicalNode, rowNode] at hs

/-- A physical path starts at one actual row attachment and ends at the
collector sink. It may be empty when these endpoints coincide. -/
structure AttachedPath where
  attachment : G.Attachment
  path : (F.collectedFlow a).Path attachment.val.2 (G.lastOutput a)

namespace AttachedPath

variable {F a}

def augment (q : F.AttachedPath a) :
    (F.flowNetwork a).Path flowSource (flowSink (G := G) a) :=
  pathComp (F.sourceStep a q.attachment.val.1)
    (pathComp (F.attachmentStep a q.attachment) ((F.physicalMap a).path q.path))

theorem augment_source_load (q : F.AttachedPath a) (i : Fin d) :
    (F.flowNetwork a).pathFlow q.augment (.inl i) =
      if q.attachment.val.1 = i then 1 else 0 := by
  have hphys := (F.physicalMap a).pathFlow_map_outside q.path (.inl i)
    (by simp [physicalMap])
  unfold augment
  erw [pathFlow_comp, pathFlow_comp]
  simp only [Pi.add_apply]
  erw [hphys]
  simp [sourceStep, attachmentStep, FiniteFlow.Network.pathFlow,
    Quiver.Hom.toPath, FiniteFlow.Network.unit, eq_comm]

theorem augment_physical_load (q : F.AttachedPath a)
    (e : Edge ⊕ (G.collector a).Link) :
    (F.flowNetwork a).pathFlow q.augment (.inr (.inr e)) =
      (F.collectedFlow a).pathFlow q.path e := by
  have hinj : Function.Injective (F.physicalMap a).edge := by
    intro u v he
    simpa [physicalMap] using he
  have he := (F.physicalMap a).pathFlow_map_of_injective hinj q.path e
  unfold augment
  erw [pathFlow_comp, pathFlow_comp]
  simp only [Pi.add_apply]
  change _ + (_ + (F.flowNetwork a).pathFlow ((F.physicalMap a).path q.path)
    ((F.physicalMap a).edge e)) = _
  rw [he]
  simp [sourceStep, attachmentStep, FiniteFlow.Network.pathFlow,
    Quiver.Hom.toPath, FiniteFlow.Network.unit]

end AttachedPath

theorem exists_attachedPath
    (p : (F.flowNetwork a).Path flowSource (flowSink (G := G) a)) :
    ∃ q : F.AttachedPath a, q.augment = p := by
  obtain ⟨i, p₁, hp⟩ := F.split_source a p
  obtain ⟨u, hu, p₂, hq⟩ := F.split_row a p₁
  obtain ⟨p₃, hr⟩ := F.lift_physical a p₂
  refine ⟨⟨⟨(i, u), hu⟩, p₃⟩, ?_⟩
  simp only [AttachedPath.augment]
  exact (congrArg (pathComp (F.sourceStep a i))
    ((congrArg (pathComp (F.attachmentStep a ⟨(i, u), hu⟩)) hr).trans hq.symm)).trans hp.symm

def stripPath (p : (F.flowNetwork a).Path flowSource (flowSink (G := G) a)) :
    F.AttachedPath a := Classical.choose (F.exists_attachedPath a p)

@[simp] theorem stripPath_augment
    (p : (F.flowNetwork a).Path flowSource (flowSink (G := G) a)) :
    (F.stripPath a p).augment = p := Classical.choose_spec (F.exists_attachedPath a p)

def augmentPacking (Q : List (ℝ × F.AttachedPath a)) :
    List (ℝ × (F.flowNetwork a).Path flowSource (flowSink (G := G) a)) :=
  Q.map fun q => (q.1, q.2.augment)

def stripPacking
    (P : List (ℝ × (F.flowNetwork a).Path flowSource (flowSink (G := G) a))) :
    List (ℝ × F.AttachedPath a) := P.map fun q => (q.1, F.stripPath a q.2)

@[simp] theorem augment_stripPacking
    (P : List (ℝ × (F.flowNetwork a).Path flowSource (flowSink (G := G) a))) :
    F.augmentPacking a (F.stripPacking a P) = P := by
  simp [augmentPacking, stripPacking, List.map_map, Function.comp_def]

def attachedMass (Q : List (ℝ × F.AttachedPath a)) : ℝ := (Q.map Prod.fst).sum

def attachedLoad (Q : List (ℝ × F.AttachedPath a))
    (e : Edge ⊕ (G.collector a).Link) : ℝ :=
  (Q.map fun q => q.1 * (F.collectedFlow a).pathFlow q.2.path e).sum

def attachedRowMass (Q : List (ℝ × F.AttachedPath a)) (i : Fin d) : ℝ :=
  (Q.map fun q => if q.2.attachment.val.1 = i then q.1 else 0).sum

theorem augmentPacking_mass (Q : List (ℝ × F.AttachedPath a)) :
    (F.flowNetwork a).packingMass (F.augmentPacking a Q) = F.attachedMass a Q := by
  simp [packingMass, augmentPacking, attachedMass, List.map_map, Function.comp_def]

theorem augmentPacking_physical_load (Q : List (ℝ × F.AttachedPath a))
    (e : Edge ⊕ (G.collector a).Link) :
    (F.flowNetwork a).packingLoad (F.augmentPacking a Q) (.inr (.inr e)) =
      F.attachedLoad a Q e := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    change q.1 * (F.flowNetwork a).pathFlow q.2.augment (.inr (.inr e)) +
      (F.flowNetwork a).packingLoad (F.augmentPacking a Q) (.inr (.inr e)) = _
    rw [q.2.augment_physical_load, ih]
    rfl

theorem augmentPacking_row_load (Q : List (ℝ × F.AttachedPath a)) (i : Fin d) :
    (F.flowNetwork a).packingLoad (F.augmentPacking a Q) (.inl i) =
      F.attachedRowMass a Q i := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    change q.1 * (F.flowNetwork a).pathFlow q.2.augment (.inl i) +
      (F.flowNetwork a).packingLoad (F.augmentPacking a Q) (.inl i) = _
    rw [q.2.augment_source_load, ih]
    simp [attachedRowMass, mul_ite]

theorem attachedRowMass_sum (Q : List (ℝ × F.AttachedPath a)) :
    (∑ i : Fin d, F.attachedRowMass a Q i) = F.attachedMass a Q := by
  simpa only [F.augmentPacking_row_load, F.augmentPacking_mass] using
    F.packing_row_mass a (F.augmentPacking a Q)

theorem exists_attached_packing [Nonempty C] :
    ∃ Q : List (ℝ × F.AttachedPath a),
      (∀ q ∈ Q, 0 < q.1) ∧
      F.attachedMass a Q =
        Real.logb 2 (Fintype.card (Set.range (fun x : C => G.projection a x.val))) ∧
      (∀ e, F.attachedLoad a Q e ≤ F.collectedCost a e) ∧
      (∀ i : Fin d, 0 ≤ F.attachedRowMass a Q i ∧
        F.attachedRowMass a Q i ≤ (Fintype.card (G.GroupColumn a) * b : ℕ) ∧
        (G.attached i = ∅ → F.attachedRowMass a Q i = 0)) ∧
      Q.length ≤ Fintype.card (FlowEdge (G := G) a) := by
  obtain ⟨P, hP, hmass, hf, hlen, hrow⟩ := F.exists_support_path_packing a
  let Q := F.stripPacking a P
  have haug : F.augmentPacking a Q = P := F.augment_stripPacking a P
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hP p hp
  · rw [← F.augmentPacking_mass a Q, haug]
    exact hmass
  · intro e
    rw [← F.augmentPacking_physical_load a Q e, haug]
    exact hf.1.2 (.inr (.inr e))
  · intro i
    rw [← F.augmentPacking_row_load a Q i, haug]
    exact hrow i
  · simpa [Q, stripPacking] using hlen

end
end SourceCovers.CausalGroups.Network.FibreTyping
