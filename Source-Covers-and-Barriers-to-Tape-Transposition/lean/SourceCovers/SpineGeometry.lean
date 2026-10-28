import SourceCovers.ProtectedPhases
import LeanMachine.IntervalComponents

/-!
# Spine and leaf packing for a periodically cut Q2 core

Keep all original nonleaves on the spine. In a two-vertex component, its
color-zero endpoint joins the spine. Original isolated vertices may remain
leaves. The remaining leaves have disjoint spans, while a surviving spine
component has a common set of `M - 1` labels, injective on that component.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
variable {K : Finset (ActualFamily xs T)}

def packingSpine (hc : HasSpanColoring K 2) (q : CoreFamily K) : Prop :=
  (coreModel K).Nonleaf q ∨
    (coreColor hc q = 0 ∧ ∃ b, (coreModel K).graph.Adj q b ∧ ¬ (coreModel K).Nonleaf b)

theorem packingSpine_of_nonleaf (hc : HasSpanColoring K 2) {q : CoreFamily K}
    (hq : (coreModel K).Nonleaf q) : packingSpine hc q := Or.inl hq

theorem packing_leaves_not_adj (hc : HasSpanColoring K 2) {a b : CoreFamily K}
    (ha : ¬ packingSpine hc a) (hb : ¬ packingSpine hc b) :
    ¬ (coreModel K).graph.Adj a b := by
  intro hab
  have hna : ¬ (coreModel K).Nonleaf a := fun h => ha (.inl h)
  have hnb : ¬ (coreModel K).Nonleaf b := fun h => hb (.inl h)
  have hca : coreColor hc a ≠ 0 := fun h => ha (.inr ⟨h, b, hab, hnb⟩)
  have hcb : coreColor hc b ≠ 0 := fun h => hb (.inr ⟨h, a, hab.symm, hna⟩)
  have := coreColor_lt hc a
  have := coreColor_lt hc b
  have := coreColor_ne_of_adj hc hab
  omega

/-- An edge between packing spines joins two original nonleaves. The extra
spine vertices selected from two-vertex components are isolated in the spine. -/
theorem packing_spine_adj_nonleaf (hc : HasSpanColoring K 2) {a b : CoreFamily K}
    (ha : packingSpine hc a) (hb : packingSpine hc b)
    (hab : (coreModel K).graph.Adj a b) :
    (coreModel K).Nonleaf a ∧ (coreModel K).Nonleaf b := by
  have one {a b : CoreFamily K} (ha : packingSpine hc a) (hb : packingSpine hc b)
      (hab : (coreModel K).graph.Adj a b) : (coreModel K).Nonleaf a := by
    by_contra hna
    obtain ⟨hca, c, hac, hnc⟩ := ha.resolve_left hna
    have hbc : b = c := by
      by_contra hbc
      exact hna ⟨b, c, hab, hac, hbc⟩
    have hnb : ¬ (coreModel K).Nonleaf b := hbc ▸ hnc
    have hcb := (hb.resolve_left hnb).1
    exact coreColor_ne_of_adj hc hab (hca.trans hcb.symm)
  exact ⟨one ha hb hab, one hb ha hab.symm⟩

def packingLeaves (hc : HasSpanColoring K 2) (M ρ : ℕ) : Finset (CoreFamily K) :=
  (phaseSurvivors K M ρ).filter (fun q => ¬ packingSpine hc q)

theorem packing_leaves_separated (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    Patch.Separated (packingLeaves hc M ρ) (fun q => q.val.shadowPatch) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro e hea heb
  have hea' := mem_Ico.mp hea
  have heb' := mem_Ico.mp heb
  change a.val.start ≤ e ∧ e < a.val.stop at hea'
  change b.val.start ≤ e ∧ e < b.val.stop at heb'
  apply packing_leaves_not_adj hc (mem_filter.mp ha).2 (mem_filter.mp hb).2
  exact ⟨hab, by change a.val.start < b.val.stop; omega,
    by change b.val.start < a.val.stop; omega⟩

abbrev SurvivingSpine (hc : HasSpanColoring K 2) (M ρ : ℕ) :=
  {q : CoreFamily K // q ∈ phaseSurvivors K M ρ ∧ packingSpine hc q}

def spineModel (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    ThinIntervals.Model (SurvivingSpine hc M ρ) where
  left := fun q => q.val.val.start
  right := fun q => q.val.val.stop
  nonempty := fun q => (coreModel K).nonempty q.val

theorem spine_adj_iff (hc : HasSpanColoring K 2) (M ρ : ℕ)
    {a b : SurvivingSpine hc M ρ} :
    (spineModel hc M ρ).graph.Adj a b ↔ (coreModel K).graph.Adj a.val b.val := by
  change (a ≠ b ∧ _ ∧ _) ↔ (a.val ≠ b.val ∧ _ ∧ _)
  exact ⟨fun h => ⟨fun he => h.1 (Subtype.ext he), h.2⟩,
    fun h => ⟨fun he => h.1 (congrArg Subtype.val he), h.2⟩⟩

def spineHom (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    (spineModel hc M ρ).graph →g (coreModel K).graph where
  toFun := Subtype.val
  map_rel' := fun h => (spine_adj_iff hc M ρ).mp h

theorem spine_thin (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    (spineModel hc M ρ).Thin := by
  intro a b c hab hbc hac
  exact core_thin hc ((spine_adj_iff hc M ρ).mp hab)
    ((spine_adj_iff hc M ρ).mp hbc) ((spine_adj_iff hc M ρ).mp hac)

theorem spine_adj_nonleaf (hc : HasSpanColoring K 2) {M ρ : ℕ}
    {a b : SurvivingSpine hc M ρ} (hab : (spineModel hc M ρ).graph.Adj a b) :
    (coreModel K).Nonleaf a.val ∧ (coreModel K).Nonleaf b.val :=
  packing_spine_adj_nonleaf hc a.property.2 b.property.2 ((spine_adj_iff hc M ρ).mp hab)

theorem spine_reachable_nonleaf (hc : HasSpanColoring K 2) {M ρ : ℕ}
    {a b : SurvivingSpine hc M ρ} (hab : (spineModel hc M ρ).graph.Reachable a b)
    (hne : a ≠ b) : (coreModel K).Nonleaf a.val := by
  obtain ⟨p⟩ := hab
  cases p with
  | nil => exact (hne rfl).elim
  | cons h p => exact (spine_adj_nonleaf hc h).1

abbrev SpineLabel (M ρ : ℕ) := {i : Fin M // i.val ≠ ρ}

theorem spineLabel_card {M ρ : ℕ} (hρ : ρ < M) :
    Fintype.card (SpineLabel M ρ) = M - 1 := by
  calc
    _ = Fintype.card {i : Fin M // i ≠ ⟨ρ, hρ⟩} :=
      Fintype.card_congr (Equiv.subtypeEquivProp (by funext i; simp only [ne_eq, Fin.ext_iff]))
    _ = M - 1 := by simp

def spareSpineLabel {M ρ : ℕ} (hM : 2 ≤ M) : SpineLabel M ρ :=
  if hρ : ρ = 0 then ⟨⟨1, by omega⟩, by change 1 ≠ ρ; omega⟩
  else ⟨⟨0, by omega⟩, by change 0 ≠ ρ; omega⟩

theorem spine_phase_ne (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (q : SurvivingSpine hc M ρ) (hq : (coreModel K).Nonleaf q.val) :
    (coreModel K).spineRank q.val % M ≠ ρ :=
  ((mem_filter.mp q.property.1).2).resolve_left
    (not_not.mpr (mem_filter.mpr ⟨mem_univ _, hq⟩))

def spineLabel (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M)
    (q : SurvivingSpine hc M ρ) : SpineLabel M ρ :=
  if hq : (coreModel K).Nonleaf q.val then
    ⟨⟨(coreModel K).spineRank q.val % M, Nat.mod_lt _ (by omega)⟩, spine_phase_ne hc q hq⟩
  else spareSpineLabel hM

theorem spineLabel_val (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M)
    {q : SurvivingSpine hc M ρ} (hq : (coreModel K).Nonleaf q.val) :
    (spineLabel hc hM q).val.val = (coreModel K).spineRank q.val % M := by
  simp only [spineLabel, dite_eq_left hq]

/-- The same `M - 1` labels can be reused in every surviving spine component. -/
theorem spineLabel_injective_on_component (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) {a b : SurvivingSpine hc M ρ}
    (hab : (spineModel hc M ρ).graph.Reachable a b)
    (he : spineLabel hc hM a = spineLabel hc hM b) : a = b := by
  by_contra hne
  have ha := spine_reachable_nonleaf hc hab hne
  have hb := spine_reachable_nonleaf hc hab.symm (Ne.symm hne)
  obtain ⟨p, hp⟩ := hab.exists_isPath
  have hp' : (p.map (spineHom hc M ρ)).IsPath := hp.map Subtype.val_injective
  have hn (q : SurvivingSpine hc M ρ) (hq : q ∈ p.support) :
      (coreModel K).Nonleaf q.val := by
    have hq' : q.val ∈ (p.map (spineHom hc M ρ)).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    rcases ThinIntervals.Model.nonleaf_or_endpoint hp' hq' with h | h | h
    · exact h
    · exact h ▸ ha
    · exact h ▸ hb
  let f : SurvivingSpine hc M ρ → ℕ := fun q => (coreModel K).spineRank q.val
  have hchain : (p.support.map f).IsChain (fun u v => u ≤ v + 1 ∧ v ≤ u + 1) := by
    apply List.isChain_map_of_isChain f _ p.isChain_adj_support
    intro u v huv
    have hn' := spine_adj_nonleaf hc huv
    have hs := ThinIntervals.Model.spineRank_adj (core_thin hc) hn'.1 hn'.2
      ((spine_adj_iff hc M ρ).mp huv)
    dsimp only [f]
    omega
  have havoid : ∀ r ∈ p.support.map f, r % M ≠ ρ := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact spine_phase_ne hc q (hn q hq)
  have hmod := PeriodicPhases.unit_chain_mod_injective hρ hchain havoid
  have he' : f a % M = f b % M := by
    have h := congrArg (fun z : SpineLabel M ρ => z.val.val) he
    simpa only [spineLabel_val hc hM ha, spineLabel_val hc hM hb] using h
  have hrank := hmod
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, p.start_mem_support, rfl⟩))
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, p.end_mem_support, rfl⟩)) he'
  exact hne (Subtype.ext (ThinIntervals.Model.spineRank_injective (core_thin hc) ha hb
    (hab.map (spineHom hc M ρ)) hrank))

end
end SourceCovers
