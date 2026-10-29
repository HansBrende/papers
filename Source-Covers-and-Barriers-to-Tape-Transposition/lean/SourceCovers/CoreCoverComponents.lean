import SourceCovers.ProtectedPhases
import LeanMachine.OrbitLabelBudget
import LeanMachine.TimeComponents

/-! Component labels of actual Q2 core orbits. Distinguished families consume
an owner-time budget; no component-cover hypothesis is assumed. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- Complete finite orbit for any retained subset of the actual core. -/
def coreOrbit (I : Finset (CoreFamily K)) (t : ℕ) : Finset ℕ :=
  FiniteOrbits.cloud (FiniteOrbits.successors I coreAction) I.card t

theorem core_orbit_exact (I : Finset (CoreFamily K)) (t : ℕ) :
    FiniteOrbits.wordOrbit I coreAction t = (coreOrbit I t : Set ℕ) := by
  apply FiniteOrbits.orbit_eq_cloud
  intro w hw hs
  rw [← List.toFinset_card_of_nodup (core_success_nodup w hs)]
  exact card_le_card (fun q hq => hw q (List.mem_toFinset.mp hq))

theorem core_successor_lt (I : Finset (CoreFamily K)) {t u : ℕ}
    (hu : u ∈ FiniteOrbits.successors I coreAction t) : u < t := by
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
  have h := q.val.shadow_active_bounds
    ((q.val.shadow_ne_self_iff t).mp (mem_filter.mp hq).2)
  exact h.2.1.trans_lt h.2.2.1

theorem coreOrbit_le (I : Finset (CoreFamily K)) {t u : ℕ} (hu : u ∈ coreOrbit I t) :
    u ≤ t :=
  OrbitLabelBudget.mem_cloud_le (fun _ _ hv => (core_successor_lt I hv).le) hu

/-- Distinguished retained families that can still act below the current time. -/
def markedBefore (I D : Finset (CoreFamily K)) (t : ℕ) : ℕ :=
  ((I ∩ D).filter (fun q => q.val.owner < t)).card

theorem markedBefore_le (I D : Finset (CoreFamily K)) (t : ℕ) :
    markedBefore I D t ≤ D.card :=
  card_le_card ((filter_subset _ _).trans inter_subset_right)

/-- Changing any label invariant under nondistinguished actions spends a
distinct distinguished family from the actual owner-time budget. -/
theorem core_label_stepBudget {β : Type*} (I D : Finset (CoreFamily K)) (c : ℕ → β)
    (hlabel : ∀ q ∈ I, q ∉ D → ∀ t, c (q.val.shadow t) = c t) :
    OrbitLabelBudget.StepBudget (FiniteOrbits.successors I coreAction) c (markedBefore I D) := by
  intro t u hu
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
  have hqI := (mem_filter.mp hq).1
  have hact := q.val.shadow_active_bounds
    ((q.val.shadow_ne_self_iff t).mp (mem_filter.mp hq).2)
  have hsub : (I ∩ D).filter (fun a => a.val.owner < q.val.shadow t) ⊆
      (I ∩ D).filter (fun a => a.val.owner < t) := by
    intro a ha
    obtain ⟨ha, hat⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨ha, hat.trans_le (hact.2.1.trans hact.2.2.1.le)⟩
  refine ⟨card_le_card hsub, ?_⟩
  intro hc
  have hqD : q ∈ D := by
    by_contra hqD
    exact hc (hlabel q hqI hqD t)
  have hqt : q ∈ (I ∩ D).filter (fun a => a.val.owner < t) :=
    mem_filter.mpr ⟨mem_inter.mpr ⟨hqI, hqD⟩, hact.2.2.1⟩
  have hqu : q ∉ (I ∩ D).filter (fun a => a.val.owner < q.val.shadow t) := by
    intro h
    exact (not_lt_of_ge hact.2.1) (mem_filter.mp h).2
  have hn := card_le_card (insert_subset_iff.mpr ⟨hqt, hsub⟩)
  rw [card_insert_of_notMem hqu] at hn
  exact hn

/-- At most two deterministic continuations share the root label. The sharper
bound counts only retained distinguished families whose owners precede the root. -/
theorem core_orbit_label_card_le {β : Type*} [DecidableEq β]
    (hc : HasSpanColoring K 2) (I D : Finset (CoreFamily K)) (c : ℕ → β)
    (hlabel : ∀ q ∈ I, q ∉ D → ∀ t, c (q.val.shadow t) = c t) (t : ℕ) :
    ((coreOrbit I t).image c).card ≤ 1 + 2 * markedBefore I D t := by
  have h := OrbitLabelBudget.image_cloud_card_le (core_deterministic_after hc I)
    (core_label_stepBudget I D c hlabel) I.card t
  have hb := core_successors_card hc I t
  change ((coreOrbit I t).image c).card ≤ _ at h
  nlinarith

theorem core_orbit_label_card_le_distinguished {β : Type*} [DecidableEq β]
    (hc : HasSpanColoring K 2) (I D : Finset (CoreFamily K)) (c : ℕ → β)
    (hlabel : ∀ q ∈ I, q ∉ D → ∀ t, c (q.val.shadow t) = c t) (t : ℕ) :
    ((coreOrbit I t).image c).card ≤ 1 + 2 * D.card := by
  exact (core_orbit_label_card_le hc I D c hlabel t).trans
    (by have := markedBefore_le I D t; omega)

/-- Original, untruncated spans used to join time components. -/
def nondistinguishedEdges (J D : Finset (CoreFamily K)) : Finset ℕ :=
  (J \ D).biUnion (fun q => q.val.edges)

theorem shadow_Ico_subset_edges (q : CoreFamily K) (t : ℕ) :
    Ico (q.val.shadow t) t ⊆ q.val.edges := by
  by_cases h : q.val.shadow t = t
  · simp [h]
  · have hb := q.val.shadow_active_bounds ((q.val.shadow_ne_self_iff t).mp h)
    intro e he
    have he' := mem_Ico.mp he
    exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem shadow_le (q : CoreFamily K) (t : ℕ) : q.val.shadow t ≤ t := by
  by_cases h : q.val.shadow t = t
  · exact h.le
  · have hb := q.val.shadow_active_bounds ((q.val.shadow_ne_self_iff t).mp h)
    exact hb.2.1.trans hb.2.2.1.le

theorem shadow_Ico_subset_nondistinguishedEdges {I J D : Finset (CoreFamily K)}
    (hIJ : I ⊆ J) {q : CoreFamily K} (hq : q ∈ I) (hqD : q ∉ D) (t : ℕ) :
    Ico (q.val.shadow t) t ⊆ nondistinguishedEdges J D := by
  intro e he
  exact mem_biUnion.mpr ⟨q, mem_sdiff.mpr ⟨hIJ hq, hqD⟩,
    shadow_Ico_subset_edges q t he⟩

/-- Concrete component labels are invariant across every retained
nondistinguished shadow, using its whole original span. -/
theorem componentLabel_shadow {I J D : Finset (CoreFamily K)}
    (hIJ : I ⊆ J) {q : CoreFamily K} (hq : q ∈ I) (hqD : q ∉ D) (t : ℕ) :
    TimeComponents.label (nondistinguishedEdges J D) (q.val.shadow t) =
      TimeComponents.label (nondistinguishedEdges J D) t :=
  TimeComponents.label_eq_of_Ico_subset (shadow_le q t)
    (shadow_Ico_subset_nondistinguishedEdges hIJ hq hqD t)

/-- The orbit meets at most one root component plus two components per
distinguished family that could act before the root. -/
theorem core_orbit_component_card_le (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (t : ℕ) :
    ((coreOrbit I t).image (TimeComponents.label (nondistinguishedEdges J D))).card ≤
      1 + 2 * markedBefore I D t :=
  core_orbit_label_card_le hc I D _ (fun _ hq hqD => componentLabel_shadow hIJ hq hqD) t

theorem core_orbit_component_card_le_distinguished (hc : HasSpanColoring K 2)
    (I J D : Finset (CoreFamily K)) (hIJ : I ⊆ J) (t : ℕ) :
    ((coreOrbit I t).image (TimeComponents.label (nondistinguishedEdges J D))).card ≤
      1 + 2 * D.card :=
  core_orbit_label_card_le_distinguished hc I D _
    (fun _ hq hqD => componentLabel_shadow hIJ hq hqD) t

theorem phaseOrbit_subset_coreOrbit (M ρ t : ℕ) :
    phaseOrbit K M ρ t ⊆ coreOrbit (phaseSurvivors K M ρ) t := by
  intro u hu
  have h := FiniteOrbits.cloud_subset_orbit (phaseSurvivors K M ρ) coreAction (M + 1) t hu
  rwa [core_orbit_exact] at h

theorem coreOrbit_phase_eq (hc : HasSpanColoring K 2) {M ρ : ℕ} (hρ : ρ < M) (t : ℕ) :
    coreOrbit (phaseSurvivors K M ρ) t = phaseOrbit K M ρ t := by
  apply Finset.coe_injective
  exact (core_orbit_exact (phaseSurvivors K M ρ) t).symm.trans (phase_orbit_exact hc hρ t)

theorem phaseOrbit_le {M ρ t u : ℕ} (hu : u ∈ phaseOrbit K M ρ t) : u ≤ t :=
  coreOrbit_le _ (phaseOrbit_subset_coreOrbit M ρ t hu)

/-- All retained phases may use the same component system built before
deletion from the nondistinguished original core spans. -/
theorem phase_orbit_component_card_le (hc : HasSpanColoring K 2)
    (D : Finset (CoreFamily K)) (M ρ t : ℕ) :
    ((phaseOrbit K M ρ t).image (TimeComponents.label
      (nondistinguishedEdges univ D))).card ≤ 1 + 2 * D.card := by
  calc
    _ ≤ ((coreOrbit (phaseSurvivors K M ρ) t).image
        (TimeComponents.label (nondistinguishedEdges univ D))).card :=
      card_le_card (image_subset_image (phaseOrbit_subset_coreOrbit M ρ t))
    _ ≤ _ := core_orbit_component_card_le_distinguished hc (phaseSurvivors K M ρ) univ D
      (subset_univ _) t

end
end SourceCovers
