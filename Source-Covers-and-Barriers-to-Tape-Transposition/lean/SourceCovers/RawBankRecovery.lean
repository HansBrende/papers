import SourceCovers.ExceptionalBank
import SourceCovers.ProtectedPhases

/-! Exact source banks contain the root read and are set-closed across every
selected actual edge with unpaid lower endpoint. This includes the original
core: all lowers of deleted core families are already in the phase payment. -/

namespace SourceCovers

open Classical Finset BoundedNesting LeanMachine LeanMachine.SourceBank

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

namespace ExactCoreBank

theorem root_mem {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (t : ℕ) : t ∈ values B t :=
  (hB t).superset (mem_shadowOrbit_self K t)

/-- Completing the orbit from an already reached vertex adds no values. -/
theorem values_subset {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) {s t : ℕ} (hs : s ∈ shadowOrbit K t) :
    values B s ⊆ values B t := by
  intro u hu
  exact (hB t).superset (shadowOrbit_trans hs ((hB s).subset hu))

theorem shadow_edge {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) {q : ActualFamily xs T} (hq : q ∈ K) (t : ℕ) :
    values B (q.shadow t) ⊆ values B t :=
  hB.values_subset ⟨[q], by simpa using hq, rfl⟩

/-- Clipping changes an actual hop only at its outer lower endpoint. -/
theorem actual_edge {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (hx : ∀ h, IsWalk (xs h))
    {q : ActualFamily xs T} (hq : q ∈ K) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ q.hops) (hunpaid : η.2.1 ≠ q.start) :
    values B η.2.1 ⊆ values B η.2.2 := by
  simpa only [q.shadow_exact hx hη hunpaid] using hB.shadow_edge hq η.2.2

theorem paid_actual_edge {K : Finset (ActualFamily xs T)} {B : Bank}
    (hB : ExactCoreBank K B) (hx : ∀ h, IsWalk (xs h)) {Γ : Finset ℕ}
    (houter : ∀ q ∈ K, q.start ∈ Γ) {q : ActualFamily xs T} (hq : q ∈ K)
    {η : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) (hunpaid : η.2.1 ∉ Γ) :
    values B η.2.1 ⊆ values B η.2.2 :=
  hB.actual_edge hx hq hη (fun he => hunpaid (he ▸ houter q hq))

end ExactCoreBank

/-- Every actual lower of a deleted core family belongs to the paid phase. -/
theorem deleted_family_lower_paid {K : Finset (ActualFamily xs T)} {M ρ : ℕ}
    {q : ActualFamily xs T} (hq : q ∈ K) (hcut : q ∉ retainedCore K M ρ)
    {η : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) : η.2.1 ∈ phasePayment K M ρ := by
  have hn : (⟨q, hq⟩ : CoreFamily K) ∉ phaseSurvivors K M ρ :=
    fun hs => hcut (mem_image.mpr ⟨⟨q, hq⟩, hs, rfl⟩)
  have hc : (⟨q, hq⟩ : CoreFamily K) ∈ coreNonleaves K ∧
      corePhase K M ⟨q, hq⟩ = ρ := by
    simpa only [phaseSurvivors, mem_filter, mem_univ, true_and, not_or,
      not_not] using hn
  exact mem_biUnion.mpr ⟨⟨q, hq⟩, mem_filter.mpr hc, mem_image.mpr ⟨η, hη, rfl⟩⟩

/-- A selected unpaid edge comes from a surviving core family or an exception. -/
theorem unpaid_family_retained {K E : Finset (ActualFamily xs T)} {M ρ : ℕ}
    {Γ : Finset ℕ} (hphase : phasePayment K M ρ ⊆ Γ)
    {q : ActualFamily xs T} (hq : q ∈ K ∪ E) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ q.hops) (hunpaid : η.2.1 ∉ Γ) : q ∈ retainedCore K M ρ ∪ E := by
  rcases mem_union.mp hq with hq | hq
  · apply mem_union_left
    by_contra hcut
    exact hunpaid (hphase (deleted_family_lower_paid hq hcut hη))
  · exact mem_union_right _ hq

/-- Set-closure across all original selected actual edges with unpaid lowers.
The bank represents the retained core, whereas the edge may be from the
original core; the phase payment justifies that distinction. -/
theorem ExactCoreBank.selected_actual_edge {K E : Finset (ActualFamily xs T)}
    {M ρ : ℕ} {B : Bank} (hB : ExactCoreBank (retainedCore K M ρ ∪ E) B)
    (hx : ∀ h, IsWalk (xs h)) {Γ : Finset ℕ}
    (hphase : phasePayment K M ρ ⊆ Γ) (houter : ∀ q ∈ K ∪ E, q.start ∈ Γ)
    {q : ActualFamily xs T} (hq : q ∈ K ∪ E) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ q.hops) (hunpaid : η.2.1 ∉ Γ) :
    values B η.2.1 ⊆ values B η.2.2 :=
  hB.actual_edge hx (unpaid_family_retained hphase hq hη hunpaid) hη
    (fun he => hunpaid (he ▸ houter q hq))

/-- Values of the raw coordinate paths, with coincident reads identified. -/
def rawBankValues {X : Type*} [DecidableEq X] (B : Bank) (x : ℕ → X) (t : ℕ) : Finset X :=
  (values B t).image x

theorem rawBankValues_mono {X : Type*} [DecidableEq X] {B : Bank} (x : ℕ → X)
    {s t : ℕ} (h : values B s ⊆ values B t) : rawBankValues B x s ⊆ rawBankValues B x t :=
  image_subset_image h

theorem ExactCoreBank.raw_root_mem {X : Type*} [DecidableEq X]
    {K : Finset (ActualFamily xs T)} {B : Bank} (hB : ExactCoreBank K B)
    (x : ℕ → X) (t : ℕ) : x t ∈ rawBankValues B x t :=
  mem_image_of_mem x (hB.root_mem t)

theorem ExactCoreBank.raw_selected_actual_edge {X : Type*} [DecidableEq X]
    {K E : Finset (ActualFamily xs T)} {M ρ : ℕ} {B : Bank}
    (hB : ExactCoreBank (retainedCore K M ρ ∪ E) B) (hx : ∀ h, IsWalk (xs h))
    {Γ : Finset ℕ} (hphase : phasePayment K M ρ ⊆ Γ)
    (houter : ∀ q ∈ K ∪ E, q.start ∈ Γ) {q : ActualFamily xs T} (hq : q ∈ K ∪ E)
    {η : Fin k × ℕ × ℕ} (hη : η ∈ q.hops) (hunpaid : η.2.1 ∉ Γ) (x : ℕ → X) :
    rawBankValues B x η.2.1 ⊆ rawBankValues B x η.2.2 :=
  rawBankValues_mono x (hB.selected_actual_edge hx hphase houter hq hη hunpaid)

end
end SourceCovers
