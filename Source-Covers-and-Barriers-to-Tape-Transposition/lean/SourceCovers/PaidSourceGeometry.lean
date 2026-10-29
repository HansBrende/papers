import SourceCovers.ExactSourceBank
import SourceCovers.ResidualRecovery

set_option autoImplicit false

/-!
# Actual dependencies and the initial paid source geometry

Every long work dependency belongs to its complete actual family; short
work dependencies coincide with a state predecessor. Original selected
families determine the selected relation before rank-phase deletion.
-/

namespace SourceCovers

open Classical Finset BoundedNesting LeanMachine LeanMachine.SourceBank
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}

/-- Actual lower endpoints from the given complete families ending at `v`. -/
def familyParents (F : Finset (ActualFamily xs T)) (v : ℕ) : Finset ℕ :=
  F.biUnion fun G => (G.hops.filter (fun η => η.2.2 = v)).image (fun η => η.2.1)

theorem mem_familyParents {F : Finset (ActualFamily xs T)} {v u : ℕ} :
    u ∈ familyParents F v ↔
      ∃ G ∈ F, ∃ η ∈ G.hops, η.2.2 = v ∧ η.2.1 = u := by
  simp only [familyParents, mem_biUnion, mem_image, mem_filter]
  aesop

theorem familyParents_mono {F F' : Finset (ActualFamily xs T)} (hFF' : F ⊆ F') (v : ℕ) :
    familyParents F v ⊆ familyParents F' v := by
  intro u hu
  obtain ⟨G, hG, η, hη, hv, hu⟩ := mem_familyParents.mp hu
  exact mem_familyParents.mpr ⟨G, hFF' hG, η, hη, hv, hu⟩

/-- Every long work hop is present, without a unit-step hypothesis. -/
theorem mem_full_familyParents {v u : ℕ} :
    u ∈ familyParents (univ : Finset (ActualFamily xs T)) v ↔
      ∃ h : Fin k, IsHop (xs h) T u v := by
  constructor
  · intro hu
    obtain ⟨G, _, η, hη, hv, hu⟩ := mem_familyParents.mp hu
    have hh := mem_allHops.mp (mem_fam.mp hη).1
    rw [hv, hu] at hh
    exact ⟨η.1, hh⟩
  · rintro ⟨h, hh⟩
    let η : Fin k × ℕ × ℕ := (h, u, v)
    have hη : η ∈ allHops xs T := mem_allHops.mpr hh
    let G : ActualFamily xs T :=
      ⟨key xs (actualOwner xs) η, mem_image_of_mem _ hη⟩
    exact mem_familyParents.mpr
      ⟨G, mem_univ _, η, mem_filter.mpr ⟨hη, rfl⟩, rfl, rfl⟩

/-- Full causal parent relation. Length-one work hops are already state edges. -/
def actualParents (xs : Fin k → ℕ → ℤ) (T v : ℕ) : Finset ℕ :=
  (if v = 0 then ∅ else {v - 1}) ∪ familyParents (univ : Finset (ActualFamily xs T)) v

theorem mem_actualParents {v u : ℕ} :
    u ∈ actualParents xs T v ↔ u + 1 = v ∨ ∃ h : Fin k, IsHop (xs h) T u v := by
  rw [actualParents, mem_union, mem_full_familyParents]
  apply or_congr _ Iff.rfl
  split_ifs with hv
  · simp [hv]
  · simp only [mem_singleton]
    omega

theorem actualParents_earlier {v u : ℕ} (hu : u ∈ actualParents xs T v) : u < v := by
  rcases mem_actualParents.mp hu with hstate | ⟨h, hh⟩
  · omega
  · have := hh.1
    omega

/-- Every physical previous visit is included, also when its hop has length one. -/
theorem work_previous_visit_mem_actualParents (h : Fin k) {u v : ℕ}
    (huv : u < v) (hv : v < T) (heq : xs h v = xs h u)
    (hlast : ∀ t ∈ Ioo u v, xs h t ≠ xs h u) : u ∈ actualParents xs T v := by
  apply mem_actualParents.mpr
  by_cases hs : u + 1 = v
  · exact Or.inl hs
  · exact Or.inr ⟨h, by omega, hv, heq, hlast⟩

/-- Original selection, before any families are removed by the rank phase. -/
def selectedParents (K E : Finset (ActualFamily xs T)) : ℕ → Finset ℕ :=
  familyParents (K ∪ E)

theorem selectedParents_subset (K E : Finset (ActualFamily xs T)) (v : ℕ) :
    selectedParents K E v ⊆ actualParents xs T v := by
  intro u hu
  exact mem_union_right _ (familyParents_mono (subset_univ _) v hu)

/-- Outer lowers are deduplicated across all originally selected families. -/
def outerPayment (F : Finset (ActualFamily xs T)) : Finset ℕ :=
  F.image ActualFamily.start

def initialPayment (K E : Finset (ActualFamily xs T)) (M ρ : ℕ) : Finset ℕ :=
  outerPayment (K ∪ E) ∪ phasePayment K M ρ

theorem outer_mem_initialPayment {K E : Finset (ActualFamily xs T)} {M ρ : ℕ}
    {G : ActualFamily xs T} (hG : G ∈ K ∪ E) : G.start ∈ initialPayment K E M ρ :=
  mem_union_left _ (mem_image_of_mem _ hG)

theorem phasePayment_subset_initialPayment (K E : Finset (ActualFamily xs T)) (M ρ : ℕ) :
    phasePayment K M ρ ⊆ initialPayment K E M ρ := subset_union_right

theorem admissiblePhase_lt {K : Finset (ActualFamily xs T)} {P : Finset (CoreFamily K)}
    {M ρ : ℕ} (hρ : ρ ∈ admissiblePhases K P M) : ρ < M :=
  mem_range.mp (mem_sdiff.mp hρ).1

theorem initialPayment_card_le (K E : Finset (ActualFamily xs T)) (M ρ : ℕ) :
    (initialPayment K E M ρ).card ≤
      (outerPayment (K ∪ E)).card + (phasePayment K M ρ).card := card_union_le _ _

theorem outerPayment_card_le (K E : Finset (ActualFamily xs T)) :
    (outerPayment (K ∪ E)).card ≤ K.card + E.card :=
  card_image_le.trans (card_union_le K E)

theorem family_start_lt (G : ActualFamily xs T) : G.start < T := by
  obtain ⟨η, hη⟩ := fam_nonempty xs (allHops xs T) (actualOwner xs) G
  have hstart := (fam_bounds hη).1
  change G.start ≤ η.2.1 at hstart
  have hh := mem_allHops.mp (mem_fam.mp hη).1
  have := hh.1
  have := hh.2.1
  omega

theorem initialPayment_subset_range (K E : Finset (ActualFamily xs T)) (M ρ : ℕ) :
    initialPayment K E M ρ ⊆ range T := by
  intro u hu
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨G, _, rfl⟩ := mem_image.mp hu
    exact mem_range.mpr (family_start_lt G)
  · obtain ⟨G, _, hu⟩ := mem_biUnion.mp hu
    obtain ⟨η, hη, rfl⟩ := mem_image.mp hu
    have hh := mem_allHops.mp (mem_fam.mp hη).1
    exact mem_range.mpr (by have := hh.1; have := hh.2.1; omega)

/-- Closure follows from the concrete selected hop and the actual initial
payment. No closure certificate is assumed. -/
theorem initial_selected_values_closed {K : Finset (ActualFamily xs T)}
    (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M)
    (E : Finset (ActualFamily xs T)) (hx : ∀ h, IsWalk (xs h))
    {v u : ℕ} (hu : u ∈ selectedParents K E v)
    (hunpaid : u ∉ initialPayment K E M ρ) :
    values (exactSourceBank (ρ := ρ) hc hM E) u ⊆
      values (exactSourceBank (ρ := ρ) hc hM E) v := by
  obtain ⟨G, hG, η, hη, hv, hup⟩ := mem_familyParents.mp hu
  have h := exactSourceBank_selected_edge hc hM hρ E hx
    (phasePayment_subset_initialPayment K E M ρ)
    (fun G hG => outer_mem_initialPayment hG) hG hη (by rwa [hup])
  simpa only [hv, hup] using h

theorem initial_selected_raw_values_closed {K : Finset (ActualFamily xs T)}
    (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M)
    (E : Finset (ActualFamily xs T)) (hx : ∀ h, IsWalk (xs h))
    {v u : ℕ} (hu : u ∈ selectedParents K E v)
    (hunpaid : u ∉ initialPayment K E M ρ) {X : Type*} [DecidableEq X] (x : ℕ → X) :
    rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x u ⊆
      rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x v :=
  image_subset_image (initial_selected_values_closed hc hM hρ E hx hu hunpaid)

/-- Every live residual lower crosses the same boundary through a state
edge or an actual hop of a family outside the original selection. -/
theorem residual_live_subset_boundary (K E : Finset (ActualFamily xs T))
    (n : ℕ) (Γ₀ : Finset ℕ) (e : ℕ) :
    ResidualGeometry.live (residualParents (actualParents xs T) (selectedParents K E)) n Γ₀ e ⊆
      boundaryLowers (univ \ (K ∪ E)) e := by
  intro u hu
  obtain ⟨_, hue, v, _, huv, hev⟩ := ResidualGeometry.mem_live.mp hu
  obtain ⟨hparent, hnot⟩ := mem_sdiff.mp huv
  rcases mem_union.mp hparent with hstate | hwork
  · by_cases hv : v = 0
    · simp [hv] at hstate
    · have hstate : u = v - 1 := by simpa [hv] using hstate
      exact mem_boundaryLowers.mpr (Or.inl (by omega))
  · obtain ⟨G, _, η, hη, hv, hup⟩ := mem_familyParents.mp hwork
    have hG : G ∉ K ∪ E := by
      intro hG
      exact hnot (mem_familyParents.mpr ⟨G, hG, η, hη, hv, hup⟩)
    exact mem_boundaryLowers.mpr (Or.inr
      ⟨G, mem_sdiff.mpr ⟨mem_univ _, hG⟩, η, hη, by omega, by omega, hup⟩)

/-- Full-system coloring and outside-family sizes derive the live-boundary
bound. It is valid for every horizon and any existing payment. -/
theorem residual_live_card_le (K E : Finset (ActualFamily xs T)) {N a : ℕ}
    (hcolor : HasSpanColoring (univ : Finset (ActualFamily xs T)) N)
    (hsize : ∀ G : ActualFamily xs T, G ∉ K ∪ E → G.hops.card ≤ a)
    (n : ℕ) (Γ₀ : Finset ℕ) (e : ℕ) :
    (ResidualGeometry.live (residualParents (actualParents xs T) (selectedParents K E))
      n Γ₀ e).card ≤ 1 + N * a := by
  apply (card_le_card (residual_live_subset_boundary K E n Γ₀ e)).trans
  exact boundary_lowers_le _ e a N (fun G hG => hsize G (mem_sdiff.mp hG).2)
    (activeFamilies_card_le (hcolor.mono (subset_univ _)) e)

/-- Keep the deduplicated outer lowers and the exact admissible-phase count. -/
theorem initialPayment_average (K E : Finset (ActualFamily xs T))
    (P : Finset (CoreFamily K)) (M : ℕ) (hA : (admissiblePhases K P M).Nonempty) :
    (∑ ρ ∈ admissiblePhases K P M, ((initialPayment K E M ρ).card : ℝ)) /
        (admissiblePhases K P M).card ≤
      (outerPayment (K ∪ E)).card +
        ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) /
          (admissiblePhases K P M).card := by
  have hpos : (0 : ℝ) < (admissiblePhases K P M).card := by
    exact_mod_cast card_pos.mpr hA
  have hsum : (∑ ρ ∈ admissiblePhases K P M, ((initialPayment K E M ρ).card : ℝ)) ≤
      ∑ ρ ∈ admissiblePhases K P M,
        (((outerPayment (K ∪ E)).card : ℝ) + (phasePayment K M ρ).card) :=
    sum_le_sum fun ρ _ => by exact_mod_cast initialPayment_card_le K E M ρ
  have hphase : (∑ ρ ∈ admissiblePhases K P M, ((phasePayment K M ρ).card : ℝ)) ≤
      ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) := by
    exact_mod_cast phase_payment_sum_hops K P M
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  apply (div_le_iff₀ hpos).mpr
  have hcancel : ((outerPayment (K ∪ E)).card +
      ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) /
        (admissiblePhases K P M).card) * (admissiblePhases K P M).card =
      (admissiblePhases K P M).card * ((outerPayment (K ∪ E)).card : ℝ) +
        ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) := by
    field_simp
  rw [hcancel]
  linarith

/-- The manuscript's budget follows from the actual phase union and family
counts; a larger protected set can only help if it uses fewer residues. -/
theorem initialPayment_average_of_budgets (K E : Finset (ActualFamily xs T))
    (P : Finset (CoreFamily K)) {J q M R : ℕ} {τ : ℝ}
    (hK : K.card ≤ J) (hE : E.card ≤ q) (hP : P.card ≤ R) (hR : R < M)
    (hτ : ((∑ G ∈ coreNonleaves K \ P, G.val.hops.card : ℕ) : ℝ) ≤ τ) :
    0 < (admissiblePhases K P M).card ∧
    (∑ ρ ∈ admissiblePhases K P M, ((initialPayment K E M ρ).card : ℝ)) /
        (admissiblePhases K P M).card ≤
      J + q + τ / ((M - R : ℕ) : ℝ) := by
  have hphase := protected_phase_average K P hP hR
  have hpos : 0 < (admissiblePhases K P M).card := by omega
  refine ⟨hpos, ?_⟩
  have hb := initialPayment_average K E P M (card_pos.mp hpos)
  have houter : ((outerPayment (K ∪ E)).card : ℝ) ≤ J + q := by
    exact_mod_cast (outerPayment_card_le K E).trans (Nat.add_le_add hK hE)
  have hmass := hphase.2.2
  have hτdiv := div_le_div_of_nonneg_right hτ (Nat.cast_nonneg (M - R) : (0 : ℝ) ≤ _)
  linarith

end
end SourceCovers
