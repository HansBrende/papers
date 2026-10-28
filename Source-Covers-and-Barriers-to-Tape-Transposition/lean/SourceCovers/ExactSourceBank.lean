import SourceCovers.SpineGeometry
import SourceCovers.LeafSandwich
import SourceCovers.ExceptionalBank
import SourceCovers.RawBankRecovery
import LeanMachine.PackedWords

/-! The exact source bank for the periodically retained actual core.
All choices are functions of the geometry, before any root or argument path.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.MonotonePatches LeanMachine.SourceBank

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
variable {K : Finset (ActualFamily xs T)}

def spineSystem (hc : HasSpanColoring K 2) (M ρ : ℕ) :
    PackedWords.System (SurvivingSpine hc M ρ) where
  patch := fun q => q.val.val.shadowPatch
  nonempty := fun q => (coreModel K).nonempty q.val
  owner := fun q => q.val.val.owner
  crosses := fun q t ht => ⟨(q.val.val.clipped_bounds t).2, ht.1⟩

def spineBank (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M) : Bank :=
  (spineSystem hc M ρ).bank (spineLabel hc hM)

theorem spineBank_length (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) :
    (spineBank (ρ := ρ) hc hM).length = 1 + M.choose 2 := by
  rw [spineBank, PackedWords.System.bank_length, spineLabel_card hρ,
    Nat.sub_add_cancel (show 1 ≤ M by omega)]

theorem spineBank_bounded (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) :
    Bounded (spineBank (ρ := ρ) hc hM) (1 + 3 * (M.choose 2 : ℕ)) := by
  have h : Bounded (spineBank (ρ := ρ) hc hM)
      (1 + 3 * ((Fintype.card (SpineLabel M ρ) + 1).choose 2 : ℕ)) :=
    (spineSystem hc M ρ).bank_bounded (spineLabel hc hM)
  rwa [spineLabel_card hρ, Nat.sub_add_cancel (show 1 ≤ M by omega)] at h

theorem spineBank_exact (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (t : ℕ) :
    (values (spineBank (ρ := ρ) hc hM) t : Set ℕ) =
      FiniteOrbits.wordOrbit univ (fun q : SurvivingSpine hc M ρ => q.val.val.shadowAction) t :=
  (spineSystem hc M ρ).bank_exact (spineLabel hc hM)
    (ThinIntervals.Model.isAcyclic (spine_thin hc M ρ))
    (fun _ _ hab he => spineLabel_injective_on_component hc hM hρ hab he) t

def coreBank (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M) : Bank :=
  leafSandwich (spineBank (ρ := ρ) hc hM) (packingLeafMap hc M ρ)

def coreSlots (M : ℕ) : ℕ := 4 + 2 * M * (M - 1)
def coreCost (M : ℕ) : ℕ := 16 + 24 * M * (M - 1)
def bankSlots (M q : ℕ) : ℕ := coreSlots M * (1 + coreSlots M) ^ q
def bankCost (M q : ℕ) : ℕ := coreCost M * (1 + 3 * coreCost M) ^ q

private theorem twice_choose_two (M : ℕ) : 2 * M.choose 2 = M * (M - 1) := by
  simpa only [Nat.descFactorial, Nat.factorial_two, Nat.sub_zero, mul_one, mul_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose M 2).symm

theorem coreBank_length (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) : (coreBank (ρ := ρ) hc hM).length = coreSlots M := by
  rw [coreBank, leafSandwich_length, spineBank_length hc hM hρ]
  have h := twice_choose_two M
  dsimp [coreSlots]
  nlinarith

theorem coreBank_bounded (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) : Bounded (coreBank (ρ := ρ) hc hM) (coreCost M) := by
  have h : Bounded (coreBank (ρ := ρ) hc hM) (16 * (1 + 3 * (M.choose 2 : ℕ))) :=
    leafSandwich_bounded (spineBank_bounded hc hM hρ) (packingLeafMap_bounded hc M ρ) (by positivity)
  have he : (coreCost M : ℝ) = 16 * (1 + 3 * (M.choose 2 : ℕ)) := by
    have htwo : (2 : ℝ) * (M.choose 2 : ℕ) = (M : ℝ) * ((M - 1 : ℕ) : ℝ) :=
      by exact_mod_cast twice_choose_two M
    simp only [coreCost, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  rwa [he]

theorem coreBank_exact (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) : ExactCoreBank (retainedCore K M ρ) (coreBank (ρ := ρ) hc hM) := by
  intro t
  have hB (v u : ℕ) : u ∈ values (spineBank (ρ := ρ) hc hM) v ↔
      u ∈ FiniteOrbits.wordOrbit (packingSpines hc M ρ) coreAction v := by
    rw [spine_orbit_subtype hc M ρ v]
    exact Set.ext_iff.mp (spineBank_exact hc hM hρ v) u
  have he : (values (coreBank (ρ := ρ) hc hM) t : Set ℕ) =
      FiniteOrbits.wordOrbit (phaseSurvivors K M ρ) coreAction t :=
    Set.ext (fun u => leafSandwich_exact hB t u)
  exact he.trans ((phase_orbit_exact hc hρ t).trans (phase_shadowOrbit_exact hc hρ t).symm)

theorem coreBank_values_card (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (t : ℕ) :
    (values (coreBank (ρ := ρ) hc hM) t).card ≤ 2 * M + 3 := by
  have he : values (coreBank (ρ := ρ) hc hM) t = phaseOrbit K M ρ t := by
    apply Finset.coe_injective
    exact (coreBank_exact hc hM hρ t).trans (phase_shadowOrbit_exact hc hρ t)
  rw [he]
  exact phase_orbit_card hc M ρ t

/-- The entire source bank, constructed before the root and the argument path. -/
def exactSourceBank (hc : HasSpanColoring K 2) {M ρ : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) : Bank :=
  ordered (coreBank (ρ := ρ) hc hM) ((orderedExceptions E).map ActualFamily.shadowAction)

theorem exactSourceBank_length (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) :
    (exactSourceBank (ρ := ρ) hc hM E).length = bankSlots M E.card := by
  simp only [exactSourceBank, ordered_length, List.length_map, orderedExceptions_length,
    coreBank_length hc hM hρ, bankSlots]

theorem exactSourceBank_bounded (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) :
    Bounded (exactSourceBank (ρ := ρ) hc hM E) (bankCost M E.card) := by
  intro X _ Y n
  have h := bounded_ordered (coreBank_bounded hc hM hρ) (Nat.cast_nonneg _)
    ((orderedExceptions E).map ActualFamily.shadowAction) Y n
  simpa only [exactSourceBank, bankCost, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    Nat.cast_ofNat, List.length_map, orderedExceptions_length] using h

theorem exactSourceBank_exact (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) :
    ExactCoreBank (retainedCore K M ρ ∪ E) (exactSourceBank (ρ := ρ) hc hM E) := by
  intro t
  simpa only [exactSourceBank, orderedExceptions_toFinset] using
    ordered_values_exact (coreBank_exact hc hM hρ) (orderedExceptions E)
      (orderedExceptions_pairwise E) t

theorem exactSourceBank_cover (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (t : ℕ) :
    ∃ R : Finset ℕ, R.card ≤ (2 * M + 4) ^ E.card ∧
      (values (exactSourceBank (ρ := ρ) hc hM E) t : Set ℕ) =
        ⋃ r ∈ R, shadowOrbit (retainedCore K M ρ) r := by
  rw [exactSourceBank_exact hc hM hρ E t]
  simpa only [orderedExceptions_toFinset, orderedExceptions_length,
    show 2 * M + 3 + 1 = 2 * M + 4 by omega] using
    exceptional_orbit_core_cover (coreBank_exact hc hM hρ) (orderedExceptions E)
      (orderedExceptions_pairwise E) (coreBank_values_card hc hM hρ) t

theorem exactSourceBank_values_card (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (t : ℕ) :
    (values (exactSourceBank (ρ := ρ) hc hM E) t).card ≤
      (2 * M + 3) * (2 * M + 4) ^ E.card := by
  simpa only [exactSourceBank, orderedExceptions_length,
    show 2 * M + 3 + 1 = 2 * M + 4 by omega] using
    ordered_values_card (coreBank_values_card hc hM hρ) (orderedExceptions E) t

theorem bankSlots_mono (M : ℕ) {p q : ℕ} (hpq : p ≤ q) : bankSlots M p ≤ bankSlots M q :=
  Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) hpq)

theorem bankCost_mono (M : ℕ) {p q : ℕ} (hpq : p ≤ q) : bankCost M p ≤ bankCost M q :=
  Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) hpq)

/-- Theorem S, with the paper's constants and any upper bound on the number
of exceptions. No bound on the number of core families is required. -/
theorem exact_source_bank (hc : HasSpanColoring K 2) {M ρ q : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (hE : E.card ≤ q) :
    ∃ B : Bank, B.length ≤ bankSlots M q ∧ Bounded B (bankCost M q) ∧
      ExactCoreBank (retainedCore K M ρ ∪ E) B ∧
      (∀ t, ∃ R : Finset ℕ, R.card ≤ (2 * M + 4) ^ q ∧
        (values B t : Set ℕ) = ⋃ r ∈ R, shadowOrbit (retainedCore K M ρ) r) ∧
      ∀ t, (values B t).card ≤ (2 * M + 3) * (2 * M + 4) ^ q := by
  refine ⟨exactSourceBank (ρ := ρ) hc hM E, ?_, ?_, exactSourceBank_exact hc hM hρ E, ?_, ?_⟩
  · rw [exactSourceBank_length hc hM hρ E]
    exact bankSlots_mono M hE
  · exact bounded_mono (exactSourceBank_bounded hc hM hρ E) (by exact_mod_cast bankCost_mono M hE)
  · intro t
    obtain ⟨R, hR, he⟩ := exactSourceBank_cover hc hM hρ E t
    exact ⟨R, hR.trans (pow_le_pow_right₀ (by omega) hE), he⟩
  · intro t
    exact (exactSourceBank_values_card hc hM hρ E t).trans
      (Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) hE))

/-- The original selected-edge consequence, including families removed by
the periodic phase. The payment set may contain additional vertices. -/
theorem exactSourceBank_selected_edge (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (hx : ∀ h, BoundedNesting.IsWalk (xs h)) {Γ : Finset ℕ}
    (hphase : phasePayment K M ρ ⊆ Γ) (houter : ∀ G ∈ K ∪ E, G.start ∈ Γ)
    {G : ActualFamily xs T} (hG : G ∈ K ∪ E) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ G.hops) (hunpaid : η.2.1 ∉ Γ) :
    values (exactSourceBank (ρ := ρ) hc hM E) η.2.1 ⊆
      values (exactSourceBank (ρ := ρ) hc hM E) η.2.2 :=
  (exactSourceBank_exact hc hM hρ E).selected_actual_edge hx hphase houter hG hη hunpaid

/-- The raw variation consequence uses only the unit-speed input path on
the finite horizon. The bank itself was fixed before choosing this path. -/
theorem exactSourceBank_raw_variation (hc : HasSpanColoring K 2) {M ρ q : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (hE : E.card ≤ q)
    {X : Type} [PseudoMetricSpace X] (x : ℕ → X)
    (hx : ∀ e < T - 1, dist (x e) (x (e + 1)) ≤ 1) :
    cost (exactSourceBank (ρ := ρ) hc hM E) x (T - 1) ≤
      (bankCost M q : ℝ) * ((T - 1 : ℕ) : ℝ) := by
  have hB : Bounded (exactSourceBank (ρ := ρ) hc hM E) (bankCost M q) :=
    bounded_mono (exactSourceBank_bounded hc hM hρ E) (by exact_mod_cast bankCost_mono M hE)
  exact hB.unit_variation (Nat.cast_nonneg _) x (T - 1) hx

theorem exactSourceBank_raw_root (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    {X : Type*} [DecidableEq X] (x : ℕ → X) (t : ℕ) :
    x t ∈ rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t :=
  (exactSourceBank_exact hc hM hρ E).raw_root_mem x t

theorem exactSourceBank_raw_values_card (hc : HasSpanColoring K 2) {M ρ q : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (hE : E.card ≤ q)
    {X : Type*} [DecidableEq X] (x : ℕ → X) (t : ℕ) :
    (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t).card ≤
      (2 * M + 3) * (2 * M + 4) ^ q :=
  card_image_le.trans ((exactSourceBank_values_card hc hM hρ E t).trans
    (Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) hE)))

theorem exactSourceBank_raw_selected_edge (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (hx : ∀ h, BoundedNesting.IsWalk (xs h)) {Γ : Finset ℕ}
    (hphase : phasePayment K M ρ ⊆ Γ) (houter : ∀ G ∈ K ∪ E, G.start ∈ Γ)
    {G : ActualFamily xs T} (hG : G ∈ K ∪ E) {η : Fin k × ℕ × ℕ}
    (hη : η ∈ G.hops) (hunpaid : η.2.1 ∉ Γ)
    {X : Type*} [DecidableEq X] (x : ℕ → X) :
    rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x η.2.1 ⊆
      rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x η.2.2 :=
  (exactSourceBank_exact hc hM hρ E).raw_selected_actual_edge hx hphase houter hG hη hunpaid x

end
end SourceCovers
