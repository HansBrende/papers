import SourceCovers.ContinuationClusters
import LeanMachine.FiniteHullVariation

set_option autoImplicit false

/-! One time hull for all nonroot continuation suppliers. Actual exceptions
are sorted once; absent exceptions are identities. The older bank is the
fixed exact bank, including every slot and its multiplicity. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

def newerException (E : Finset (ActualFamily xs T)) : Option (ActualFamily xs T) :=
  if (orderedExceptions E).length ≤ 1 then none else (orderedExceptions E)[0]?

def olderException (E : Finset (ActualFamily xs T)) : Option (ActualFamily xs T) :=
  if (orderedExceptions E).length ≤ 1 then (orderedExceptions E)[0]? else (orderedExceptions E)[1]?

private theorem two_options {α : Type*} (l : List α) (h : l.length ≤ 2) :
    (if l.length ≤ 1 then none else l[0]?).toList ++
      (if l.length ≤ 1 then l[0]? else l[1]?).toList = l := by
  match l with
  | [] => rfl
  | [a] => rfl
  | [a, b] => rfl
  | a :: b :: c :: l => simp only [List.length_cons] at h; omega

theorem two_exceptions_ordered (E : Finset (ActualFamily xs T)) (hE : E.card ≤ 2) :
    (newerException E).toList ++ (olderException E).toList = orderedExceptions E :=
  two_options _ (by simpa only [orderedExceptions_length] using hE)

/-- Normalized movement over the hull of the nonroot maximal suppliers.
The empty set and a singleton both give zero. Illegal phases are set to zero
only to make the finite averaging function total. -/
def phaseMovement (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ) (L ρ t : ℕ) : ℝ :=
  if hρ : ρ < M then
    FiniteHullVariation.movement
      (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset) x
      ((continuationSuppliers (coreBank_exact hc hM hρ)
        (newerException E) (olderException E) t).erase t) t / L
  else 0

theorem phaseMovement_nonneg (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ) (L ρ t : ℕ) :
    0 ≤ phaseMovement hc hM E x L ρ t := by
  unfold phaseMovement
  split_ifs
  · exact div_nonneg (FiniteHullVariation.movement_nonneg ..) (Nat.cast_nonneg _)
  · exact le_rfl

/-- For a fixed modulus the entire older bank has a uniform variation bound.
This supplies the boundedness needed for the later real lower limits. -/
theorem phaseMovement_le (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ) {L ρ t : ℕ}
    (ht : t < T) (hstep : ∀ u < T - 1, dist (x u : ℝ) (x (u + 1) : ℝ) ≤ 1) :
    phaseMovement hc hM E x L ρ t ≤
      (bankCost M 1 : ℝ) * ((T - 1 : ℕ) : ℝ) / L := by
  unfold phaseMovement
  split_ifs with hρ
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply (FiniteHullVariation.movement_le_cost _ _ (fun u hu =>
      continuationSuppliers_past _ _ _ (mem_erase.mp hu).2) (by omega : t ≤ T - 1)).trans
    apply exactSourceBank_raw_variation hc hM hρ _ _ (fun u => (x u : ℝ)) hstep
    cases olderException E <;> simp
  · positivity

/-- The sharper one-cluster gap bound uses the clipped quadratic loss,
including the empty-supplier case without an extra case assumption. -/
theorem phaseMovement_gap (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (hE : E.card ≤ 2)
    (x : ℕ → ℕ) {L t : ℕ} (ht : t < T) (hx : ∀ u < T, x u < L)
    (D : Finset (CoreFamily K)) {r : ℕ} (hD : D.card ≤ r) {α : ℝ}
    (hV : (∑ q ∈ univ \ D, ∑ u ∈ q.val.edges,
      dist (x u : ℝ) (x (u + 1) : ℝ)) ≤ α * L) :
    let S := rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t
    ∀ hS : S.Nonempty,
    max (1 - α) 0 ^ 2 / (4 * (2 * (r : ℝ) + 1) * (2 * (M : ℝ) + 4)) -
      AnchoredGapErosion.penalty (min (phaseMovement hc hM E x L ρ t) 1) ≤
      GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L := by
  intro S hS
  let F := (continuationSuppliers (coreBank_exact hc hM hρ)
    (newerException E) (olderException E) t).erase t
  let ends := FiniteHullVariation.endpoints F t
  have hends := FiniteHullVariation.endpoints_bounds (fun u hu =>
    continuationSuppliers_past _ _ _ (mem_erase.mp hu).2 : ∀ u ∈ F, u ≤ t)
  have horder : ((newerException E).toList ++ (olderException E).toList).Pairwise
      (fun a b => b.owner ≤ a.owner) := by
    rw [two_exceptions_ordered E hE]
    exact orderedExceptions_pairwise E
  have hbank : twoExceptionBank (coreBank (ρ := ρ) hc hM)
      (newerException E) (olderException E) = exactSourceBank (ρ := ρ) hc hM E := by
    rw [twoExceptionBank, two_exceptions_ordered E hE, exactSourceBank]
  have h := continuationClusters_gap hc hM hρ (newerException E) (olderException E)
    horder (exactSourceBank_exact hc hM hρ (olderException E).toList.toFinset) x ht hx
    (fun _ : Fin 1 => ends.1) (fun _ : Fin 1 => ends.2) (fun _ : Fin 1 => ends.1)
    (fun _ => ⟨le_rfl, hends.1⟩) (fun _ => hends.2.trans_lt ht)
    (fun u hu hut => ⟨0, FiniteHullVariation.mem_endpoints (mem_erase.mpr ⟨hut, hu⟩)⟩)
    D hD hV
  dsimp only at h
  rw [hbank] at h
  have hp := h hS
  convert hp using 1
  simp [clusterVariation, FiniteHullVariation.movement, phaseMovement, hρ, F, ends]
  ring

end
end SourceCovers
