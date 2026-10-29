import SourceCovers.ContinuationMovement
import LeanMachine.ShiftedGridUnion

set_option autoImplicit false

/-! Shared raw support of all actual output roots, before any grid is chosen.
The maximal seeds use complete older reachability, not temporal order. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped BigOperators
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

def newerLandingSeeds (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (roots : Finset ℕ) (ρ : ℕ) : Finset ℕ :=
  roots.biUnion fun u => CausalClosure.landings (values (coreBank (ρ := ρ) hc hM) u)
    (exceptionMap (newerException E))

def sharedRawSupport (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ) (roots : Finset ℕ) (ρ : ℕ) : Finset ℕ :=
  ((newerLandingSeeds hc hM E roots ρ).biUnion
    (values (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset))).image x

def sharedSeedCount (hc : HasSpanColoring K 2) {M : ℕ} (hM : 2 ≤ M)
    (E : Finset (ActualFamily xs T)) (roots : Finset ℕ) (ρ : ℕ) : ℕ :=
  ((newerLandingSeeds hc hM E roots ρ).filter fun z =>
    ∀ u ∈ newerLandingSeeds hc hM E roots ρ,
      z ∈ values (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset) u →
        u = z).card

/-- Each full source set is contained in its complete older bank plus the
same raw set shared by the whole root family. -/
theorem exactSourceBank_shared_cover (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (hE : E.card ≤ 2)
    (x : ℕ → ℕ) (roots : Finset ℕ) {t : ℕ} (ht : t ∈ roots) :
    rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t ⊆
      rawBankValues (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset) x t ∪
        sharedRawSupport hc hM E x roots ρ := by
  let B := coreBank (ρ := ρ) hc hM
  let hB := coreBank_exact hc hM hρ
  let D := (oneExceptionBank_exact hB (olderException E)).closure
  have hD (u : ℕ) : D.reach u =
      values (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset) u :=
    coe_injective ((oneExceptionBank_exact hB (olderException E) u).trans
      (exactSourceBank_exact hc hM hρ (olderException E).toList.toFinset u).symm)
  have he := continuationSuppliers_exact hB (newerException E) (olderException E) t
  rw [twoExceptionBank, two_exceptions_ordered E hE] at he
  change values (exactSourceBank (ρ := ρ) hc hM E) t =
    D.hull (D.maximal (insert t (CausalClosure.landings (values B t)
      (exceptionMap (newerException E))))) at he
  rw [D.hull_maximal, CausalClosure.hull, biUnion_insert] at he
  simp_rw [hD] at he
  rintro q hq
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hq
  rw [he] at hu
  rcases mem_union.mp hu with hu | hu
  · exact mem_union_left _ (mem_image_of_mem x hu)
  · obtain ⟨z, hz, hu⟩ := mem_biUnion.mp hu
    exact mem_union_right _ (mem_image_of_mem x
      (mem_biUnion.mpr ⟨z, mem_biUnion.mpr ⟨t, ht, hz⟩, (hD z) ▸ hu⟩))

/-- The strongest elementary count retains the complete closures at maximal
seeds. Raw-coordinate coincidences can only reduce the support. -/
theorem sharedRawSupport_card_le_sum (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (x : ℕ → ℕ) (roots : Finset ℕ) :
    (sharedRawSupport hc hM E x roots ρ).card ≤
      ∑ u ∈ (exactSourceBank_exact hc hM hρ (olderException E).toList.toFinset).closure.maximal
        (newerLandingSeeds hc hM E roots ρ),
        (values (exactSourceBank (ρ := ρ) hc hM (olderException E).toList.toFinset) u).card := by
  let D := (exactSourceBank_exact hc hM hρ (olderException E).toList.toFinset).closure
  apply card_image_le.trans
  change (D.hull (newerLandingSeeds hc hM E roots ρ)).card ≤ _
  rw [← D.hull_maximal]
  exact card_biUnion_le

theorem sharedRawSupport_card_le (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (x : ℕ → ℕ) (roots : Finset ℕ) :
    (sharedRawSupport hc hM E x roots ρ).card ≤
      ((2 * M + 3) * (2 * M + 4)) * sharedSeedCount hc hM E roots ρ := by
  apply (sharedRawSupport_card_le_sum hc hM hρ E x roots).trans
  have hcard : ∀ u, (values (exactSourceBank (ρ := ρ) hc hM
      (olderException E).toList.toFinset) u).card ≤ (2 * M + 3) * (2 * M + 4) := by
    intro u
    apply (exactSourceBank_values_card hc hM hρ _ u).trans
    apply Nat.mul_le_mul_left
    have h : (olderException E).toList.toFinset.card ≤ 1 := by
      cases olderException E <;> simp
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ 2 * M + 4) h
  exact (sum_le_sum (fun u _ => hcard u)).trans_eq (by
    simp only [sum_const, nsmul_eq_mul, sharedSeedCount, CausalClosure.maximal,
      ExactCoreBank.closure]
    exact Nat.mul_comm _ _)

/-- The payment bound holds for every grid shift, including before a
residual-cut shift is selected. The empty seed family costs zero. -/
theorem sharedRawSupport_blocks_card_le (hc : HasSpanColoring K 2) {M ρ L w : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (hw : 0 < w)
    (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ) (roots : Finset ℕ) (θ : ℕ) :
    (ShiftedGrid.blockUnion L w θ (sharedRawSupport hc hM E x roots ρ)).card ≤
      w * ((2 * M + 3) * (2 * M + 4)) * sharedSeedCount hc hM E roots ρ :=
  ((ShiftedGrid.blockUnion_card_le hw θ _).trans (min_le_right ..)).trans
    ((Nat.mul_le_mul_left w (sharedRawSupport_card_le hc hM hρ E x roots)).trans_eq
      (Nat.mul_assoc ..).symm)

end
end SourceCovers
