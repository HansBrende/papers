import SourceCovers.CoreFractionalCover
import LeanMachine.FractionalCoverBounds

set_option autoImplicit false

/-!
# Complete core covers rooted inside the computation

The exceptional-family decomposition already gives an exact union of core
orbits. Every covering root belongs to its own orbit, so completeness and
regression force all those roots to precede the source-bank root.
-/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped ENNReal

noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ} {K : Finset (ActualFamily xs T)}

/-- The original complete-core decomposition needs no extra root-range premise. -/
theorem exactSourceBank_past_core_cover (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (t : ℕ) :
    ∃ R : Finset ℕ, R.card ≤ (2 * M + 4) ^ E.card ∧
      (∀ r ∈ R, r ≤ t) ∧
      (values (exactSourceBank (ρ := ρ) hc hM E) t : Set ℕ) =
        ⋃ r ∈ R, shadowOrbit (retainedCore K M ρ) r := by
  obtain ⟨R, hR, heq⟩ := exactSourceBank_cover hc hM hρ E t
  refine ⟨R, hR, ?_, heq⟩
  intro r hr
  have hmem : r ∈ (values (exactSourceBank (ρ := ρ) hc hM E) t : Set ℕ) := by
    rw [heq]
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨hr, mem_shadowOrbit_self (retainedCore K M ρ) r⟩⟩
  exact shadowOrbit_le ((exactSourceBank_exact hc hM hρ E t).subset hmem)

/-- The actual complete raw bank is exactly a union of at most the stated
number of complete retained-core raw sets, with roots in `Fin T`. -/
theorem exactSourceBank_terminal_core_cover (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T)) (x : ℕ → ℕ)
    {t : ℕ} (ht : t < T) :
    ∃ R : Finset (Fin T), R.card ≤ (2 * M + 4) ^ E.card ∧
      (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t : Set ℕ) =
        ⋃ r ∈ R, coreRawSets (phaseSurvivors K M ρ) x r := by
  obtain ⟨R, hR, hroot, heq⟩ := exactSourceBank_past_core_cover hc hM hρ E t
  let R' : Finset (Fin T) := univ.filter fun r => r.val ∈ R
  have hcard : R'.card ≤ R.card := by
    apply card_le_card_of_injOn Fin.val
    · intro r hr
      exact (mem_filter.mp hr).2
    · intro r _ s _ h
      exact Fin.ext h
  refine ⟨R', hcard.trans hR, ?_⟩
  rw [rawBankValues, coe_image, heq]
  simp_rw [coreRawSets_phase_shadowOrbit_eq hc hρ]
  ext a
  simp only [Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨u, ⟨r, hr, hu⟩, rfl⟩
    exact ⟨⟨r, (hroot r hr).trans_lt ht⟩,
      mem_filter.mpr ⟨mem_univ _, hr⟩, u, hu, rfl⟩
  · rintro ⟨r, hr, u, hu, rfl⟩
    exact ⟨u, ⟨r.val, (mem_filter.mp hr).2, hu⟩, rfl⟩

/-- Any actual finite-root cover bounds the fractional minimum by its own
cardinality, before replacing it with the uniform exceptional-family count. -/
theorem fractionalCoreCover_le_card (I : Finset (CoreFamily K)) (x : ℕ → ℕ)
    {S : Finset ℕ} (R : Finset (Fin T))
    (hcover : (S : Set ℕ) ⊆ ⋃ r ∈ R, coreRawSets I x r) :
    fractionalCoreCover I x S ≠ ⊤ ∧ (fractionalCoreCover I x S).toReal ≤ R.card := by
  apply FractionalCover.number_le_card R
  intro a ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ha)
  obtain ⟨hi, hai⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hi, hai⟩

/-- Actual complete-bank cover weights are finite and at least one. The
terminal-core decomposition bounds them using the actual exception count. -/
theorem fractionalCoreCover_exactSourceBank_bounds (hc : HasSpanColoring K 2)
    {M ρ : ℕ} (hM : 2 ≤ M) (hρ : ρ < M) (E : Finset (ActualFamily xs T))
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    let κ := fractionalCoreCover (phaseSurvivors K M ρ) x
      (rawBankValues (exactSourceBank (ρ := ρ) hc hM E) x t)
    κ ≠ ⊤ ∧ 1 ≤ κ.toReal ∧ κ.toReal ≤ ((2 * M + 4) ^ E.card : ℕ) := by
  obtain ⟨R, hR, heq⟩ := exactSourceBank_terminal_core_cover hc hM hρ E x ht
  have hκ := fractionalCoreCover_le_card (phaseSurvivors K M ρ) x R heq.subset
  exact ⟨hκ.1, one_le_fractionalCoreCover_toReal _ x
    ⟨x t, exactSourceBank_raw_root hc hM hρ E x t⟩ hκ.1,
    hκ.2.trans (by exact_mod_cast hR)⟩

end
end SourceCovers
