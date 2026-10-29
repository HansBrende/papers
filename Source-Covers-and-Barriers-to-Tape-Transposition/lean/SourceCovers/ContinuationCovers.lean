import SourceCovers.ContinuationBank

/-! Complete supplier covers and their fractional weights. The natural-root
adapter keeps roots within the actual computation, using causal regression. -/

namespace SourceCovers

open Classical Finset LeanMachine LeanMachine.SourceBank
open scoped BigOperators ENNReal
noncomputable section

variable {k T : ℕ} {xs : Fin k → ℕ → ℤ}
variable {K : Finset (ActualFamily xs T)} {B : Bank}

theorem continuationSuppliers_core_cover (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) :
    ∃ R : Finset ℕ, R.card ≤ ∑ u ∈ continuationSuppliers hB g e t,
        (1 + (values B u).card) ∧
      hB.closure.hull R = values (twoExceptionBank B g e) t := by
  rw [continuationSuppliers_exact hB g e t]
  exact hB.closure.hull_extension_core_cover _ _ (oneExceptionBank_decomposition hB e) _

theorem olderLandingSuppliers_core_cover (hB : ExactCoreBank K B)
    (g e : Option (ActualFamily xs T)) (t : ℕ) :
    ∃ R : Finset ℕ, R.card ≤ 1 + (values B t).card +
        (olderLandingSuppliers hB g e t).card ∧
      hB.closure.hull R = values (twoExceptionBank B g e) t := by
  obtain ⟨R, hR, he⟩ := hB.closure.hull_extension_core_cover
    (oneExceptionBank_exact hB g).closure (exceptionMap g)
    (oneExceptionBank_decomposition hB g) {t}
  have hR' : R.card ≤ 1 + (values B t).card := by simpa [ExactCoreBank.closure] using hR
  have he' : hB.closure.hull R = values (oneExceptionBank B g) t := by
    simpa [CausalClosure.hull, ExactCoreBank.closure] using he
  refine ⟨R ∪ olderLandingSuppliers hB g e t,
    (card_union_le ..).trans (Nat.add_le_add_right hR' _), ?_⟩
  rw [CausalClosure.hull, union_biUnion]
  change hB.closure.hull R ∪ _ = _
  rw [he', olderLandingSuppliers_exact hB g e t]
  rfl

/-- Any finite complete-core cover by past natural times is a legal cover
in the paper's `Fin T` interface. No injectivity of raw coordinates is needed. -/
theorem fractionalCoreCover_le_time_roots (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hρ : ρ < M) (x : ℕ → ℕ) {S : Finset ℕ} (R : Finset ℕ)
    (hroot : ∀ r ∈ R, r < T)
    (hcover : ∀ a ∈ S, ∃ r ∈ R, a ∈ x '' shadowOrbit (retainedCore K M ρ) r) :
    fractionalCoreCover (phaseSurvivors K M ρ) x S ≠ ⊤ ∧
      (fractionalCoreCover (phaseSurvivors K M ρ) x S).toReal ≤ R.card := by
  let R' : Finset (Fin T) := univ.filter fun r => r.val ∈ R
  have hcard : R'.card ≤ R.card := card_le_card_of_injOn Fin.val
    (fun r hr => (mem_filter.mp hr).2) (fun _ _ _ _ h => Fin.ext h)
  have h := fractionalCoreCover_le_card (phaseSurvivors K M ρ) x R' (by
    intro a ha
    obtain ⟨r, hr, har⟩ := hcover a ha
    refine Set.mem_iUnion.mpr ⟨⟨r, hroot r hr⟩, Set.mem_iUnion.mpr
      ⟨mem_filter.mpr ⟨mem_univ _, hr⟩, ?_⟩⟩
    rwa [coreRawSets_phase_shadowOrbit_eq hc hρ])
  exact ⟨h.1, h.2.trans (by exact_mod_cast hcard)⟩

theorem fractionalCoreCover_le_exact_time_cover (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hρ : ρ < M) {A D : Bank} (hA : ExactCoreBank (retainedCore K M ρ) A)
    {F : Finset (ActualFamily xs T)} (hD : ExactCoreBank F D)
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) (R : Finset ℕ)
    (he : hA.closure.hull R = values D t) :
    fractionalCoreCover (phaseSurvivors K M ρ) x (rawBankValues D x t) ≠ ⊤ ∧
      (fractionalCoreCover (phaseSurvivors K M ρ) x (rawBankValues D x t)).toReal ≤ R.card := by
  apply fractionalCoreCover_le_time_roots hc hρ x R
  · intro r hr
    have hm : r ∈ hA.closure.hull R := mem_biUnion.mpr ⟨r, hr, hA.root_mem r⟩
    exact (shadowOrbit_le ((hD t).subset (he ▸ hm))).trans_lt ht
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    rw [← he] at hu
    obtain ⟨r, hr, hur⟩ := mem_biUnion.mp hu
    exact ⟨r, hr, u, (hA r).subset hur, rfl⟩

/-- Part (a), with the actual size of each supplier's core orbit in place
of a uniform worst-case size. The order condition only establishes that the
ordered bank is the full physical source closure. -/
theorem continuationSuppliers_fractional_bound (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner))
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    let B := coreBank (ρ := ρ) hc hM
    let hB := coreBank_exact hc hM hρ
    let κ := fractionalCoreCover (phaseSurvivors K M ρ) x
      (rawBankValues (twoExceptionBank B g e) x t)
    κ ≠ ⊤ ∧ κ.toReal ≤ ∑ u ∈ continuationSuppliers hB g e t,
      (1 + ((values B u).card : ℝ)) := by
  dsimp only
  obtain ⟨R, hR, he⟩ := continuationSuppliers_core_cover (coreBank_exact hc hM hρ) g e t
  have h := fractionalCoreCover_le_exact_time_cover hc hρ (coreBank_exact hc hM hρ)
    (twoExceptionBank_exact (coreBank_exact hc hM hρ) g e horder) x ht R he
  exact ⟨h.1, h.2.trans (by exact_mod_cast hR)⟩

/-- Part (b), likewise retaining the actual core-orbit size at the root. -/
theorem olderLandingSuppliers_fractional_bound (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner))
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    let B := coreBank (ρ := ρ) hc hM
    let hB := coreBank_exact hc hM hρ
    let κ := fractionalCoreCover (phaseSurvivors K M ρ) x
      (rawBankValues (twoExceptionBank B g e) x t)
    κ ≠ ⊤ ∧ κ.toReal ≤ 1 + ((values B t).card : ℝ) +
      (olderLandingSuppliers hB g e t).card := by
  dsimp only
  obtain ⟨R, hR, he⟩ := olderLandingSuppliers_core_cover (coreBank_exact hc hM hρ) g e t
  have h := fractionalCoreCover_le_exact_time_cover hc hρ (coreBank_exact hc hM hρ)
    (twoExceptionBank_exact (coreBank_exact hc hM hρ) g e horder) x ht R he
  exact ⟨h.1, h.2.trans (by exact_mod_cast hR)⟩

/-- Both original bounds follow from the actual-cardinality statements;
the two candidate covers can be compared without choosing between them. -/
theorem continuation_fractional_bounds (hc : HasSpanColoring K 2) {M ρ : ℕ}
    (hM : 2 ≤ M) (hρ : ρ < M) (g e : Option (ActualFamily xs T))
    (horder : (g.toList ++ e.toList).Pairwise (fun a b => b.owner ≤ a.owner))
    (x : ℕ → ℕ) {t : ℕ} (ht : t < T) :
    let B := coreBank (ρ := ρ) hc hM
    let hB := coreBank_exact hc hM hρ
    let κ := fractionalCoreCover (phaseSurvivors K M ρ) x
      (rawBankValues (twoExceptionBank B g e) x t)
    κ ≠ ⊤ ∧
      κ.toReal ≤ (2 * (M : ℝ) + 4) * (continuationSuppliers hB g e t).card ∧
      κ.toReal ≤ 2 * (M : ℝ) + 4 + (olderLandingSuppliers hB g e t).card := by
  dsimp only
  have ha := continuationSuppliers_fractional_bound hc hM hρ g e horder x ht
  have hb := olderLandingSuppliers_fractional_bound hc hM hρ g e horder x ht
  have hsize (u : ℕ) : ((values (coreBank (ρ := ρ) hc hM) u).card : ℝ) ≤ 2 * M + 3 := by
    exact_mod_cast coreBank_values_card hc hM hρ u
  refine ⟨ha.1, ha.2.trans ?_, hb.2.trans (by have := hsize t; linarith)⟩
  calc
    _ ≤ ∑ _u ∈ continuationSuppliers (coreBank_exact hc hM hρ) g e t,
        (2 * (M : ℝ) + 4) := sum_le_sum fun u _ => by have := hsize u; linarith
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]

end
end SourceCovers
