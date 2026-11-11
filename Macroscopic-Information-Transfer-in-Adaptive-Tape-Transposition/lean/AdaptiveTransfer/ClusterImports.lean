import AdaptiveTransfer.ClusterSnapshots
import AdaptiveTransfer.ReturnImports

/-! Actual complementary-head import events inject into original cluster
complement long returns. The typed slots still include every head/time, so
one sparse record pays events jointly even when their imported value is blank. -/

namespace AdaptiveTransfer
open Transpose Finset BoundedNesting LeanMachine

noncomputable def clusterIncomingFields {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (cluster : Finset (Fin M.k)) : Fin N × Fin M.k → Option (Fin (M.g + 1)) :=
  fun slot => if slot.1.val ∈ C ∧ slot.2 ∉ cluster then
    E.incomingRecord H (entry slot.1.val) slot.1.val slot.2 else none

theorem cluster_import_has_long_return {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (cluster : Finset (Fin M.k))
    (hCT : ∀ t ∈ C, t < T) (hentry : ∀ t ∈ C, entry t ≤ t)
    (slot : Fin N × Fin M.k)
    (htag : clusterIncomingFields E N H C entry cluster slot ≠ none) :
    ∃ p, (slot.2, p, slot.1.val) ∈
      offClusterReturns (fun h t => (E.config t).workPos h) cluster T H := by
  classical
  have hc : slot.1.val ∈ C ∧ slot.2 ∉ cluster := by
    by_contra hn
    simp only [clusterIncomingFields, ite_eq_right hn, ne_eq, not_true_eq_false] at htag
  have htC := hc.1
  have hrec : E.incomingRecord H (entry slot.1.val) slot.1.val slot.2 ≠ none := by
    simpa only [clusterIncomingFields, ite_eq_left hc] using htag
  have hcond : H < ((E.config slot.1.val).workPos slot.2 -
        (E.config (entry slot.1.val)).workPos slot.2).natAbs ∧
      (∀ u, entry slot.1.val ≤ u → u < slot.1.val →
        (E.config slot.1.val).workPos slot.2 ≠ (E.config u).workPos slot.2) ∧
      ∃ u < slot.1.val,
        (E.config slot.1.val).workPos slot.2 = (E.config u).workPos slot.2 := by
    simpa only [ExecutionPrefix.incomingRecord, ne_eq, ite_eq_right_iff,
      Option.some_ne_none, imp_false, not_not] using hrec
  let visits := (range slot.1.val).filter fun u =>
    (E.config slot.1.val).workPos slot.2 = (E.config u).workPos slot.2
  have hv : visits.Nonempty := by
    obtain ⟨u, hu, he⟩ := hcond.2.2
    exact ⟨u, mem_filter.mpr ⟨mem_range.mpr hu, he⟩⟩
  let p := visits.max' hv
  have hp := mem_filter.mp (max'_mem visits hv)
  have hpt := mem_range.mp hp.1
  have hlast : ∀ u, p < u → u < slot.1.val →
      (E.config u).workPos slot.2 ≠ (E.config slot.1.val).workPos slot.2 := by
    intro u hpu hut heq
    have hu : u ∈ visits := mem_filter.mpr ⟨mem_range.mpr hut, heq.symm⟩
    have := le_max' visits u hu
    omega
  have hfar : (H : ℤ) < |(E.config slot.1.val).workPos slot.2 -
      (E.config (entry slot.1.val)).workPos slot.2| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hcond.1
  have hh := outside_first_read_is_long_return (y := fun t => (E.config t).workPos slot.2)
    (hentry _ htC) (hCT _ htC) hpt hp.2.symm
    (fun u hau hut => (hcond.2.1 u hau hut).symm) hlast hfar
  refine ⟨p, mem_filter.mpr ⟨mem_allHops.mpr hh.2.2.1, hc.2,
    entry slot.1.val, mem_Ioo.mpr ⟨hh.1, hh.2.1⟩, ?_⟩⟩
  have hfar' := hh.2.2.2
  rw [← Int.natCast_natAbs] at hfar'
  exact_mod_cast hfar'

/-- The actual support size is bounded by the number of actual off-carrier
long returns. This pays events jointly, including tagged blank symbols. -/
theorem cluster_incoming_support_le_returns {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (cluster : Finset (Fin M.k))
    (hCT : ∀ t ∈ C, t < T) (hentry : ∀ t ∈ C, entry t ≤ t) :
    (recordSupport (fun _ => none) (clusterIncomingFields E N H C entry cluster)).card ≤
      (offClusterReturns (fun h t => (E.config t).workPos h) cluster T H).card := by
  classical
  let support := recordSupport (fun _ => none) (clusterIncomingFields E N H C entry cluster)
  let returns := offClusterReturns (fun h t => (E.config t).workPos h) cluster T H
  have hex (s : support) : ∃ p, (s.val.2, p, s.val.1.val) ∈ returns :=
    cluster_import_has_long_return E N H C entry cluster hCT hentry s.val
      ((mem_recordSupport _ _ _).mp s.property)
  let enc (s : support) : returns :=
    ⟨(s.val.2, (hex s).choose, s.val.1.val), (hex s).choose_spec⟩
  have hi : Function.Injective enc := by
    intro s t hst
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun v : returns => v.val.2.2) hst
    · exact congrArg (fun v : returns => v.val.1) hst
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective enc hi

end AdaptiveTransfer
