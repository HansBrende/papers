import AdaptiveTransfer.ReplayCounting
import AdaptiveTransfer.IncomingReturns
import BoundedNesting.WalkDag

/-! Actual typed first-read imports inject into completed long returns.
The return is determined using the last global prior visit; the current typed
slot remains part of its triple, so different import events stay distinct. -/

namespace AdaptiveTransfer

open Transpose Finset BoundedNesting LeanMachine

noncomputable def offCarrierReturns {k : ℕ} (y : Fin k → ℕ → ℤ)
    (f : Fin k) (T H : ℕ) : Finset (Fin k × ℕ × ℕ) := by
  classical
  exact (allHops y T).filter fun e => e.1 ≠ f ∧
    ∃ u ∈ Ioo e.2.1 e.2.2, H < (y e.1 u - y e.1 e.2.1).natAbs

theorem import_has_long_return {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, t < T) (hentry : ∀ t ∈ C, entry t ≤ t)
    (slot : Fin N × OtherHeads f)
    (htag : incomingFields E N H C entry f slot ≠ none) :
    ∃ p, (slot.2.val, p, slot.1.val) ∈
      offCarrierReturns (fun h t => (E.config t).workPos h) f T H := by
  classical
  have htC : slot.1.val ∈ C := by
    by_contra hn
    simp only [incomingFields, ite_eq_right hn, ne_eq, not_true_eq_false] at htag
  have hrec : E.incomingRecord H (entry slot.1.val) slot.1.val slot.2.val ≠ none := by
    simpa only [incomingFields, ite_eq_left htC] using htag
  have hcond : H < ((E.config slot.1.val).workPos slot.2.val -
        (E.config (entry slot.1.val)).workPos slot.2.val).natAbs ∧
      (∀ u, entry slot.1.val ≤ u → u < slot.1.val →
        (E.config slot.1.val).workPos slot.2.val ≠ (E.config u).workPos slot.2.val) ∧
      ∃ u < slot.1.val,
        (E.config slot.1.val).workPos slot.2.val = (E.config u).workPos slot.2.val := by
    simpa only [ExecutionPrefix.incomingRecord, ne_eq, ite_eq_right_iff,
      Option.some_ne_none, imp_false, not_not] using hrec
  let visits := (range slot.1.val).filter fun u =>
    (E.config slot.1.val).workPos slot.2.val = (E.config u).workPos slot.2.val
  have hv : visits.Nonempty := by
    obtain ⟨u, hu, he⟩ := hcond.2.2
    exact ⟨u, mem_filter.mpr ⟨mem_range.mpr hu, he⟩⟩
  let p := visits.max' hv
  have hp := mem_filter.mp (max'_mem visits hv)
  have hpt := mem_range.mp hp.1
  have hlast : ∀ u, p < u → u < slot.1.val →
      (E.config u).workPos slot.2.val ≠ (E.config slot.1.val).workPos slot.2.val := by
    intro u hpu hut heq
    have hu : u ∈ visits := mem_filter.mpr ⟨mem_range.mpr hut, heq.symm⟩
    have := le_max' visits u hu
    omega
  have hfar : (H : ℤ) < |(E.config slot.1.val).workPos slot.2.val -
      (E.config (entry slot.1.val)).workPos slot.2.val| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hcond.1
  have hh := outside_first_read_is_long_return (y := fun t => (E.config t).workPos slot.2.val)
    (hentry _ htC) (hCT _ htC) hpt hp.2.symm
    (fun u hau hut => (hcond.2.1 u hau hut).symm) hlast hfar
  refine ⟨p, mem_filter.mpr ⟨mem_allHops.mpr hh.2.2.1, slot.2.property,
    entry slot.1.val, mem_Ioo.mpr ⟨hh.1, hh.2.1⟩, ?_⟩⟩
  have hfar' := hh.2.2.2
  rw [← Int.natCast_natAbs] at hfar'
  exact_mod_cast hfar'

/-- The actual support size is bounded by the number of actual off-carrier
long returns. This pays events jointly, including tagged blank symbols. -/
theorem incoming_support_le_returns {M : TM} {P T : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (N H : ℕ) (C : Finset ℕ)
    (entry : ℕ → ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, t < T) (hentry : ∀ t ∈ C, entry t ≤ t) :
    (recordSupport (fun _ => none) (incomingFields E N H C entry f)).card ≤
      (offCarrierReturns (fun h t => (E.config t).workPos h) f T H).card := by
  classical
  let support := recordSupport (fun _ => none) (incomingFields E N H C entry f)
  let returns := offCarrierReturns (fun h t => (E.config t).workPos h) f T H
  have hex (s : support) : ∃ p, (s.val.2.val, p, s.val.1.val) ∈ returns :=
    import_has_long_return E N H C entry f hCT hentry s.val
      ((mem_recordSupport _ _ _).mp s.property)
  let enc (s : support) : returns :=
    ⟨(s.val.2.val, (hex s).choose, s.val.1.val), (hex s).choose_spec⟩
  have hi : Function.Injective enc := by
    intro s t hst
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun v : returns => v.val.2.2) hst
    · apply Subtype.ext
      exact congrArg (fun v : returns => v.val.1) hst
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective enc hi

end AdaptiveTransfer
