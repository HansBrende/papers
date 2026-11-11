import AdaptiveTransfer.GetterCounting
import AdaptiveTransfer.ReturnImports

/-! The selected correction payload injects into the actual whole-run getter
failures on long consecutive returns, preserving the typed endpoint (time,head).
-/

namespace AdaptiveTransfer.Getter

open Transpose Finset LeanMachine

variable {M : TM} {U Λ : Type*} {v R P T : ℕ} {X : Fin P → Bool}

noncomputable def errorReturns (E : ExecutionPrefix M (List.ofFn X) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (f : Fin M.k) (label : Λ) (H : ℕ) :
    Finset (Fin M.k × ℕ × ℕ) :=
  (offCarrierReturns (fun h t => (E.config t).workPos h) f T H).filter fun e =>
    (E.config e.2.2).work e.1 ((E.config e.2.2).workPos e.1) ≠
      prediction A G f label (List.ofFn X) e.2.2 e.1

theorem errorRecord_ne_none_iff (E : ExecutionPrefix M (List.ofFn X) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (f : Fin M.k)
    (label : Λ) (H a t : ℕ) (h : Fin M.k) :
    errorRecord E A G f label H a t h ≠ none ↔
      E.incomingRecord H a t h ≠ none ∧
      (E.config t).work h ((E.config t).workPos h) ≠ prediction A G f label (List.ofFn X) t h := by
  unfold errorRecord
  cases hr : E.incomingRecord H a t h with
  | none => simp
  | some value =>
    have hv : value = (E.config t).work h ((E.config t).workPos h) := by
      unfold ExecutionPrefix.incomingRecord at hr
      split at hr
      · exact (Option.some.inj hr).symm
      · contradiction
    simp only [Option.bind_some]
    by_cases hh : value = prediction A G f label (List.ofFn X) t h <;> simp_all

theorem correction_has_error_return (E : ExecutionPrefix M (List.ofFn X) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (label : Λ)
    (N H : ℕ) (C : Finset ℕ) (entry : ℕ → ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, t < T) (hentry : ∀ t ∈ C, entry t ≤ t)
    (slot : Fin N × OtherHeads f)
    (htag : errorFields E A G label N H C entry f slot ≠ none) :
    ∃ a, (slot.2.val, a, slot.1.val) ∈ errorReturns E A G f label H := by
  classical
  have htC : slot.1.val ∈ C := by
    by_contra hn
    simp only [errorFields, ite_eq_right hn, ne_eq, not_true_eq_false] at htag
  have he : errorRecord E A G f label H (entry slot.1.val) slot.1.val slot.2.val ≠ none := by
    simpa only [errorFields, ite_eq_left htC] using htag
  have hh := (errorRecord_ne_none_iff E A G f label H _ _ _).mp he
  have hi : incomingFields E N H C entry f slot ≠ none := by
    simpa only [incomingFields, ite_eq_left htC] using hh.1
  obtain ⟨a, ha⟩ := import_has_long_return E N H C entry f hCT hentry slot hi
  exact ⟨a, mem_filter.mpr ⟨ha, hh.2⟩⟩

/-- The actual whole-run discrepancy budget pays every selected error slot,
including an erroneous prediction of a blank symbol. -/
theorem error_support_le_returns (E : ExecutionPrefix M (List.ofFn X) T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (label : Λ)
    (N H : ℕ) (C : Finset ℕ) (entry : ℕ → ℕ) (f : Fin M.k)
    (hCT : ∀ t ∈ C, t < T) (hentry : ∀ t ∈ C, entry t ≤ t) :
    (recordSupport (fun _ => none) (errorFields E A G label N H C entry f)).card ≤
      (errorReturns E A G f label H).card := by
  classical
  let support := recordSupport (fun _ => none) (errorFields E A G label N H C entry f)
  let returns := errorReturns E A G f label H
  have hex (s : support) : ∃ a, (s.val.2.val, a, s.val.1.val) ∈ returns :=
    correction_has_error_return E A G label N H C entry f hCT hentry s.val
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

end AdaptiveTransfer.Getter
