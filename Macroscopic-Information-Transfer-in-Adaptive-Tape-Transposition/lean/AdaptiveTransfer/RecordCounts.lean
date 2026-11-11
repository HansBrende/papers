import LeanMachine.SparseRecords

/-! Exact finite types for one JOINT sparse event/value record. Values are
listed in the increasing order of the selected event slots; there is no
independent logarithmic address charge per import. -/

namespace AdaptiveTransfer

open scoped BigOperators

abbrev SizedImports := LeanMachine.SizedImports
abbrev SparseImports := LeanMachine.SparseImports

-- Compatibility names; the shared record/count proof is maintained once.
alias sizedImports_card := LeanMachine.sizedImports_card
alias sparseImports_card := LeanMachine.sparseImports_card

/-- This is a finite message-counting theorem, not an assertion that the native
replay encoder has been constructed in Lean. Its injectivity obligation is
separate and visible. -/
theorem replay_message_bound {S : Type*} [Fintype S]
    (metadata exterior payload n A J : ℕ)
    (encode : S → Fin metadata × (Fin exterior → Bool) ×
      (Fin payload → Bool) × SparseImports n A J)
    (hinj : Function.Injective encode) :
    Fintype.card S ≤ metadata * (2 ^ exterior *
      (2 ^ payload * ∑ j ∈ Finset.range (J + 1), n.choose j * A ^ j)) := by
  have h := Fintype.card_le_of_injective encode hinj
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool] at h
  rw [sparseImports_card] at h
  exact h

end AdaptiveTransfer
