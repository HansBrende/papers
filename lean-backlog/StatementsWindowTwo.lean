import LeanMachine.WholeRow.AcyclicOrder

/-!
# Open obligation: the row-order bound at window two

Statement only; the first theorem is left open with `sorry` and asserts nothing yet.
It is the ranking lemma behind the bound `d(d+1)/2 + d - 1` for whole-row codes of
window at most two, which paper 21 still cites from the synthesis paper as a written proof.
With `LeanMachine.WholeRow.OrderCode.card_le_order` it gives the bound on codes.

The closed form `windowTwoBound` is an invariant for the induction that puts last a row
helping the fewest columns. It was checked by exhaustive enumeration for up to five rows.
Plan: `notes/paper21-formalization-queue.md`, item 2′.

Check from the paper's package:
`cd Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean && lake env lean ../../lean-backlog/StatementsWindowTwo.lean`
-/

namespace LeanMachine.WholeRow.AcyclicOrder

open Finset LiftOrder

variable {R J : Type*} [Fintype R] [Fintype J]

/-- Bound for `n` rows and `m` columns, each column with at most two helper rows. -/
def windowTwoBound (n m : ℕ) : ℕ :=
  if m < n then n * (n + 1) / 2 - (n - m) else n * (n + 1) / 2 + n * (m - n) + (n - 1)

/-- Some row order has cost at most `windowTwoBound`. -/
theorem exists_cost_window_two_le (ρ : J → Finset R) (h2 : ∀ j, (ρ j).card ≤ 2) :
    ∃ o : R ≃ Fin (Fintype.card R),
      cost ρ o ≤ windowTwoBound (Fintype.card R) (Fintype.card J) := by
  sorry

/-- The square case: cost at most `d(d+1)/2 + d - 1`. -/
theorem exists_cost_window_two_square (ρ : J → Finset R) (h2 : ∀ j, (ρ j).card ≤ 2)
    (hJ : Fintype.card J = Fintype.card R) :
    ∃ o : R ≃ Fin (Fintype.card R),
      cost ρ o ≤ Fintype.card R * (Fintype.card R + 1) / 2 + (Fintype.card R - 1) := by
  obtain ⟨o, ho⟩ := exists_cost_window_two_le ρ h2
  refine ⟨o, ?_⟩
  simpa [windowTwoBound, hJ] using ho

end LeanMachine.WholeRow.AcyclicOrder
