import LeanMachine.WholeRow.AcyclicOrder

/-!
# Open obligation: the window bound for the least row-order cost

Statement only; the first theorem is left open with `sorry` and asserts nothing yet.
With `Fintype.card R = Fintype.card J = d` it reads `(w+1) * minimumCost ρ ≤ w * d * (d+1)`:
the acyclic bound gives rate at most `w/(w+1) * (1 + 1/d)`. This is the first of the known
bounds that paper 21 cites from the synthesis paper as written and not formalized.

Check from the paper's package:
`cd Tape-Transposition-and-the-Matrix-Coding-Conjecture/lean && lake env lean ../../lean-backlog/StatementsOrderWindow.lean`

Proof plan (induction on the number of rows, last row first; integers only), in
`notes/paper21-formalization-queue.md`.
-/

namespace LeanMachine.WholeRow.AcyclicOrder

open Finset LiftOrder

variable {R J : Type*} [Fintype R] [Fintype J]

/-- Some row order has cost at most `w/(w+1)` of `|J| * (|R| + 1)`. -/
theorem exists_cost_window_le (ρ : J → Finset R) (w : ℕ) (hw : ∀ j, (ρ j).card ≤ w) :
    ∃ o : R ≃ Fin (Fintype.card R),
      (w + 1) * cost ρ o ≤ w * Fintype.card J * (Fintype.card R + 1) := by
  sorry

/-- The same bound for the least cost. -/
theorem minimumCost_window_le (ρ : J → Finset R) (w : ℕ) (hw : ∀ j, (ρ j).card ≤ w) :
    (w + 1) * minimumCost ρ ≤ w * Fintype.card J * (Fintype.card R + 1) := by
  obtain ⟨o, ho⟩ := exists_cost_window_le ρ w hw
  exact le_trans (Nat.mul_le_mul_left _ (minimumCost_le ρ o)) ho

end LeanMachine.WholeRow.AcyclicOrder
