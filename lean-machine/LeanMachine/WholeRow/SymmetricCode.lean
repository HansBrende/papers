import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The symmetric-array code

Over any finite alphabet, assign one free symbol to every unordered pair
of row indices, including diagonal pairs. Column j is determined by row j.
-/

namespace LeanMachine.WholeRow.SymmetricCode

open Finset
open scoped Classical
noncomputable section

variable {R A : Type*} [Fintype R] [Fintype A]

/-- One source symbol per unordered pair, with diagonal pairs included. -/
def encode (f : Sym2 R → A) : R × R → A := fun p => f s(p.1, p.2)

omit [Fintype R] [Fintype A] in
theorem encode_injective : Function.Injective (encode (R := R) (A := A)) := by
  intro f g h
  funext p
  exact Sym2.ind (fun i j => congrFun h (i, j)) p

/-- All symmetric arrays, presented by their independent unordered-pair symbols. -/
def code (R A : Type*) [Fintype R] [Fintype A] : Finset (R × R → A) :=
  univ.map ⟨encode, encode_injective⟩

theorem symmetric {x : R × R → A} (hx : x ∈ code R A) (i j : R) :
    x (i, j) = x (j, i) := by
  obtain ⟨f, _, rfl⟩ := mem_map.mp hx
  exact congrArg f Sym2.eq_swap

/-- The pairing construction is a whole-row code of window one. -/
theorem recovery {x y : R × R → A} (hx : x ∈ code R A) (hy : y ∈ code R A)
    (j : R) (hxy : ∀ k, x (j, k) = y (j, k)) (i : R) : x (i, j) = y (i, j) := by
  rw [symmetric hx i j, symmetric hy i j]
  exact hxy i

/-- Exact cardinality over every finite alphabet; no group structure is used. -/
theorem card : (code R A).card =
    Fintype.card A ^ (Fintype.card R * (Fintype.card R + 1) / 2) := by
  simp [code, Sym2.card, Nat.choose_two_right, Nat.mul_comm]

end
end LeanMachine.WholeRow.SymmetricCode
