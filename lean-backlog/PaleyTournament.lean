import MotionDepthCodes.Clebsch

/-!
# The seven-vertex Paley tournament beats half rate

This is the known binary Hamming-code example of Gadouleau–Riis (2011),
Example 9. We reuse the storage-code predicate and check the small finite
instance in Lean. Recovery on coordinates 2, 1, 0 proves the upper bound
over every finite alphabet, not only for linear codes.
-/

namespace LeanBacklog.PaleyTournament

open Finset MotionDepthCodes
open scoped BigOperators

def helpers : Fin 7 → Finset (Fin 7) :=
  ![{1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5},
    {1, 5, 6}, {0, 2, 6}, {0, 1, 3}]

theorem helpers_loopless (i : Fin 7) : i ∉ helpers i := by
  revert i
  decide

theorem helpers_oriented (i j : Fin 7) : j ∈ helpers i → i ∉ helpers j := by
  revert i j
  decide

/-- The seven binary recovery equations define the Hamming code. -/
def binaryCode : Finset (Fin 7 → ZMod 2) :=
  univ.filter fun x => ∀ i, x i = ∑ j ∈ helpers i, x j

theorem binaryCode_card : binaryCode.card = 16 := by decide

theorem binaryCode_isStorageCode : IsStorageCode helpers binaryCode := by
  intro x hx y hy i hxy
  have hx' := (mem_filter.mp hx).2 i
  have hy' := (mem_filter.mp hy).2 i
  exact hx'.trans ((sum_congr rfl hxy).trans hy'.symm)

/-- The four recorded coordinates determine the other three in the order
2, 1, 0. This proof uses no field operations or linearity. -/
theorem storageCode_card_le {α : Type*} [Fintype α]
    (C : Finset (Fin 7 → α)) (hC : IsStorageCode helpers C) :
    C.card ≤ Fintype.card α ^ 4 := by
  classical
  let record : C → (Fin 4 → α) := fun x => ![x.1 3, x.1 4, x.1 5, x.1 6]
  have hinj : Function.Injective record := by
    intro x y h
    have h3 : x.1 3 = y.1 3 := congrFun h 0
    have h4 : x.1 4 = y.1 4 := congrFun h 1
    have h5 : x.1 5 = y.1 5 := congrFun h 2
    have h6 : x.1 6 = y.1 6 := congrFun h 3
    have h2 : x.1 2 = y.1 2 := hC x.1 x.2 y.1 y.2 2 (by
      intro j hj
      fin_cases j <;> simp_all [helpers])
    have h1 : x.1 1 = y.1 1 := hC x.1 x.2 y.1 y.2 1 (by
      intro j hj
      fin_cases j <;> simp_all [helpers])
    have h0 : x.1 0 = y.1 0 := hC x.1 x.2 y.1 y.2 0 (by
      intro j hj
      fin_cases j <;> simp_all [helpers])
    apply Subtype.ext
    funext i
    fin_cases i <;> assumption
  simpa using Fintype.card_le_of_injective record hinj

/-- Squaring cardinalities expresses a strict half-rate violation without
rounding a logarithmic exponent. -/
theorem binaryCode_exceeds_half : 2 ^ 7 < binaryCode.card ^ 2 := by
  rw [binaryCode_card]
  decide

#print axioms helpers_loopless
#print axioms helpers_oriented
#print axioms binaryCode_card
#print axioms binaryCode_isStorageCode
#print axioms storageCode_card_le
#print axioms binaryCode_exceeds_half

end LeanBacklog.PaleyTournament
