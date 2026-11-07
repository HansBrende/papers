import TapeStorageRates.MajorityOperator
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Exact finite majority counts

The count includes empty alphabets, empty distinguished sets and zero
coordinates. No probability model, positivity or parity hypothesis is needed.
-/

namespace TapeStorageRates.Majority

open Finset
open scoped BigOperators

set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positions whose values belong to the distinguished alphabet subset. -/
def membershipPattern (P : Finset ι) {m : ℕ} (p : Fin m → ι) : Finset (Fin m) :=
  univ.filter fun i => p i ∈ P

/-- Each exact membership pattern has the expected product cardinality. -/
theorem membershipPattern_fibre_card (P : Finset ι) (m : ℕ) (S : Finset (Fin m)) :
    (univ.filter fun p : Fin m → ι => membershipPattern P p = S).card =
      P.card ^ S.card * (Fintype.card ι - P.card) ^ (m - S.card) := by
  classical
  have hfiber : (univ.filter fun p : Fin m → ι => membershipPattern P p = S) =
      Fintype.piFinset (fun i : Fin m => if i ∈ S then P else Pᶜ) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset,
      Finset.ext_iff, membershipPattern]
    constructor
    · intro h i
      by_cases hi : i ∈ S <;> simpa [hi] using h i
    · intro h i
      by_cases hi : i ∈ S <;> simpa [hi] using h i
  rw [hfiber, Fintype.card_piFinset]
  simp_rw [apply_ite]
  rw [Finset.prod_ite]
  have hcompl : (univ.filter fun i : Fin m => i ∉ S) = Sᶜ := by
    ext i
    simp
  simp [hcompl, card_compl]

private theorem goodIndices_pattern_fibre_card (P : Finset ι) (m : ℕ)
    (S : Finset (Fin m)) :
    ((goodIndices P m).filter fun p => membershipPattern P p = S).card =
      if m < 2 * S.card then
        P.card ^ S.card * (Fintype.card ι - P.card) ^ (m - S.card) else 0 := by
  classical
  by_cases hmajor : m < 2 * S.card
  · rw [ite_eq_left hmajor, ← membershipPattern_fibre_card P m S]
    congr 1
    ext p
    simp only [goodIndices, mem_filter, mem_univ, true_and]
    change (m < 2 * (membershipPattern P p).card ∧ membershipPattern P p = S) ↔
      membershipPattern P p = S
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h.symm ▸ hmajor, h⟩
  · rw [ite_eq_right hmajor, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hgood, hpattern⟩ := mem_filter.mp hp
    have h := (mem_filter.mp hgood).2
    change m < 2 * (membershipPattern P p).card at h
    exact hmajor (hpattern ▸ h)

/-- Exact binomial count of the basis indices fixed by the majority operator. -/
theorem goodIndices_card_eq_binomial_sum (P : Finset ι) (m : ℕ) :
    (goodIndices P m).card =
      ∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a),
        m.choose a * P.card ^ a * (Fintype.card ι - P.card) ^ (m - a) := by
  classical
  have hfib := card_eq_sum_card_fiberwise
    (s := goodIndices P m) (t := (univ : Finset (Fin m)).powerset)
    (f := membershipPattern P) (fun p _ => mem_powerset.mpr (subset_univ _))
  rw [hfib]
  simp_rw [goodIndices_pattern_fibre_card]
  rw [sum_powerset_apply_card (fun a => if m < 2 * a then
    P.card ^ a * (Fintype.card ι - P.card) ^ (m - a) else 0)]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : m < 2 * a <;> simp [ha, mul_assoc]

end TapeStorageRates.Majority
