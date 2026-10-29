import LeanMachine.FiniteIncidence
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.GroupWithZero.Nat

/-! Finite selection averages from pointwise credits on disjoint source regions. -/

namespace LeanMachine.SelectionAverage

open Finset

/-- Number of experiments selecting a coordinate. -/
def pointCount {ε X : Type*} [DecidableEq X]
    (E : Finset ε) (chosen : ε → Finset X) (z : X) : ℕ :=
  (E.filter (fun e => z ∈ chosen e)).card

/-- Count selected demanded coordinates by experiment or by coordinate. -/
theorem sum_card_inter_eq_sum_pointCount {ε X : Type*} [DecidableEq X]
    (E : Finset ε) (D : Finset X) (chosen : ε → Finset X) :
    (∑ e ∈ E, (D ∩ chosen e).card) = ∑ z ∈ D, pointCount E chosen z := by
  classical
  calc
    _ = ∑ e ∈ E, ∑ z ∈ D, if z ∈ chosen e then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro e _
      simp [← sum_filter, filter_mem_eq_inter]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro z _
      simp [← sum_filter, pointCount]

/-- Pointwise selection credits on disjoint regions give a lower bound on the
total number of selected demands, summed over all experiments. -/
theorem sum_credit_mul_card_inter_le {ε X ι : Type*} [DecidableEq X]
    (E : Finset ε) (D : Finset X) (chosen : ε → Finset X)
    (I : Finset ι) (A : ι → Finset X) (credit : ι → ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint A)
    (hcredit : ∀ i ∈ I, ∀ z ∈ D ∩ A i, credit i ≤ pointCount E chosen z) :
    (∑ i ∈ I, credit i * (D ∩ A i).card) ≤ ∑ e ∈ E, (D ∩ chosen e).card := by
  classical
  have hdisj' : (I : Set ι).PairwiseDisjoint (fun i => D ∩ A i) := by
    intro i hi k hk hik
    exact (hdisj hi hk hik).mono inter_subset_right inter_subset_right
  have hsub : I.biUnion (fun i => D ∩ A i) ⊆ D := by
    intro z hz
    obtain ⟨i, _, hzi⟩ := mem_biUnion.mp hz
    exact (mem_inter.mp hzi).1
  rw [sum_card_inter_eq_sum_pointCount]
  calc
    _ = ∑ i ∈ I, ∑ _z ∈ D ∩ A i, credit i := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ I, ∑ z ∈ D ∩ A i, pointCount E chosen z :=
      sum_le_sum fun i hi => sum_le_sum fun z hz => hcredit i hi z hz
    _ = ∑ z ∈ I.biUnion (fun i => D ∩ A i), pointCount E chosen z :=
      (sum_biUnion hdisj').symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

end LeanMachine.SelectionAverage
