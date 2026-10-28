import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card

/-! Finite incidence sums and overlap bounds from disjoint color classes. -/

namespace LeanMachine.FiniteIncidence

open Classical
open scoped BigOperators

/-- Sum weights over a finite indexed family, counting each point by its
actual multiplicity. Repeated members of the indexed family are allowed. -/
theorem sum_eq_sum_multiplicity {ι X M : Type*} [AddCommMonoid M]
    (I : Finset ι) (U : Finset X) (A : ι → Finset X) (w : X → M)
    (hA : ∀ i ∈ I, A i ⊆ U) :
    (∑ i ∈ I, ∑ x ∈ A i, w x) =
      ∑ x ∈ U, (I.filter (fun i => x ∈ A i)).card • w x := by
  calc
    _ = ∑ i ∈ I, ∑ x ∈ U, if x ∈ A i then w x else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      congr 1
      exact (Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hA i hi))).symm
    _ = _ := by
      rw [Finset.sum_comm]
      simp [← Finset.sum_filter]

/-- In a coloring with disjoint members of each color, the number of sets
containing any fixed point is at most the number of colors. -/
theorem multiplicity_le_of_coloring {ι X κ : Type*}
    (I : Finset ι) (A : ι → Finset X) (C : Finset κ) (color : ι → κ)
    (hcolor : ∀ i ∈ I, color i ∈ C)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → color i = color j → Disjoint (A i) (A j))
    (x : X) : (I.filter (fun i => x ∈ A i)).card ≤ C.card := by
  classical
  apply Finset.card_le_card_of_injOn color (fun i hi => hcolor i (Finset.mem_filter.mp hi).1) ?_
  intro i hi j hj he
  by_contra hne
  exact Finset.disjoint_left.mp
    (hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne he)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

end LeanMachine.FiniteIncidence
