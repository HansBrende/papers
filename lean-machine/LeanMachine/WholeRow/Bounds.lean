import LeanMachine.WholeRow.Basic
import LeanMachine.FiniteProjection
import LeanMachine.SequentialDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Fin

/-! Whole-row dimension bounds from completed columns and usable frontier blocks. -/

namespace LeanMachine.WholeRow

open Module
open scoped Matrix

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Vanishing completed-column entries leave at most the other coordinates free. -/
theorem finrank_rowSpace_le_completed (A B R : Finset ι) (M : ι → Matrix ι ι F) :
    finrank F (rowSpace A B R M) ≤ Fintype.card ι - B.card := by
  apply FiniteProjection.finrank_le_compl_of_injective _ LinearMap.id B
  · intro x y hxy
    exact Subtype.ext hxy
  · intro x j hj
    exact x.property.1 j hj

/-- One injective frontier block gives a complementary bound from its known output entries. -/
theorem finrank_rowSpace_le_frontier (A B R : Finset ι) (M : ι → Matrix ι ι F)
    {r : ι} (hr : r ∈ R) (hM : Function.Injective (M r).mulVec) :
    finrank F (rowSpace A B R M) ≤ Fintype.card ι - A.card := by
  apply FiniteProjection.finrank_le_compl_of_injective _ (M r).mulVecLin A
  · intro x y hxy
    exact Subtype.ext (hM hxy)
  · intro x i hi
    exact x.property.2 r hr i hi

variable [LinearOrder ι]

omit [DecidableEq ι] in
/-- Sum the dimensions of the conditional row spaces in any prescribed order. -/
theorem finrank_rowCode_le_sum_stepSpace (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F)
    (σ : Equiv.Perm ι) :
    finrank F (rowCode ρ M) ≤ ∑ t, finrank F (stepSpace ρ M σ t) :=
  SequentialDimension.finrank_le_sum_of_prefix (rowCode ρ M) σ (stepSpace ρ M σ)
    (fun t _ hx hpre => row_mem_stepSpace σ t hx hpre)

/-- Frontier columns whose block on the current row is invertible. -/
noncomputable def invertibleFrontier (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F)
    (σ : Equiv.Perm ι) (t : ι) : Finset ι := by
  classical
  exact (frontier ρ σ t).filter fun r => IsUnit (M r (σ t)).det

/-- The second rule applies wherever at least one frontier block is invertible.
All other blocks may be singular. -/
theorem finrank_rowCode_le_local (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F)
    (σ : Equiv.Perm ι) :
    finrank F (rowCode ρ M) ≤ ∑ t, (Fintype.card ι - max (complete ρ σ t).card
      (if (invertibleFrontier ρ M σ t).Nonempty then (known σ t).card else 0)) := by
  classical
  apply (finrank_rowCode_le_sum_stepSpace ρ M σ).trans
  apply Finset.sum_le_sum
  intro t _
  have hB := finrank_rowSpace_le_completed (known σ t) (complete ρ σ t)
    (frontier ρ σ t) (fun r => M r (σ t))
  change finrank F (stepSpace ρ M σ t) ≤ _ at hB
  by_cases h : (invertibleFrontier ρ M σ t).Nonempty
  · rw [ite_eq_left h]
    obtain ⟨r, hr⟩ := h
    have hr' := Finset.mem_filter.mp hr
    have hinj := Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr hr'.2)
    have hA := finrank_rowSpace_le_frontier (known σ t) (complete ρ σ t)
      (frontier ρ σ t) (fun r => M r (σ t)) hr'.1 hinj
    change finrank F (stepSpace ρ M σ t) ≤ _ at hA
    omega
  · simpa [h] using hB

/-- At step `t` of a permutation of `Fin d`, exactly `t` rows precede the current row. -/
theorem known_card {d : ℕ} (σ : Equiv.Perm (Fin d)) (t : Fin d) :
    (known σ t).card = t.val := by
  rw [known, Finset.card_image_of_injective _ σ.injective]
  have he : Finset.univ.filter (fun u : Fin d => u < t) = Finset.Iio t := by
    ext u
    simp
  rw [he, Fin.card_Iio]

/-- Backlog C2, with its original hypotheses, over any field and including `d = 0`. -/
theorem finrank_rowCode_le {d : ℕ} (ρ : Fin d → Finset (Fin d))
    (M : Fin d → Fin d → Matrix (Fin d) (Fin d) F)
    (hM : ∀ r, ∀ s ∈ ρ r, IsUnit (M r s).det) (σ : Equiv.Perm (Fin d)) :
    finrank F (rowCode ρ M) ≤ ∑ t : Fin d,
      (d - max (complete ρ σ t).card (if (frontier ρ σ t).Nonempty then (t : ℕ) else 0)) := by
  classical
  have he (t : Fin d) : invertibleFrontier ρ M σ t = frontier ρ σ t := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    exact hM r (σ t) (Finset.mem_filter.mp hr).2.1
  simpa only [he, known_card, Fintype.card_fin] using finrank_rowCode_le_local ρ M σ

end LeanMachine.WholeRow
