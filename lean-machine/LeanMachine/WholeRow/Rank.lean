import LeanMachine.WholeRow.Bounds
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The stacked frontier constraints give a rank bound even when blocks are singular. -/

namespace LeanMachine.WholeRow

open Module
open scoped Matrix

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Stack the blocks' rows in `A`, after removing the columns in `B`.
The first row index chooses the block, and the second chooses its row. -/
def constraintMatrix (A B R : Finset ι) (M : ι → Matrix ι ι F) :
    Matrix (R × A) (Bᶜ : Finset ι) F :=
  fun p j => M p.1.val p.2.val j.val

/-- A candidate row, restricted to the unresolved coordinates, lies in the
kernel of the stacked matrix. -/
theorem restrict_mem_constraint_ker (A B R : Finset ι) (M : ι → Matrix ι ι F)
    (x : rowSpace A B R M) :
    (fun j : (Bᶜ : Finset ι) => x.val j.val) ∈ LinearMap.ker (constraintMatrix A B R M).mulVecLin := by
  apply LinearMap.mem_ker.mpr
  funext p
  change (∑ j : (Bᶜ : Finset ι), M p.1.val p.2.val j.val * x.val j.val) = 0
  rw [Finset.sum_coe_sort (Bᶜ) (fun j : ι => M p.1.val p.2.val j * x.val j)]
  have he : (∑ j ∈ Bᶜ, M p.1.val p.2.val j * x.val j) =
      ∑ j, M p.1.val p.2.val j * x.val j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hjB : j ∈ B := by simpa using hj
    simp [x.property.1 j hjB]
  rw [he]
  exact x.property.2 p.1.val p.1.property p.2.val p.2.property

/-- The stacked rank and the remaining row dimension together fit in the
unresolved coordinate space. No invertibility hypothesis is needed. -/
theorem finrank_rowSpace_add_rank_le (A B R : Finset ι) (M : ι → Matrix ι ι F) :
    finrank F (rowSpace A B R M) + (constraintMatrix A B R M).rank ≤ Fintype.card ι - B.card := by
  let Y := constraintMatrix A B R M
  let f : rowSpace A B R M →ₗ[F] LinearMap.ker Y.mulVecLin :=
    { toFun := fun x => ⟨fun j => x.val j.val, restrict_mem_constraint_ker A B R M x⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ B
    · exact (x.property.1 j hj).trans (y.property.1 j hj).symm
    · exact congrFun (congrArg Subtype.val hxy) ⟨j, Finset.mem_compl.mpr hj⟩
  have hd := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hn := Y.mulVecLin.finrank_range_add_finrank_ker
  change Y.rank + finrank F (LinearMap.ker Y.mulVecLin) = _ at hn
  rw [Module.finrank_pi] at hn
  simp only [Fintype.card_coe, Finset.card_compl] at hn
  change finrank F (rowSpace A B R M) + Y.rank ≤ _
  omega

variable [LinearOrder ι]

/-- The matrix `Y_t` in C1: frontier blocks, known rows, and unresolved columns. -/
def stepMatrix (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F) (σ : Equiv.Perm ι) (t : ι) :
    Matrix ((frontier ρ σ t) × (known σ t)) ((complete ρ σ t)ᶜ : Finset ι) F :=
  constraintMatrix (known σ t) (complete ρ σ t) (frontier ρ σ t) (fun r => M r (σ t))

/-- Backlog C1: subtract the full joint frontier rank at every step, over any field. -/
theorem finrank_rowCode_le_rank (ρ : ι → Finset ι) (M : ι → ι → Matrix ι ι F)
    (σ : Equiv.Perm ι) :
    finrank F (rowCode ρ M) ≤
      ∑ t, (Fintype.card ι - (complete ρ σ t).card - (stepMatrix ρ M σ t).rank) := by
  apply (finrank_rowCode_le_sum_stepSpace ρ M σ).trans
  apply Finset.sum_le_sum
  intro t _
  have h := finrank_rowSpace_add_rank_le (known σ t) (complete ρ σ t)
    (frontier ρ σ t) (fun r => M r (σ t))
  change finrank F (stepSpace ρ M σ t) + (stepMatrix ρ M σ t).rank ≤ _ at h
  omega

end LeanMachine.WholeRow
