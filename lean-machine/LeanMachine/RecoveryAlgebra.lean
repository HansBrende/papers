import LeanMachine.LinearRecovery
import LeanMachine.FiniteProjection
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Recovery certificates over arbitrary fields

Rank defects and coordinate restriction replace the positivity assumptions in
analytic recovery bounds. These are consequences of the existing rank identity
and coordinate-capacity lemmas, not unconditional substitutes for trace bounds.
-/

namespace LeanMachine.RecoveryAlgebra

open Module
open scoped Matrix

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

/-- An intertwining defect bounds every subspace fixed by `M`, over any field.
No invertibility is required in this form. -/
theorem two_mul_finrank_add_rank_le (C : Submodule F (n → F))
    (M L R : Matrix n n F) (hC : C ≤ LinearMap.ker (1 - M).mulVecLin) :
    2 * finrank F C + (L - R).rank ≤
      2 * Fintype.card n + (M * L - R * M).rank := by
  have h := MatrixRankCertificate.matrix_rank_identity M L R
  have hb := LinearRecovery.finrank_add_rank_le C M hC
  omega

/-- An invertible difference of labels gives a half-dimension bound with the
actual rank of the intertwining defect as its penalty. -/
theorem two_mul_finrank_le_of_isUnit (C : Submodule F (n → F))
    (M L R : Matrix n n F) (hC : C ≤ LinearMap.ker (1 - M).mulVecLin)
    (hLR : IsUnit (L - R)) :
    2 * finrank F C ≤ Fintype.card n + (M * L - R * M).rank := by
  have h := two_mul_finrank_add_rank_le C M L R hC
  rw [Matrix.rank_of_isUnit _ hLR] at h
  omega

/-- If no coordinate in `S` uses a coordinate in `S` for recovery, restriction
to the complement is injective. This includes fields of characteristic two. -/
theorem finrank_le_of_zero_square (C : Submodule F (n → F))
    (M : Matrix n n F) (hC : C ≤ LinearMap.ker (1 - M).mulVecLin)
    (S : Finset n) (hS : ∀ i ∈ S, ∀ j ∈ S, M i j = 0) :
    finrank F C ≤ Fintype.card n - S.card := by
  have hz : FiniteProjection.vanishing C Sᶜ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    funext i
    have hfix : M *ᵥ x.val = x.val := by
      have hk := LinearMap.mem_ker.mp (hC x.property)
      simpa only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
        sub_eq_zero, eq_comm] using hk
    by_cases hi : i ∈ S
    · rw [← congrFun hfix i, Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ S
      · rw [hS i hi j hj, zero_mul]
      · rw [hx j (Finset.mem_compl.mpr hj), mul_zero]
    · exact hx i (Finset.mem_compl.mpr hi)
  have h := FiniteProjection.dimension_le C Sᶜ
  rw [hz] at h
  simpa only [finrank_bot, add_zero, finrank_self, mul_one,
    Finset.card_compl] using h

/-- A bipartite recovery matrix bounds the code dimension by the smaller
part, over every field, with no sign or characteristic restriction. -/
theorem finrank_le_min_of_bipartite (C : Submodule F (n → F))
    (M : Matrix n n F) (hC : C ≤ LinearMap.ker (1 - M).mulVecLin)
    (S : Finset n) (hS : ∀ i ∈ S, ∀ j ∈ S, M i j = 0)
    (hSc : ∀ i ∈ Sᶜ, ∀ j ∈ Sᶜ, M i j = 0) :
    finrank F C ≤ min S.card (Fintype.card n - S.card) := by
  refine le_min ?_ (finrank_le_of_zero_square C M hC S hS)
  have h := finrank_le_of_zero_square C M hC Sᶜ hSc
  rw [Finset.card_compl] at h
  have hcard := Finset.card_le_univ S
  omega

/-- In characteristic `p`, all powers of the `p`-dimensional identity have
zero trace. Trace moments alone therefore cannot detect its full fixed space. -/
theorem trace_identity_pow_eq_zero (p k : ℕ) [CharP F p] :
    ((1 : Matrix (Fin p) (Fin p) F) ^ k).trace = 0 := by
  simp [CharP.cast_eq_zero]

/-- The identity used in the preceding trace collision has full fixed space. -/
theorem finrank_fixed_identity (p : ℕ) :
    finrank F (LinearMap.ker (1 - (1 : Matrix (Fin p) (Fin p) F)).mulVecLin) = p := by
  rw [sub_self, Matrix.mulVecLin_zero, LinearMap.ker_zero]
  simp

end LeanMachine.RecoveryAlgebra
