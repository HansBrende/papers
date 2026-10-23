import TransposeFollowup.ExpanderShear
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! A sparse matrix cannot have many nonzero entries and small rank. The
argument chooses actual basis rows; no generic-rank or cancellation premise
is imposed, so it applies in characteristic two. -/

namespace TransposeFollowup.ExpanderShear

open scoped BigOperators
set_option autoImplicit false

theorem nnz_eq_sum_columns {α β F : Type*} [Fintype α] [Fintype β] [Zero F] [DecidableEq F]
    (M : Matrix α β F) :
    nnz M = ∑ j : β, (Finset.univ.filter (fun i => M i j ≠ 0)).card := by
  classical
  simp only [nnz, Finset.card_filter]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : M i j = 0 <;> simp [h]

theorem nnz_le_rank_mul_sq {α β K : Type*} [Fintype α] [Fintype β] [Field K] [DecidableEq K]
    (M : Matrix α β K) (Γ : ℕ)
    (hrow : ∀ i, (Finset.univ.filter (fun j => M i j ≠ 0)).card ≤ Γ)
    (hcol : ∀ j, (Finset.univ.filter (fun i => M i j ≠ 0)).card ≤ Γ) :
    nnz M ≤ M.rank * Γ ^ 2 := by
  classical
  obtain ⟨t, ht, htcard, htspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K (Set.range M.row)
  let S : Finset β := t.biUnion (fun v => Finset.univ.filter (fun j => v j ≠ 0))
  have htbound : ∀ v ∈ t,
      (Finset.univ.filter (fun j => v j ≠ 0)).card ≤ Γ := by
    intro v hv
    obtain ⟨i, rfl⟩ := ht hv
    exact hrow i
  have hScard : S.card ≤ M.rank * Γ := by
    calc
      S.card ≤ ∑ v ∈ t, (Finset.univ.filter (fun j => v j ≠ 0)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ t, Γ := Finset.sum_le_sum htbound
      _ = t.card * Γ := by simp
      _ = M.rank * Γ := by rw [htcard, Matrix.rank_eq_finrank_span_row]
  have hzero : ∀ j ∉ S, ∀ i, M i j = 0 := by
    intro j hj i
    have hmem : M.row i ∈ Submodule.span K (t : Set (β → K)) := by
      rw [htspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hz : ∀ v ∈ Submodule.span K (t : Set (β → K)), v j = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        by_contra h
        exact hj (Finset.mem_biUnion.mpr ⟨v, hv, by simp [h]⟩)
      | zero => rfl
      | add v w _ _ hv hw => simp [hv, hw]
      | smul a v _ hv => simp [hv]
    exact hz _ hmem
  have hn : nnz M ≤ S.card * Γ := by
    rw [nnz_eq_sum_columns]
    calc
      _ ≤ ∑ j : β, if j ∈ S then Γ else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j ∈ S
        · simpa only [hj, ite_true] using hcol j
        · simp [hj, hzero j hj]
      _ = S.card * Γ := by simp
  calc
    nnz M ≤ S.card * Γ := hn
    _ ≤ (M.rank * Γ) * Γ := Nat.mul_le_mul_right Γ hScard
    _ = M.rank * Γ ^ 2 := by ring

end TransposeFollowup.ExpanderShear
