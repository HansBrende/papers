import TransposeFollowup.ExpanderShearRank

/-! Explicit row and column support bounds for the shear and its cut blocks. -/
namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open Classical
set_option autoImplicit false

theorem matrix_row_support_card {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (r : Row m) :
    (Finset.univ.filter (fun c => matrix L r c ≠ 0)).card =
      match r with
      | .inl _ => 1
      | .inr j => (Finset.univ.filter (fun i => L j i ≠ 0)).card + 1 := by
  simp only [Finset.card_filter]
  cases r <;> simp only [matrix, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  all_goals simp [Matrix.one_apply, ite_not]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem matrix_col_support_card {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (c : Row m) :
    (Finset.univ.filter (fun r => matrix L r c ≠ 0)).card =
      match c with
      | .inl i => (Finset.univ.filter (fun j => L j i ≠ 0)).card + 1
      | .inr _ => 1 := by
  simp only [Finset.card_filter]
  cases c <;> simp only [matrix, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  all_goals simp [Matrix.one_apply, ite_not, add_comm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem matrix_row_support_le {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (D : ℕ)
    (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D) (r : Row m) :
    (Finset.univ.filter (fun c => matrix L r c ≠ 0)).card ≤ D + 1 := by
  rw [matrix_row_support_card]
  cases r with
  | inl i => dsimp; omega
  | inr j => exact Nat.add_le_add_right (hrow j) 1

theorem matrix_col_support_le {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (D : ℕ)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D) (c : Row m) :
    (Finset.univ.filter (fun r => matrix L r c ≠ 0)).card ≤ D + 1 := by
  rw [matrix_col_support_card]
  cases c with
  | inl i => exact Nat.add_le_add_right (hcol i) 1
  | inr j => dsimp; omega

theorem submatrix_row_support_le {α β α' β' K : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [Zero K] [DecidableEq K]
    (M : Matrix α β K) (r : α' → α) (c : β' → β)
    (hc : Function.Injective c) (i : α') :
    (Finset.univ.filter (fun j => M.submatrix r c i j ≠ 0)).card ≤
      (Finset.univ.filter (fun j => M (r i) j ≠ 0)).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_le_of_injective (fun j => ⟨c j.val, j.property⟩)
  intro a b h
  exact Subtype.ext (hc (congrArg Subtype.val h))

theorem submatrix_col_support_le {α β α' β' K : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [Zero K] [DecidableEq K]
    (M : Matrix α β K) (r : α' → α) (c : β' → β)
    (hr : Function.Injective r) (j : β') :
    (Finset.univ.filter (fun i => M.submatrix r c i j ≠ 0)).card ≤
      (Finset.univ.filter (fun i => M i (c j) ≠ 0)).card := by
  exact submatrix_row_support_le M.transpose c r hr j

theorem cross_nnz_le_rank_mul_sq {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (D : ℕ)
    (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (I J : Finset (Row m)) :
    nnz (crossMatrix (matrix L) J I) ≤ (crossMatrix (matrix L) J I).rank * (D + 1)^2 := by
  apply nnz_le_rank_mul_sq
  · intro j
    exact (submatrix_row_support_le (matrix L) Subtype.val Subtype.val
      Subtype.val_injective j).trans (matrix_row_support_le L D hrow j)
  · intro i
    exact (submatrix_col_support_le (matrix L) Subtype.val Subtype.val
      Subtype.val_injective i).trans (matrix_col_support_le L D hcol i)

end TransposeFollowup.ExpanderShear
