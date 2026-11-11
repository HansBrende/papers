import SharedDecoders.ResidualRowColumn
import SwapRigidity.Flag
import SwapRigidity.Swap
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Sharp rank-sensitive defect of a single separable baseline -/

namespace SharedDecoders.Separable

open Matrix Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

abbrev BlockIndex (r s : ℕ) := Fin r ⊕ Fin s

def blockProjection (r s : ℕ) : Matrix (BlockIndex r s) (BlockIndex r s) F :=
  Matrix.fromBlocks 1 0 0 0

@[simp] theorem blockProjection_mul_inl {r s : ℕ}
    (Z : Matrix (BlockIndex r s) (BlockIndex r s) F) (i : Fin r) (j : BlockIndex r s) :
    (blockProjection (F := F) r s * Z) (Sum.inl i) j = Z (Sum.inl i) j := by
  simp [blockProjection, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem blockProjection_mul_inr {r s : ℕ}
    (Z : Matrix (BlockIndex r s) (BlockIndex r s) F) (i : Fin s) (j : BlockIndex r s) :
    (blockProjection (F := F) r s * Z) (Sum.inr i) j = 0 := by
  simp [blockProjection, Matrix.mul_apply, Fintype.sum_sum_type]

def normalizedSpace {r s : ℕ} (D : Matrix (BlockIndex r s) (BlockIndex r s) F) :
    Submodule F (Matrix (BlockIndex r s) (BlockIndex r s) F) where
  carrier := {Y | Y = blockProjection r s * Y.transpose * D.transpose}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change X + Y = _
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
    exact congrArg₂ (· + ·) hX hY
  smul_mem' := by
    intro a X hX
    change a • X = _
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (a • ·) hX

theorem normalized_row_inr {r s : ℕ} {D : Matrix (BlockIndex r s) (BlockIndex r s) F}
    {Y : Matrix (BlockIndex r s) (BlockIndex r s) F} (hY : Y ∈ normalizedSpace D)
    (i : Fin s) (j : BlockIndex r s) : Y (Sum.inr i) j = 0 := by
  have h := congrFun (congrFun hY (Sum.inr i)) j
  simpa only [Matrix.mul_assoc, blockProjection_mul_inr] using h

theorem normalized_row_inl {r s : ℕ} {D : Matrix (BlockIndex r s) (BlockIndex r s) F}
    {Y : Matrix (BlockIndex r s) (BlockIndex r s) F} (hY : Y ∈ normalizedSpace D)
    (i : Fin r) (j : BlockIndex r s) :
    Y (Sum.inl i) j = ∑ k : Fin r, Y (Sum.inl k) (Sum.inl i) * D j (Sum.inl k) := by
  have h := congrFun (congrFun hY (Sum.inl i)) j
  change Y (Sum.inl i) j = ((blockProjection (F := F) r s * Y.transpose) * D.transpose) (Sum.inl i) j at h
  rw [Matrix.mul_assoc, blockProjection_mul_inl] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type] at h
  simpa only [normalized_row_inr hY, zero_mul, Finset.sum_const_zero, add_zero] using h

def activeBlock {r s : ℕ} (Y : Matrix (BlockIndex r s) (BlockIndex r s) F) : RowColumn.Mat r F :=
  fun i j => Y (Sum.inl i) (Sum.inl j)

/-- Restriction to the triangular coordinates of the actual active block. -/
def normalizedTriangle {r s : ℕ} (D : Matrix (BlockIndex r s) (BlockIndex r s) F) :
    normalizedSpace D →ₗ[F] (Sym2 (Fin r) → F) where
  toFun Y := RowColumn.triangle (activeBlock Y.val)
  map_add' X Y := by
    funext z
    induction z using Sym2.ind with
    | _ i j => rfl
  map_smul' a X := by
    funext z
    induction z using Sym2.ind with
    | _ i j => rfl

theorem normalizedTriangle_injective {r s : ℕ}
    (D : Matrix (BlockIndex r s) (BlockIndex r s) F) : Function.Injective (normalizedTriangle D) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have hQ : activeBlock Y.val = 0 := by
    apply RowColumn.triangle_injective_of_rows
      (fun _ v j => ∑ k : Fin r, v k * D (Sum.inl j) (Sum.inl k))
      (fun i => funext (fun j => normalized_row_inl Y.property i (Sum.inl j)))
      (fun _ => by funext j; simp)
    calc
      RowColumn.triangle (activeBlock Y.val) = 0 := hY
      _ = RowColumn.triangle 0 := by
        funext z
        induction z using Sym2.ind with
        | _ i j => rfl
  apply Subtype.ext
  funext i j
  cases i with
  | inl i =>
    rw [normalized_row_inl Y.property]
    apply Finset.sum_eq_zero
    intro k _
    have hk := congrFun (congrFun hQ k) i
    change Y.val (Sum.inl k) (Sum.inl i) = 0 at hk
    rw [hk, zero_mul]
  | inr i => exact normalized_row_inr Y.property i j

theorem normalized_finrank_le {r s : ℕ}
    (D : Matrix (BlockIndex r s) (BlockIndex r s) F) :
    finrank F (normalizedSpace D) ≤ r * (r + 1) / 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective (normalizedTriangle_injective D)
  simpa only [Module.finrank_fintype_fun_eq_card, RowColumn.sym2_card] using h

section Square
variable {d : ℕ}

def baseline (A B : Matrix (Fin d) (Fin d) F) :
    Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) F where
  toFun X := A * X * B.transpose
  map_add' _ _ := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' _ _ := by simp

def defect (A B : Matrix (Fin d) (Fin d) F) :
    Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) F :=
  SwapRigidity.swap F (Fin d) - baseline A B

theorem ker_defect_eq (A B : Matrix (Fin d) (Fin d) F) :
    (defect A B).ker = SwapRigidity.swapCode (fun _ : Unit => A) (fun _ : Unit => B) := by
  ext X
  simp [defect, baseline, SwapRigidity.mem_swapCode, LinearMap.mem_ker, sub_eq_zero]

/-- Reindex the actual normal form and transpose the actual solution. -/
def normalizeCode {r s : ℕ} (e : Fin d ≃ BlockIndex r s)
    (D : Matrix (Fin d) (Fin d) F) :
    SwapRigidity.swapCode (fun _ : Unit => (blockProjection r s).submatrix e e) (fun _ : Unit => D) →ₗ[F]
      normalizedSpace (D.submatrix e.symm e.symm) where
  toFun X := ⟨X.val.transpose.submatrix e.symm e.symm, by
    have hX : X.val.transpose = (blockProjection r s).submatrix e e * X.val * D.transpose := by
      simpa only [SwapRigidity.mem_swapCode, Finset.univ_unique, Finset.sum_singleton] using X.property
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) F => M.submatrix e.symm e.symm) hX
    change X.val.transpose.submatrix e.symm e.symm =
      blockProjection r s * (X.val.transpose.submatrix e.symm e.symm).transpose *
        (D.submatrix e.symm e.symm).transpose
    rw [← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm,
      ← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm] at hh
    simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Matrix.submatrix_id_id, Matrix.transpose_submatrix, Matrix.transpose_transpose] using hh⟩
  map_add' X Y := by apply Subtype.ext; rfl
  map_smul' a X := by apply Subtype.ext; rfl

theorem normalizeCode_injective {r s : ℕ} (e : Fin d ≃ BlockIndex r s)
    (D : Matrix (Fin d) (Fin d) F) : Function.Injective (normalizeCode e D) := by
  intro X Y h
  apply Subtype.ext
  funext i j
  have hh := congrFun (congrFun (congrArg Subtype.val h) (e j)) (e i)
  change X.val (e.symm (e i)) (e.symm (e j)) = Y.val (e.symm (e i)) (e.symm (e j)) at hh
  simpa only [Equiv.symm_apply_apply] using hh

theorem normal_code_finrank_le {r s : ℕ} (e : Fin d ≃ BlockIndex r s)
    (D : Matrix (Fin d) (Fin d) F) :
    finrank F (SwapRigidity.swapCode
      (fun _ : Unit => (blockProjection r s).submatrix e e) (fun _ : Unit => D)) ≤ r * (r + 1) / 2 :=
  (LinearMap.finrank_le_finrank_of_injective (normalizeCode_injective e D)).trans
    (normalized_finrank_le _)

/-- Rank sensitivity is derived from an actual rank normal form of the first factor. -/
theorem kernel_finrank_le_left (A B : Matrix (Fin d) (Fin d) F) :
    finrank F (defect A B).ker ≤ A.rank * (A.rank + 1) / 2 := by
  rw [ker_defect_eq]
  obtain ⟨V, U, e, hV, hU, hnorm⟩ := Matrix.exists_rank_normal_form A
  have hVdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUdet := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have he := (SwapRigidity.swapCodeEquiv (fun _ : Unit => A) (fun _ : Unit => B)
    (Matrix.mul_nonsing_inv U hUdet) (Matrix.nonsing_inv_mul V hVdet)).finrank_eq
  rw [he, hnorm]
  exact normal_code_finrank_le e (U⁻¹ * B * V⁻¹)

theorem kernel_finrank_le_right (A B : Matrix (Fin d) (Fin d) F) :
    finrank F (defect A B).ker ≤ B.rank * (B.rank + 1) / 2 := by
  rw [ker_defect_eq, SwapRigidity.finrank_swapCode_swap, ← ker_defect_eq]
  exact kernel_finrank_le_left B A

/-- The complete separable baseline has at least the stated rank defect, in every characteristic. -/
theorem rank_defect_lower (A B : Matrix (Fin d) (Fin d) F) :
    d * d - (min A.rank B.rank) * (min A.rank B.rank + 1) / 2 ≤
      finrank F (defect A B).range := by
  have hk : finrank F (defect A B).ker ≤
      (min A.rank B.rank) * (min A.rank B.rank + 1) / 2 := by
    rcases le_total A.rank B.rank with h | h
    · simpa only [min_eq_left h] using kernel_finrank_le_left A B
    · simpa only [min_eq_right h] using kernel_finrank_le_right A B
  have hn := (defect A B).finrank_range_add_finrank_ker
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hn
  omega

end Square
end SharedDecoders.Separable
