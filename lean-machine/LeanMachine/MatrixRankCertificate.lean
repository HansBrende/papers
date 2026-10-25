import LeanMachine.RankCertificate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.Flat.Basic

/-!
# Matrix rank certificates

Finite-dimensional tensor-product ranks multiply. The matrix formulation uses
arbitrary finite row and column index types and arbitrary fields.
-/

open Module
open scoped TensorProduct Kronecker BigOperators

namespace LeanMachine.MatrixRankCertificate

variable {F : Type*} [Field F]

/-- The rank of a tensor product of linear maps is the product of their ranks. -/
theorem finrank_range_tensorProduct_map
    {U V W Z : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup W] [AddCommGroup Z] [Module F U] [Module F V]
    [Module F W] [Module F Z] [FiniteDimensional F U]
    [FiniteDimensional F V] [FiniteDimensional F W] [FiniteDimensional F Z]
    (f : U →ₗ[F] V) (g : W →ₗ[F] Z) :
    finrank F (LinearMap.range (TensorProduct.map f g)) =
      finrank F (LinearMap.range f) * finrank F (LinearMap.range g) := by
  rw [TensorProduct.range_map, ← TensorProduct.range_mapIncl]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _)]
  exact Module.finrank_tensorProduct

/-- Kronecker-product ranks multiply over an arbitrary field. -/
theorem rank_kronecker {ι κ ι' κ' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (A : Matrix ι' ι F) (B : Matrix κ' κ F) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin (A ⊗ₖ B)
    ((Pi.basisFun F ι').tensorProduct (Pi.basisFun F κ'))
    ((Pi.basisFun F ι).tensorProduct (Pi.basisFun F κ))]
  rw [Matrix.toLin_kronecker, finrank_range_tensorProduct_map]
  rw [← Matrix.rank_eq_finrank_range_toLin, ← Matrix.rank_eq_finrank_range_toLin]

/-- The rank of a finite block-diagonal linear map is the sum of its block ranks. -/
theorem finrank_range_piMap {ι : Type*} [Fintype ι]
    {U V : ι → Type*} [∀ i, AddCommGroup (U i)] [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (U i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (f : ∀ i, U i →ₗ[F] V i) :
    finrank F (LinearMap.range (LinearMap.piMap f)) =
      ∑ i, finrank F (LinearMap.range (f i)) := by
  classical
  let e : LinearMap.range (LinearMap.piMap f) ≃ₗ[F]
      (∀ i, LinearMap.range (f i)) :=
    { toFun := fun x i => ⟨x.val i, by
        rcases x.property with ⟨y, hy⟩
        exact ⟨y i, congrFun hy i⟩⟩
      invFun := fun x => ⟨fun i => (x i).val, by
        choose y hy using fun i => (x i).property
        exact ⟨y, funext hy⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

/-- Rank subadditivity for rectangular matrices. -/
theorem rank_add_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ F) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a finite sum is at most the sum of the ranks. -/
theorem rank_sum_le {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (s : Finset σ) (A : σ → Matrix ι κ F) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    simpa only [Finset.sum_cons] using
      (rank_add_le (A i) (∑ j ∈ s, A j)).trans (Nat.add_le_add_left ih _)

/-- Assemble a rectangular array of matrices into one matrix. -/
def blocks {C D I J : Type*} (B : C → D → Matrix I J F) :
    Matrix (C × I) (D × J) F := fun qi pj => B qi.1 pj.1 qi.2 pj.2

/-- Assemble a block-diagonal matrix, with the coordinate index first. -/
def diagonalBlocks {C I J : Type*} [DecidableEq C] (B : C → Matrix I J F) :
    Matrix (C × I) (C × J) F :=
  blocks fun q p => if q = p then B q else 0

private def curryEquiv (C I : Type*) : ((C × I) → F) ≃ₗ[F] (C → I → F) where
  toFun x q i := x (q, i)
  invFun x qi := x qi.1 qi.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The rank of a block-diagonal matrix is the sum of the ranks of its blocks. -/
theorem rank_diagonalBlocks {C I J : Type*}
    [Fintype C] [Fintype I] [Fintype J] [DecidableEq C]
    (B : C → Matrix I J F) :
    (diagonalBlocks B).rank = ∑ q, (B q).rank := by
  have h : (diagonalBlocks B).mulVecLin =
      (curryEquiv (F := F) C I).symm.toLinearMap ∘ₗ
        (LinearMap.piMap fun q => (B q).mulVecLin) ∘ₗ
        (curryEquiv (F := F) C J).toLinearMap := by
    ext x ⟨q, i⟩
    simp only [diagonalBlocks, blocks, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.coe_piMap, curryEquiv]
    rw [Finset.sum_eq_single q]
    · simp [Matrix.mulVec, dotProduct]
    · intro p _ hp; simp [Ne.symm hp]
    · simp
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq,
    finrank_range_piMap]
  rfl

private theorem rank_single_le_one {C D : Type*} [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] (q : C) (p : D) :
    (Matrix.single q p (1 : F)).rank ≤ 1 := by
  refine (Matrix.rank_le_card_of_support_subset _ {q} ?_).trans_eq (Finset.card_singleton _)
  intro r hr
  simp only [Finset.coe_singleton, Set.mem_singleton_iff]
  by_contra h
  apply hr
  ext j
  exact Matrix.single_apply_of_row_ne (Ne.symm h) _ _ _

/-- The rank of a block matrix is at most the sum of the block ranks. -/
theorem rank_blocks_le {C D I J : Type*}
    [Fintype C] [Fintype D] [Fintype I] [Fintype J]
    (B : C → D → Matrix I J F) :
    (blocks B).rank ≤ ∑ q, ∑ p, (B q p).rank := by
  classical
  have h : blocks B = ∑ q, ∑ p, Matrix.single q p (1 : F) ⊗ₖ B q p := by
    ext ⟨q, i⟩ ⟨p, j⟩
    simp [blocks, Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Matrix.single_apply, ite_and]
  rw [h]
  apply (rank_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  apply (rank_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  rw [rank_kronecker]
  simpa using Nat.mul_le_mul_right (B q p).rank (rank_single_le_one (F := F) q p)

private theorem blocks_mul_diagonalBlocks {C D I J K : Type*}
    [Fintype D] [Fintype J] [DecidableEq D]
    (B : C → D → Matrix I J F) (Z : D → Matrix J K F) :
    blocks B * diagonalBlocks Z = blocks (fun q p => B q p * Z p) := by
  ext ⟨q, i⟩ ⟨p, j⟩
  simp only [Matrix.mul_apply, blocks, diagonalBlocks, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p]
  · simp
  · intro r _ hr; simp [hr]
  · simp

private theorem diagonalBlocks_mul_blocks {C D I J K : Type*}
    [Fintype C] [Fintype J] [DecidableEq C]
    (Z : C → Matrix I J F) (B : C → D → Matrix J K F) :
    diagonalBlocks Z * blocks B = blocks (fun q p => Z q * B q p) := by
  ext ⟨q, i⟩ ⟨p, j⟩
  simp only [Matrix.mul_apply, blocks, diagonalBlocks, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single q]
  · simp
  · intro r _ hr; simp [Ne.symm hr]
  · simp

private theorem blocks_sub {C D I J : Type*}
    (B Z : C → D → Matrix I J F) :
    blocks B - blocks Z = blocks (fun q p => B q p - Z q p) := rfl

private theorem diagonalBlocks_sub {C I J : Type*} [DecidableEq C]
    (B Z : C → Matrix I J F) :
    diagonalBlocks B - diagonalBlocks Z = diagonalBlocks (fun q => B q - Z q) := by
  ext ⟨q, i⟩ ⟨p, j⟩
  by_cases h : q = p <;> simp [diagonalBlocks, blocks, h]

private theorem kronecker_sub_right {I J M N : Type*}
    (A : Matrix I J F) (B C : Matrix M N F) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨i, u⟩ ⟨j, v⟩
  exact mul_sub _ _ _

private theorem kronecker_sub_left {I J M N : Type*}
    (A B : Matrix I J F) (C : Matrix M N F) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, u⟩ ⟨j, v⟩
  exact sub_mul _ _ _

/-- The rank-identity certificate written directly for square matrices. -/
theorem matrix_rank_identity {I : Type*} [Fintype I] [DecidableEq I]
    (A L R : Matrix I I F) :
    (L - R).rank ≤ (A * L - R * A).rank + 2 * (1 - A).rank := by
  have h := RankCertificate.rank_identity (Matrix.toLinAlgEquiv' A)
    (Matrix.toLinAlgEquiv' L) (Matrix.toLinAlgEquiv' R)
  let ρ := fun f : Module.End F (I → F) => finrank F (LinearMap.range f)
  have h₁ : (L - R).rank = ρ (Matrix.toLinAlgEquiv' L - Matrix.toLinAlgEquiv' R) :=
    congrArg ρ (map_sub Matrix.toLinAlgEquiv' L R)
  have h₂ : (A * L - R * A).rank = ρ
      (Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' L -
        Matrix.toLinAlgEquiv' R * Matrix.toLinAlgEquiv' A) := by
    apply congrArg ρ
    change Matrix.toLinAlgEquiv' (A * L - R * A) = _
    rw [map_sub, map_mul, map_mul]
  have h₃ : (1 - A).rank = ρ (1 - Matrix.toLinAlgEquiv' A) := by
    apply congrArg ρ
    change Matrix.toLinAlgEquiv' (1 - A) = _
    rw [map_sub, map_one]
  rw [h₁, h₂, h₃]
  exact h

/-- Tensor amplification, retaining the coordinate index first. -/
def amplify {C T M : Type*} [DecidableEq M] (A : Matrix (C × T) (C × T) F) :
    Matrix (C × (T × M)) (C × (T × M)) F :=
  (A ⊗ₖ (1 : Matrix M M F)).submatrix
    (Equiv.prodAssoc C T M).symm (Equiv.prodAssoc C T M).symm

private theorem amplify_eq_blocks {C T M : Type*} [DecidableEq M]
    (A : Matrix (C × T) (C × T) F) :
    amplify (M := M) A = blocks fun q p =>
      (A.submatrix (Prod.mk q) (Prod.mk p)) ⊗ₖ (1 : Matrix M M F) := rfl

private theorem one_sub_amplify {C T M : Type*}
    [DecidableEq C] [DecidableEq T] [DecidableEq M]
    (A : Matrix (C × T) (C × T) F) :
    1 - amplify (M := M) A = amplify (M := M) (1 - A) := by
  unfold amplify
  rw [kronecker_sub_left, Matrix.one_kronecker_one]
  ext ⟨q, i, u⟩ ⟨p, j, v⟩
  simp [Matrix.one_apply, and_assoc]

/-- Tensor amplification multiplies the rank by the witness dimension. -/
theorem rank_amplify {C T M : Type*} [Fintype C] [Fintype T] [Fintype M]
    [DecidableEq M] (A : Matrix (C × T) (C × T) F) :
    (amplify (M := M) A).rank = A.rank * Fintype.card M := by
  rw [amplify, Matrix.rank_submatrix, rank_kronecker, Matrix.rank_one]

/-- The finite matrix-label certificate, in additive natural-number form.
There is no positivity or invertibility requirement on the labels or on `A`. -/
theorem matrix_label_certificate {C T M : Type*}
    [Fintype C] [Fintype T] [Fintype M]
    [DecidableEq C] [DecidableEq T] [DecidableEq M]
    (A : Matrix (C × T) (C × T) F) (X Y : C → Matrix M M F) :
    Fintype.card T * (∑ p, (X p - Y p).rank) ≤
      (∑ q, ∑ p, (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank) +
        2 * Fintype.card M * (1 - A).rank := by
  let L := diagonalBlocks fun p => (1 : Matrix T T F) ⊗ₖ X p
  let R := diagonalBlocks fun q => (1 : Matrix T T F) ⊗ₖ Y q
  have hdiff : (L - R).rank = Fintype.card T * (∑ p, (X p - Y p).rank) := by
    dsimp [L, R]
    rw [diagonalBlocks_sub]
    simp_rw [← kronecker_sub_right, rank_diagonalBlocks, rank_kronecker,
      Matrix.rank_one]
    exact (Finset.mul_sum _ _ _).symm
  have hdefect : amplify (M := M) A * L - R * amplify (M := M) A =
      blocks (fun q p => (A.submatrix (Prod.mk q) (Prod.mk p)) ⊗ₖ (X p - Y q)) := by
    dsimp [L, R]
    rw [amplify_eq_blocks, blocks_mul_diagonalBlocks, diagonalBlocks_mul_blocks,
      blocks_sub]
    congr 1
    funext q p
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, kronecker_sub_right]
  have hbound : (amplify (M := M) A * L - R * amplify (M := M) A).rank ≤
      ∑ q, ∑ p, (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank := by
    rw [hdefect]
    simpa only [rank_kronecker] using
      rank_blocks_le (fun q p => (A.submatrix (Prod.mk q) (Prod.mk p)) ⊗ₖ (X p - Y q))
  have h := matrix_rank_identity (amplify (M := M) A) L R
  rw [hdiff, one_sub_amplify, rank_amplify] at h
  calc
    _ ≤ (amplify (M := M) A * L - R * amplify (M := M) A).rank +
        2 * ((1 - A).rank * Fintype.card M) := h
    _ ≤ _ := by
      simpa only [Nat.mul_assoc, Nat.mul_comm (1 - A).rank] using
        Nat.add_le_add_right hbound (2 * ((1 - A).rank * Fintype.card M))

/-- The matrix-label certificate with the defect sum restricted to a support relation. -/
theorem supported_matrix_label_certificate {C T M : Type*}
    [Fintype C] [Fintype T] [Fintype M]
    [DecidableEq C] [DecidableEq T] [DecidableEq M]
    (E : C → C → Prop) [DecidableRel E]
    (A : Matrix (C × T) (C × T) F)
    (hA : ∀ q p, ¬ E p q → A.submatrix (Prod.mk q) (Prod.mk p) = 0)
    (X Y : C → Matrix M M F) :
    Fintype.card T * (∑ p, (X p - Y p).rank) ≤
      (∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
        (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank) +
      2 * Fintype.card M * (1 - A).rank := by
  have hs : (∑ q, ∑ p, (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank) =
      ∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
        (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank := by
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : E p q
    · simp [hp]
    · simp [hp, hA q p hp]
  rw [← hs]
  exact matrix_label_certificate A X Y

private theorem rank_map_diagonal {K I : Type*} [Field K] [Fintype I]
    [DecidableEq I] (f : F →+* K) (d : I → F) :
    ((Matrix.diagonal d).map f).rank = (Matrix.diagonal d).rank := by
  classical
  rw [Matrix.diagonal_map (map_zero f), Matrix.rank_diagonal, Matrix.rank_diagonal]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => by
    constructor
    · intro hn hz; apply hn; rw [hz, map_zero]
    · intro hn hz; apply hn; apply f.injective; simpa only [map_zero] using hz

/-- The rank of a square matrix is unchanged under any embedding of fields.
No finiteness assumption is imposed on the field extension. -/
theorem rank_map_field {K I : Type*} [Field K] [Fintype I]
    [DecidableEq I] (f : F →+* K) (A : Matrix I I F) :
    (A.map f).rank = A.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form A
  let D : Matrix (Fin A.rank ⊕ Fin (Fintype.card I - A.rank))
      (Fin A.rank ⊕ Fin (Fintype.card I - A.rank)) F := Matrix.fromBlocks 1 0 0 0
  have hD : (D.map f).rank = D.rank := by
    dsimp [D]
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal]
    exact rank_map_diagonal f _
  have hm : V.map f * A.map f * U.map f = (D.map f).submatrix e e := by
    have hm := congrArg (fun B => B.map f) h
    rw [Matrix.map_mul, Matrix.map_mul] at hm
    exact hm.trans (by ext i j; rfl)
  have hVm : IsUnit (V.map f).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hV.map f.mapMatrix)
  have hUm : IsUnit (U.map f).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hU.map f.mapMatrix)
  calc
    (A.map f).rank = (V.map f * A.map f * U.map f).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUm,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVm]
    _ = ((D.map f).submatrix e e).rank := congrArg Matrix.rank hm
    _ = (D.submatrix e e).rank := by rw [Matrix.rank_submatrix, Matrix.rank_submatrix, hD]
    _ = (V * A * U).rank := congrArg Matrix.rank h.symm
    _ = A.rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hV)]

/-- Extension-field matrix labels give the same certificate for matrices over the
original field. All ranks involving the original matrix are taken over that field. -/
theorem supported_matrix_label_certificate_extension {K C T M : Type*}
    [Field K] [Fintype C] [Fintype T] [Fintype M]
    [DecidableEq C] [DecidableEq T] [DecidableEq M]
    (f : F →+* K) (E : C → C → Prop) [DecidableRel E]
    (A : Matrix (C × T) (C × T) F)
    (hA : ∀ q p, ¬ E p q → A.submatrix (Prod.mk q) (Prod.mk p) = 0)
    (X Y : C → Matrix M M K) :
    Fintype.card T * (∑ p, (X p - Y p).rank) ≤
      (∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
        (A.submatrix (Prod.mk q) (Prod.mk p)).rank * (X p - Y q).rank) +
      2 * Fintype.card M * (1 - A).rank := by
  have hAm : ∀ q p, ¬ E p q → (A.map f).submatrix (Prod.mk q) (Prod.mk p) = 0 := by
    intro q p hp
    change (A.submatrix (Prod.mk q) (Prod.mk p)).map f = 0
    rw [hA q p hp]
    ext i j
    exact map_zero f
  have h := supported_matrix_label_certificate E (A.map f) hAm X Y
  have hblock (q p : C) : ((A.map f).submatrix (Prod.mk q) (Prod.mk p)).rank =
      (A.submatrix (Prod.mk q) (Prod.mk p)).rank := rank_map_field f _
  have hrem : (1 - A.map f).rank = (1 - A).rank := by
    have heq : (1 - A).map f = 1 - A.map f := by
      change f.mapMatrix (1 - A) = 1 - f.mapMatrix A
      rw [map_sub, map_one]
    rw [← heq, rank_map_field]
  simpa only [hblock, hrem] using h

end LeanMachine.MatrixRankCertificate
