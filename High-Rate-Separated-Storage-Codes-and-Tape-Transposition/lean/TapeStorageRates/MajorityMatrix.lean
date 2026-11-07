import TapeStorageRates.MajorityOperator
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Standard-coordinate matrix of the majority tensor operator -/

namespace TapeStorageRates.Majority

open Finset Module PiTensorProduct
open scoped BigOperators TensorProduct

set_option autoImplicit false
noncomputable section

variable {K V : Type*} [Field K] [Fintype V] [DecidableEq V] {m : ℕ}

/-- The coordinate basis, distinct from the adapted basis used to count
fixed vectors. Its indices are the actual tuples of source coordinates. -/
def coordinateBasis (K : Type*) [Field K] (V : Type*) [Fintype V] (m : ℕ) :
    Basis (Fin m → V) K (⨂[K] _ : Fin m, V → K) :=
  Basis.piTensorProduct fun _ : Fin m => Pi.basisFun K V

/-- The concrete matrix on tuples of coordinates. -/
def matrix (A : Matrix V V K) (m : ℕ) : Matrix (Fin m → V) (Fin m → V) K :=
  LinearMap.toMatrix (coordinateBasis K V m) (coordinateBasis K V m)
    (operator A.mulVecLin m)

/-- Exact signed-corner entry formula in the coordinate basis. -/
theorem matrix_apply (A : Matrix V V K) (u v : Fin m → V) :
    matrix A m u v = ((2 : K) ^ m)⁻¹ *
      ∑ σ : Fin m → Bool, majoritySign (K := K) σ *
        ∏ i, ((if u i = v i then 1 else 0) + sign (K := K) (σ i) * A (u i) (v i)) := by
  simp [matrix, LinearMap.toMatrix_apply, coordinateBasis, operator, corner,
    Pi.basisFun_apply, Pi.single_apply]

/-- The changed coordinates of a pair of tuple indices. -/
def active (u v : Fin m → V) : Finset (Fin m) := univ.filter fun i => u i ≠ v i

/-- The coefficient of an active coordinate set in the signed-corner formula. -/
def coefficient (K : Type*) [Field K] {m : ℕ} (S : Finset (Fin m)) : K :=
  ((2 : K) ^ m)⁻¹ * ∑ σ : Fin m → Bool, majoritySign (K := K) σ *
    ∏ i ∈ S, sign (K := K) (σ i)

/-- Even active sets have zero coefficient. Only powers of two are divided
out; there is no restriction relating `m` to the field characteristic. -/
theorem coefficient_eq_zero_of_even (h2 : (2 : K) ≠ 0) (hm : Odd m)
    (S : Finset (Fin m)) (hS : Even S.card) : coefficient K S = 0 := by
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    ⟨(fun σ i => !σ i), (fun σ i => !σ i), (by intro σ; funext i; simp),
      (by intro σ; funext i; simp)⟩
  let f : (Fin m → Bool) → K := fun σ => majoritySign (K := K) σ *
    ∏ i ∈ S, sign (K := K) (σ i)
  have hneg (σ : Fin m → Bool) : f (e σ) = -f σ := by
    simp [f, e, majoritySign_not hm, Finset.prod_neg, hS.neg_one_pow]
  have hsum : (∑ σ, f σ) = -(∑ σ, f σ) := by
    calc
      _ = ∑ σ, f (e σ) := (e.sum_comp f).symm
      _ = _ := by simp_rw [hneg]; rw [sum_neg_distrib]
  have hz : ∑ σ, f σ = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * (∑ σ, f σ) = 0 from ?_)).resolve_left h2
    rw [two_mul]
    conv_lhs => rhs; rw [hsum]
    exact add_neg_cancel _
  change ((2 : K) ^ m)⁻¹ * (∑ σ, f σ) = 0
  rw [hz, mul_zero]

/-- Zero diagonal makes the changed-coordinate set determine the entire
matrix entry; inactive coordinates contribute exactly one. -/
theorem matrix_apply_active (A : Matrix V V K) (hdiag : ∀ v, A v v = 0)
    (u v : Fin m → V) :
    matrix A m u v = coefficient K (active u v) * ∏ i ∈ active u v, A (u i) (v i) := by
  have hprod (σ : Fin m → Bool) :
      (∏ i, ((if u i = v i then 1 else 0) + sign (K := K) (σ i) * A (u i) (v i))) =
      (∏ i ∈ active u v, sign (K := K) (σ i)) * ∏ i ∈ active u v, A (u i) (v i) := by
    rw [← Finset.prod_mul_distrib]
    rw [active, prod_filter]
    apply prod_congr rfl
    intro i _
    by_cases hi : u i = v i <;> simp [hi, hdiag]
  rw [matrix_apply]
  simp_rw [hprod, ← mul_assoc]
  rw [← sum_mul]
  exact (mul_assoc _ _ _).symm

/-- A nonzero entry changes an odd number of coordinates, along nonzero
entries of the original matrix in every changed coordinate. -/
theorem matrix_support (A : Matrix V V K) (hdiag : ∀ v, A v v = 0)
    (h2 : (2 : K) ≠ 0) (hm : Odd m) {u v : Fin m → V}
    (huv : matrix A m u v ≠ 0) :
    Odd (active u v).card ∧ ∀ i, u i ≠ v i → A (u i) (v i) ≠ 0 := by
  rw [matrix_apply_active A hdiag] at huv
  obtain ⟨hc, hp⟩ := mul_ne_zero_iff.mp huv
  constructor
  · by_contra h
    exact hc (coefficient_eq_zero_of_even h2 hm _ (Nat.not_odd_iff_even.mp h))
  · intro i hi
    exact prod_ne_zero_iff.mp hp i (mem_filter.mpr ⟨mem_univ _, hi⟩)

/-- The amplified matrix has zero diagonal. -/
theorem matrix_diag (A : Matrix V V K) (hdiag : ∀ v, A v v = 0)
    (h2 : (2 : K) ≠ 0) (hm : Odd m) (u : Fin m → V) : matrix A m u u = 0 := by
  by_contra h
  have ho := (matrix_support A hdiag h2 hm h).1
  simp [active] at ho

/-- Matrix rank plus the actual operator's kernel dimension is the exact
tuple-space dimension. This is the bridge needed by syndrome counting. -/
theorem check_rank_add_finrank_ker (A : Matrix V V K) (m : ℕ) :
    (1 - matrix A m).rank +
      finrank K (LinearMap.ker (LinearMap.id - operator A.mulVecLin m)) =
        Fintype.card V ^ m := by
  let b := coordinateBasis K V m
  have : Module.Finite K (⨂[K] _ : Fin m, V → K) := Module.Finite.of_basis b
  have he : 1 - matrix A m = LinearMap.toMatrix b b (LinearMap.id - operator A.mulVecLin m) := by
    have hs := (LinearMap.toMatrix b b).map_sub LinearMap.id (operator A.mulVecLin m)
    change LinearMap.toMatrix b b (LinearMap.id - operator A.mulVecLin m) =
      LinearMap.toMatrix b b LinearMap.id - LinearMap.toMatrix b b (operator A.mulVecLin m) at hs
    rw [LinearMap.toMatrix_id] at hs
    exact hs.symm
  rw [he, Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix,
    LinearMap.finrank_range_add_finrank_ker, Module.finrank_eq_card_basis b]
  exact Fintype.card_pi_const V m

end
end TapeStorageRates.Majority
