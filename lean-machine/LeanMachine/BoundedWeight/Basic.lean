import LeanMachine.RecoveryTrace
import Mathlib.Analysis.Matrix.Order

/-! Contractions and the transpose permutation for bounded-weight decoders. -/

namespace LeanMachine.BoundedWeight

open scoped Matrix Kronecker ComplexOrder

/-- Euclidean contraction, expressed without choosing a matrix norm instance. -/
def IsContraction {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) : Prop := (1 - Aᴴ * A).PosSemidef

/-- A Kronecker product of Euclidean contractions is a contraction. -/
theorem IsContraction.kronecker {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : IsContraction A) (hB : IsContraction B) : IsContraction (A ⊗ₖ B) := by
  have h := (Matrix.PosSemidef.kronecker hA
    (Matrix.PosSemidef.one : (1 : Matrix n n 𝕜).PosSemidef)).add
    ((Matrix.posSemidef_conjTranspose_mul_self A).kronecker hB)
  have he : 1 - (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) =
      (1 - Aᴴ * A) ⊗ₖ (1 : Matrix n n 𝕜) + (Aᴴ * A) ⊗ₖ (1 - Bᴴ * B) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.one_kronecker_one (m := m) (n := n) (α := 𝕜)]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kroneckerMap_apply]
    ring
  change (1 - (A ⊗ₖ B)ᴴ * (A ⊗ₖ B)).PosSemidef
  rwa [he]

/-- Positions of a `d × d` matrix. -/
abbrev Idx (d : ℕ) := Fin d × Fin d

/-- The permutation matrix sending a vectorized matrix to its transpose. -/
def swapMat (d : ℕ) : Matrix (Idx d) (Idx d) ℂ :=
  Matrix.of fun p q => if p = q.swap then 1 else 0

/-- A finite nonnegative combination of tensor products of contractions;
`γ` is the sum of its coefficients. -/
def HasWeight {d : ℕ} (K : Matrix (Idx d) (Idx d) ℂ) (γ : ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (A B : Fin m → Matrix (Fin d) (Fin d) ℂ),
    (∀ a, 0 ≤ c a) ∧ ∑ a, c a = γ ∧ (∀ a, IsContraction (A a)) ∧
      (∀ a, IsContraction (B a)) ∧ K = ∑ a, (c a : ℂ) • (A a ⊗ₖ B a)

/-- Matrices on which the decoder agrees with transposition. -/
def code {d : ℕ} (K : Matrix (Idx d) (Idx d) ℂ) : Submodule ℂ (Idx d → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin (swapMat d - K))

/-- Composing the decoder with transpose turns its code into a fixed space. -/
def T {d : ℕ} (K : Matrix (Idx d) (Idx d) ℂ) : Matrix (Idx d) (Idx d) ℂ :=
  swapMat d * K

variable {d : ℕ}

/-- The transpose permutation acts by swapping the two indices. -/
theorem swapMat_mulVec (x : Idx d → ℂ) (p : Idx d) :
    (swapMat d *ᵥ x) p = x p.swap := by
  have he (q : Idx d) : p = q.swap ↔ q = p.swap := by
    constructor <;> intro h
    · simpa using (congrArg Prod.swap h).symm
    · simp [h]
  simp [Matrix.mulVec, dotProduct, swapMat, he]

/-- Left multiplication by the transpose permutation swaps row indices. -/
theorem swapMat_mul_apply (A : Matrix (Idx d) (Idx d) ℂ) (p q : Idx d) :
    (swapMat d * A) p q = A p.swap q :=
  swapMat_mulVec (fun r => A r q) p

/-- Transposing twice is the identity. -/
theorem swapMat_mul_self : swapMat d * swapMat d = 1 := by
  ext p q
  rw [swapMat_mul_apply]
  simp [swapMat, Matrix.one_apply, Prod.swap_inj]

/-- Transposition preserves Euclidean norm. -/
theorem norm_swapMat_apply (x : EuclideanSpace ℂ (Idx d)) :
    ‖(swapMat d).toEuclideanLin x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply,
    swapMat_mulVec, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The decoder code is exactly the fixed space of `T`. -/
theorem code_eq_ker (K : Matrix (Idx d) (Idx d) ℂ) :
    code K = LinearMap.ker (1 - T K).mulVecLin := by
  ext x
  simp only [code, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero, T]
  constructor
  · intro h
    have hx := congrArg (fun y => swapMat d *ᵥ y) h
    simpa only [Matrix.mulVec_mulVec, swapMat_mul_self, Matrix.one_mulVec] using hx
  · intro h
    have hx := congrArg (fun y => swapMat d *ᵥ y) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, swapMat_mul_self,
      Matrix.one_mul] using hx

/-- The trace of a swapped tensor product collapses to a single matrix trace. -/
theorem trace_swapMat_kronecker (A B : Matrix (Fin d) (Fin d) ℂ) :
    (swapMat d * (A ⊗ₖ B)).trace = (A * B).trace := by
  change (∑ p : Idx d, (swapMat d * (A ⊗ₖ B)) p p) = ∑ i, (A * B) i i
  simp_rw [swapMat_mul_apply, Matrix.kroneckerMap_apply]
  simp only [Fintype.sum_prod_type, Matrix.mul_apply]
  exact Finset.sum_comm

end LeanMachine.BoundedWeight
