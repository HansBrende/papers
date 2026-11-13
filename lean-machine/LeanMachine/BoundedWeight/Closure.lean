import LeanMachine.BoundedWeight.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Closure of bounded-weight tensor combinations under sums, scaling, products, adjoints,
and conjugation by transposition. -/

namespace LeanMachine.BoundedWeight

open scoped Matrix Kronecker ComplexOrder

section Contraction

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive-semidefinite condition agrees with the Euclidean operator norm. -/
theorem isContraction_iff_l2_opNorm_le (A : Matrix n n ℂ) :
    IsContraction A ↔ ‖A‖ ≤ 1 := by
  change Aᴴ * A ≤ 1 ↔ ‖A‖ ≤ 1
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg,
    Matrix.l2_opNorm_conjTranspose_mul_self]
  constructor <;> intro h
  · nlinarith [norm_nonneg A]
  · nlinarith [norm_nonneg A]

/-- Contractions are closed under composition. -/
theorem IsContraction.mul {A B : Matrix n n ℂ}
    (hA : IsContraction A) (hB : IsContraction B) : IsContraction (A * B) := by
  rw [isContraction_iff_l2_opNorm_le] at hA hB ⊢
  exact (Matrix.l2_opNorm_mul A B).trans (by
    simpa only [one_mul] using mul_le_mul hA hB (norm_nonneg B) zero_le_one)

/-- Contractions are closed under adjoints. -/
theorem IsContraction.conjTranspose {A : Matrix n n ℂ}
    (hA : IsContraction A) : IsContraction Aᴴ := by
  rwa [isContraction_iff_l2_opNorm_le, Matrix.l2_opNorm_conjTranspose,
    ← isContraction_iff_l2_opNorm_le]

end Contraction

variable {d : ℕ}

/-- Finite indexing types can be used without manually numbering summands. -/
theorem HasWeight.of_fintype {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (A B : ι → Matrix (Fin d) (Fin d) ℂ)
    (hc : ∀ i, 0 ≤ c i) (hA : ∀ i, IsContraction (A i))
    (hB : ∀ i, IsContraction (B i)) :
    HasWeight (∑ i, (c i : ℂ) • (A i ⊗ₖ B i)) (∑ i, c i) := by
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, c ∘ e, A ∘ e, B ∘ e, fun i => hc (e i),
    ?_, fun i => hA (e i), fun i => hB (e i), ?_⟩
  · exact e.sum_comp c
  · exact (e.sum_comp (fun i => (c i : ℂ) • (A i ⊗ₖ B i))).symm

/-- Adding decoders adds their weights. -/
theorem HasWeight.add {K L : Matrix (Idx d) (Idx d) ℂ} {γ δ : ℝ}
    (hK : HasWeight K γ) (hL : HasWeight L δ) : HasWeight (K + L) (γ + δ) := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := hK
  obtain ⟨n, e, C, D, he, hδ, hC, hD, rfl⟩ := hL
  have h := HasWeight.of_fintype (Sum.elim c e) (Sum.elim A C) (Sum.elim B D)
    (by rintro (i | i) <;> simp [hc, he])
    (by rintro (i | i) <;> simp [hA, hC])
    (by rintro (i | i) <;> simp [hB, hD])
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hγ, hδ] using h

/-- Nonnegative rescaling rescales the coefficient sum. -/
theorem HasWeight.smul_nonneg {K : Matrix (Idx d) (Idx d) ℂ} {γ a : ℝ}
    (h : HasWeight K γ) (ha : 0 ≤ a) : HasWeight ((a : ℂ) • K) (a * γ) := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := h
  refine ⟨m, fun i => a * c i, A, B, fun i => mul_nonneg ha (hc i),
    ?_, hA, hB, ?_⟩
  · rw [← Finset.mul_sum, hγ]
  · simp only [Finset.smul_sum, Complex.ofReal_mul, smul_smul]

/-- Zero can carry any nonnegative weight through a zero tensor summand. -/
theorem HasWeight.zero {γ : ℝ} (hγ : 0 ≤ γ) :
    HasWeight (0 : Matrix (Idx d) (Idx d) ℂ) γ := by
  have hz : IsContraction (0 : Matrix (Fin d) (Fin d) ℂ) := by
    simpa [IsContraction] using
      (Matrix.PosSemidef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosSemidef)
  have h := HasWeight.of_fintype (fun _ : Unit => γ)
    (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun _ => (0 : Matrix (Fin d) (Fin d) ℂ))
    (fun _ => hγ) (fun _ => hz) (fun _ => hz)
  simpa using h

/-- Padding with a zero summand raises the weight to any larger bound. -/
theorem HasWeight.mono {K : Matrix (Idx d) (Idx d) ℂ} {γ Γ : ℝ}
    (h : HasWeight K γ) (hγ : γ ≤ Γ) : HasWeight K Γ := by
  have hz : HasWeight (0 : Matrix (Idx d) (Idx d) ℂ) (Γ - γ) :=
    HasWeight.zero (sub_nonneg.mpr hγ)
  simpa using h.add hz

/-- Multiplication multiplies the coefficient sums. -/
theorem HasWeight.mul {K L : Matrix (Idx d) (Idx d) ℂ} {γ δ : ℝ}
    (hK : HasWeight K γ) (hL : HasWeight L δ) : HasWeight (K * L) (γ * δ) := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := hK
  obtain ⟨n, e, C, D, he, hδ, hC, hD, rfl⟩ := hL
  have h := HasWeight.of_fintype (fun p : Fin m × Fin n => c p.1 * e p.2)
    (fun p => A p.1 * C p.2) (fun p => B p.1 * D p.2)
    (fun p => mul_nonneg (hc p.1) (he p.2))
    (fun p => (hA p.1).mul (hC p.2)) (fun p => (hB p.1).mul (hD p.2))
  have hw : (∑ p : Fin m × Fin n, c p.1 * e p.2) = γ * δ := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hγ, hδ]
  rw [hw] at h
  simpa only [Fintype.sum_prod_type, Finset.sum_mul_sum, Matrix.mul_kronecker_mul,
    Complex.ofReal_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm] using h

/-- Taking adjoints preserves the coefficient sum because the weights are real. -/
theorem HasWeight.conjTranspose {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (hK : HasWeight K γ) : HasWeight Kᴴ γ := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := hK
  refine ⟨m, c, fun i => (A i)ᴴ, fun i => (B i)ᴴ, hc, hγ,
    fun i => (hA i).conjTranspose, fun i => (hB i).conjTranspose, ?_⟩
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, RCLike.star_def, Complex.conj_ofReal]

/-- Right multiplication by transpose swaps column indices. -/
theorem mul_swapMat_apply (A : Matrix (Idx d) (Idx d) ℂ) (p q : Idx d) :
    (A * swapMat d) p q = A p q.swap := by
  simp [Matrix.mul_apply, swapMat]

/-- The transpose permutation is self-adjoint. -/
theorem conjTranspose_swapMat : (swapMat d)ᴴ = swapMat d := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.conjTranspose_apply, swapMat, eq_comm, and_comm]

/-- Conjugating a tensor product by transpose exchanges its two factors. -/
theorem swapMat_kronecker_swapMat (A B : Matrix (Fin d) (Fin d) ℂ) :
    swapMat d * (A ⊗ₖ B) * swapMat d = B ⊗ₖ A := by
  ext p q
  rw [mul_swapMat_apply, swapMat_mul_apply]
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- Conjugation by transpose preserves the weight. -/
theorem HasWeight.swap_conj {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (hK : HasWeight K γ) : HasWeight (swapMat d * K * swapMat d) γ := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := hK
  refine ⟨m, c, B, A, hc, hγ, hB, hA, ?_⟩
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    swapMat_kronecker_swapMat]

end LeanMachine.BoundedWeight
