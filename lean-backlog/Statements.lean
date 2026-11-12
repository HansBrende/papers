/-
Statements only. Every `sorry` below is a proof obligation of the backlog; nothing here is proved.
Typechecked against Lean and Mathlib v4.34.1 with `lake env lean` from `lean-machine/`.
The informal statements and proofs are in the Markdown files of this folder.
-/
import Mathlib

open scoped Kronecker Matrix ComplexOrder

namespace LeanBacklog

/-! ## Common definitions -/

/-- `A` is a contraction for the Euclidean operator norm: `1 - Aᴴ A` is positive semidefinite. -/
def IsContraction {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Prop :=
  (1 - Aᴴ * A).PosSemidef

/-! ## Item A: decoders of bounded weight (`A-bounded-weight.md`) -/

section BoundedWeight

/-- Positions of a `d × d` matrix. A vector `x : Idx d → ℂ` is the matrix `X` with `X i j = x (i, j)`. -/
abbrev Idx (d : ℕ) := Fin d × Fin d

variable {d : ℕ}

/-- The swap `X ↦ Xᵀ` on vectors indexed by positions. -/
def swapMat (d : ℕ) : Matrix (Idx d) (Idx d) ℂ :=
  Matrix.of fun p q => if p = q.swap then 1 else 0

/-- `K` is a combination, with nonnegative weights of sum `γ`, of Kronecker products of contractions.
`A ⊗ₖ B` acts on positions as `X ↦ A X Bᵀ`. -/
def HasWeight (K : Matrix (Idx d) (Idx d) ℂ) (γ : ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (A B : Fin m → Matrix (Fin d) (Fin d) ℂ),
    (∀ a, 0 ≤ c a) ∧ ∑ a, c a = γ ∧ (∀ a, IsContraction (A a)) ∧ (∀ a, IsContraction (B a)) ∧
      K = ∑ a, (c a : ℂ) • (A a ⊗ₖ B a)

/-- The code of the decoder `K`: the matrices `X` with `Xᵀ = K X`. -/
def code (K : Matrix (Idx d) (Idx d) ℂ) : Submodule ℂ (Idx d → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin (swapMat d - K))

/-- `T = swap ∘ K`; the code is the fixed space of `T`. -/
def T (K : Matrix (Idx d) (Idx d) ℂ) : Matrix (Idx d) (Idx d) ℂ := swapMat d * K

/-- The product of the letters of a word, `true` for `T` and `false` for `Tᴴ`. -/
def word (K : Matrix (Idx d) (Idx d) ℂ) : List Bool → Matrix (Idx d) (Idx d) ℂ
  | [] => 1
  | b :: w => (if b then T K else (T K)ᴴ) * word K w

/-- Lemma A1: a word of odd length has trace at most `γ ^ length * d` in absolute value. -/
theorem norm_trace_word_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ} (h : HasWeight K γ)
    (w : List Bool) (hw : Odd w.length) :
    ‖(word K w).trace‖ ≤ γ ^ w.length * d := by
  sorry

/-- Theorem A2: `dim code ≤ γ (d² + d) / (1 + γ)`. -/
theorem finrank_code_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ} (h : HasWeight K γ) :
    (1 + γ) * (Module.finrank ℂ (code K) : ℝ) ≤ γ * ((d : ℝ) ^ 2 + d) := by
  sorry

/-- Theorem A2, second part: for `γ ≤ 1`, `dim code ≤ (d² + γ d) / 2`. -/
theorem two_mul_finrank_code_le_of_le_one {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (hγ : γ ≤ 1) :
    2 * (Module.finrank ℂ (code K) : ℝ) ≤ (d : ℝ) ^ 2 + γ * d := by
  sorry

/-- The Hermitian part of `T`. -/
noncomputable def hermPart (K : Matrix (Idx d) (Idx d) ℂ) : Matrix (Idx d) (Idx d) ℂ :=
  (1 / 2 : ℂ) • (T K + (T K)ᴴ)

theorem hermPart_isHermitian (K : Matrix (Idx d) (Idx d) ℂ) : (hermPart K).IsHermitian := by
  sorry

/-- The number of eigenvalues of the Hermitian part that are at least `1`. -/
noncomputable def nPlus (K : Matrix (Idx d) (Idx d) ℂ) : ℕ :=
  Nat.card {i : Idx d // 1 ≤ (hermPart_isHermitian K).eigenvalues i}

/-- Theorem A3, first part: the code is no larger than the number of eigenvalues `≥ 1`. -/
theorem finrank_code_le_nPlus (K : Matrix (Idx d) (Idx d) ℂ) :
    Module.finrank ℂ (code K) ≤ nPlus K := by
  sorry

/-- `clip x = max (-1) (min 1 x)`. -/
noncomputable def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- Theorem A3, second part: for an odd polynomial `q` within `η` of `clip` on `[-γ, γ]`,
`2 n₊ ≤ (1 + η) d² + (∑ |q_k| γ^k) d`. -/
theorem two_mul_nPlus_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ} (h : HasWeight K γ)
    (q : Polynomial ℝ) (η : ℝ) (hodd : ∀ x, q.eval (-x) = -q.eval x)
    (happrox : ∀ x ∈ Set.Icc (-γ) γ, |q.eval x - clip x| ≤ η) :
    2 * (nPlus K : ℝ) ≤ (1 + η) * (d : ℝ) ^ 2 + (∑ k ∈ q.support, |q.coeff k| * γ ^ k) * d := by
  sorry

/-- Corollary A4: bounded weight gives rate `1/2 + o(1)`, with an excess linear in `d`. -/
theorem exists_linear_excess (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ (d : ℕ) (K : Matrix (Idx d) (Idx d) ℂ), HasWeight K γ →
      (Module.finrank ℂ (code K) : ℝ) ≤ (1 / 2 + η) * (d : ℝ) ^ 2 + C * d := by
  sorry

end BoundedWeight

/-! ## Item B: codes with a recovery matrix (`B-recovery-matrix.md`) -/

section RecoveryMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Theorem B1: the fixed space of a contraction `M` has dimension at most `(N + Re tr M) / 2`. -/
theorem two_mul_finrank_fixed_le_of_contraction (M : Matrix n n ℂ) (hM : IsContraction M) :
    2 * (Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (1 - M))) : ℝ)
      ≤ Fintype.card n + M.trace.re := by
  sorry

/-- Theorem B2: `|tr Z|² ≤ rank Z * ‖Z‖_F²`. -/
theorem norm_trace_sq_le_rank_mul (Z : Matrix n n ℂ) :
    ‖Z.trace‖ ^ 2 ≤ (Z.rank : ℝ) * ∑ i, ∑ j, ‖Z i j‖ ^ 2 := by
  sorry

/-- Proposition B3: if a diagonal sign change turns `M` into `-M`, the fixed space of `M` has dimension
at most `N / 2` (characteristic not 2). -/
theorem two_mul_finrank_fixed_le_of_sign {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (M : Matrix n n F) (ε : n → F) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hM : Matrix.diagonal ε * M * Matrix.diagonal ε = -M) :
    2 * Module.finrank F (LinearMap.ker (Matrix.mulVecLin (1 - M))) ≤ Fintype.card n := by
  sorry

end RecoveryMatrix

/-! ## Item C: the second rule for whole-row decoders with invertible blocks (`C-second-rule.md`) -/

section SecondRule

variable {F : Type*} [Field F] {d : ℕ}

/-- The code of a whole-row decoder: column `r` of `X` is `∑ s ∈ ρ r, M r s *ᵥ (row s of X)`. -/
def rowCode (ρ : Fin d → Finset (Fin d)) (M : Fin d → Fin d → Matrix (Fin d) (Fin d) F) :
    Submodule F (Matrix (Fin d) (Fin d) F) where
  carrier := {X | ∀ r i, X i r = ∑ s ∈ ρ r, ∑ j, M r s i j * X s j}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

/-- The rows known before step `t` of the order `σ`. -/
def known (σ : Equiv.Perm (Fin d)) (t : Fin d) : Finset (Fin d) :=
  (Finset.univ.filter fun u : Fin d => u < t).image σ

/-- The columns all of whose rows are known before step `t`. -/
def complete (ρ : Fin d → Finset (Fin d)) (σ : Equiv.Perm (Fin d)) (t : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun r => ρ r ⊆ known σ t

/-- The columns whose only unknown row at step `t` is the new row `σ t`. -/
def frontier (ρ : Fin d → Finset (Fin d)) (σ : Equiv.Perm (Fin d)) (t : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun r => σ t ∈ ρ r ∧ ρ r ⊆ insert (σ t) (known σ t)

/-- Corollary C2: with invertible blocks, for every order `σ` of the rows,
`dim ≤ ∑ t, (d - max |complete| (|known| if the frontier is nonempty))`. -/
theorem finrank_rowCode_le (ρ : Fin d → Finset (Fin d))
    (M : Fin d → Fin d → Matrix (Fin d) (Fin d) F) (hM : ∀ r, ∀ s ∈ ρ r, IsUnit (M r s).det)
    (σ : Equiv.Perm (Fin d)) :
    Module.finrank F (rowCode ρ M) ≤
      ∑ t : Fin d, (d - max (complete ρ σ t).card (if (frontier ρ σ t).Nonempty then (t : ℕ) else 0)) := by
  sorry

end SecondRule

end LeanBacklog
