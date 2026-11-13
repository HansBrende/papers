/-
Item D of the backlog: comparison bounds for one-hop decoders over every field, a Frobenius form
of the bounded-weight theorem, and two open problems stated as propositions.
Statements only; every `sorry` is an open obligation. See `D-comparison.md`.
Run `lake env lean ../lean-backlog/StatementsD.lean` from `lean-machine/`.
-/
import LeanMachine.BoundedWeight.Asymptotic

open scoped Kronecker Matrix

namespace LeanBacklog.D

/-- Positions of a `d × d` matrix (the same type as `LeanMachine.BoundedWeight.Idx`). -/
abbrev Idx (d : ℕ) := Fin d × Fin d

variable {F : Type*} [Field F] {d : ℕ}

/-- The permutation matrix of transposition, over any field. -/
def swapMat (F : Type*) [Field F] (d : ℕ) : Matrix (Idx d) (Idx d) F :=
  Matrix.of fun p q => if p = q.swap then 1 else 0

/-- The code of a decoder `K`: the vectorized matrices `X` with `Xᵀ = K X`.
`(A ⊗ₖ B)` acts by `X ↦ A X Bᵀ`. -/
def code (K : Matrix (Idx d) (Idx d) F) : Submodule F (Idx d → F) :=
  LinearMap.ker (Matrix.mulVecLin (swapMat F d - K))

/-- D0. Two independent base changes do not change the dimension of the code. -/
theorem finrank_code_baseChange (K : Matrix (Idx d) (Idx d) F)
    (P Q : Matrix (Fin d) (Fin d) F) (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    Module.finrank F (code ((Q ⊗ₖ P) * K * (P⁻¹ ⊗ₖ Q⁻¹))) = Module.finrank F (code K) := by
  sorry

/-- D1. Two codes: they overlap inside the kernel of the difference of the decoders. -/
theorem finrank_code_add_le (K K' : Matrix (Idx d) (Idx d) F) :
    Module.finrank F (code K) + Module.finrank F (code K') ≤
      d ^ 2 + Module.finrank F (LinearMap.ker (Matrix.mulVecLin (K - K'))) := by
  sorry

/-- D2. Comparison with the code of `-(G ⊗ G⁻¹)`. -/
theorem two_mul_finrank_code_le_pairing (K : Matrix (Idx d) (Idx d) F)
    (G : Matrix (Fin d) (Fin d) F) (hG : IsUnit G.det) :
    2 * Module.finrank F (code K) ≤
      d * (d + 1) + 2 * Module.finrank F (LinearMap.ker (Matrix.mulVecLin (K + G ⊗ₖ G⁻¹))) := by
  sorry

/-- The square system of the triangle bound: below the diagonal the unknown itself, on and above
the diagonal the entry of `K X` minus the diagonal entry of `X`. -/
def triangleMat (K : Matrix (Idx d) (Idx d) F) : Matrix (Idx d) (Idx d) F :=
  Matrix.of fun p q =>
    if p.2 < p.1 then (if p = q then 1 else 0)
    else K p q - (if p.1 = p.2 ∧ p = q then 1 else 0)

/-- D3. The triangle bound, in every characteristic. -/
theorem two_mul_finrank_code_le_triangle (K : Matrix (Idx d) (Idx d) F) :
    2 * Module.finrank F (code K) ≤
      d * (d - 1) + 2 * Module.finrank F (LinearMap.ker (Matrix.mulVecLin (triangleMat K))) := by
  sorry

/-- D4. Compression by any matrix `E`: `(1 ⊗ E) (A ⊗ B) (E ⊗ 1) = A E ⊗ E B`. -/
theorem finrank_code_le_compress (K : Matrix (Idx d) (Idx d) F) (E : Matrix (Fin d) (Fin d) F) :
    Module.finrank F (code K) ≤
      Module.finrank F (code (((1 : Matrix (Fin d) (Fin d) F) ⊗ₖ E) * K *
        (E ⊗ₖ (1 : Matrix (Fin d) (Fin d) F)))) + d * (1 - E).rank := by
  sorry

/-- D5. The half bound for a fixed number of terms of bounded mean square Frobenius norm. -/
theorem exists_linear_excess_frobenius (M : ℕ) (κ η : ℝ) (hκ : 0 ≤ κ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ (d : ℕ) (A B : Fin M → Matrix (Fin d) (Fin d) ℂ),
      (∑ a, ((∑ i, ∑ j, ‖A a i j‖ ^ 2) + (∑ i, ∑ j, ‖B a i j‖ ^ 2)) ≤ κ * d) →
      (Module.finrank ℂ (LeanMachine.BoundedWeight.code (∑ a, A a ⊗ₖ B a)) : ℝ) ≤
        (1 / 2 + η) * (d : ℝ) ^ 2 + C * d := by
  sorry

/-- **Open.** Problem R for `M` terms over `F`: rate one half up to a linear term. -/
def ProblemR (F : Type*) [Field F] (M : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ (d : ℕ) (A B : Fin M → Matrix (Fin d) (Fin d) F),
    (Module.finrank F (code (∑ a, A a ⊗ₖ B a)) : ℝ) ≤ (1 / 2 + η) * (d : ℝ) ^ 2 + C * d

/-- **Open.** Problem S for `M` terms over `F`: some pairing operator is far from `-K`. -/
def ProblemS (F : Type*) [Field F] (M : ℕ) : Prop :=
  ∃ C : ℕ, ∀ (d : ℕ) (A B : Fin M → Matrix (Fin d) (Fin d) F),
    ∃ G : Matrix (Fin d) (Fin d) F, IsUnit G.det ∧
      Module.finrank F (LinearMap.ker (Matrix.mulVecLin ((∑ a, A a ⊗ₖ B a) + G ⊗ₖ G⁻¹))) ≤ C * d

/-- D6. Problem S implies Problem R (by D2). -/
theorem problemR_of_problemS (F : Type*) [Field F] (M : ℕ) (h : ProblemS F M) : ProblemR F M := by
  sorry

end LeanBacklog.D
