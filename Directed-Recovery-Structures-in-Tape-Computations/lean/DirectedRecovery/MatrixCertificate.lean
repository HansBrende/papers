import LeanMachine.MatrixRankCertificate
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The finite matrix-label certificate

The matrix has `N` coordinate blocks of width `t`. An incidence `E p q`
allows the block in output row `q` and input column `p`. Labels have an
independent width `m`, and may be taken over any extension of the coefficient
field. The displayed bound uses real subtraction and division, exactly as
in the manuscript.
-/

open scoped BigOperators

namespace DirectedRecovery

/-- The full matrix-label certificate with labels over an arbitrary field extension.
The original matrix and all its block ranks remain over `F`. -/
theorem matrix_label_certificate_extension {F K : Type*} [Field F] [Field K]
    {N t m : ℕ} (hm : 0 < m) (f : F →+* K)
    (E : Fin N → Fin N → Prop) [DecidableRel E]
    (A : Matrix (Fin N × Fin t) (Fin N × Fin t) F)
    (hA : ∀ q p, ¬ E p q → A.submatrix (Prod.mk q) (Prod.mk p) = 0)
    (X Y : Fin N → Matrix (Fin m) (Fin m) K) :
    ((t : ℝ) * (∑ p, ((X p - Y p).rank : ℝ)) -
        (∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
          ((A.submatrix (Prod.mk q) (Prod.mk p)).rank : ℝ) *
            ((X p - Y q).rank : ℝ))) / (2 * (m : ℝ)) ≤
      ((1 - A).rank : ℝ) := by
  have h := LeanMachine.MatrixRankCertificate.supported_matrix_label_certificate_extension
    f E A hA X Y
  simp only [Fintype.card_fin] at h
  have hreal : (t : ℝ) * (∑ p, ((X p - Y p).rank : ℝ)) ≤
      (∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
        ((A.submatrix (Prod.mk q) (Prod.mk p)).rank : ℝ) *
          ((X p - Y q).rank : ℝ)) + 2 * (m : ℝ) * ((1 - A).rank : ℝ) := by
    exact_mod_cast h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mpr
  nlinarith only [hreal]

/-- The matrix-label certificate over the coefficient field itself. -/
theorem matrix_label_certificate {F : Type*} [Field F]
    {N t m : ℕ} (hm : 0 < m)
    (E : Fin N → Fin N → Prop) [DecidableRel E]
    (A : Matrix (Fin N × Fin t) (Fin N × Fin t) F)
    (hA : ∀ q p, ¬ E p q → A.submatrix (Prod.mk q) (Prod.mk p) = 0)
    (X Y : Fin N → Matrix (Fin m) (Fin m) F) :
    ((t : ℝ) * (∑ p, ((X p - Y p).rank : ℝ)) -
        (∑ q, ∑ p ∈ Finset.univ.filter (fun p => E p q),
          ((A.submatrix (Prod.mk q) (Prod.mk p)).rank : ℝ) *
            ((X p - Y q).rank : ℝ))) / (2 * (m : ℝ)) ≤
      ((1 - A).rank : ℝ) :=
  matrix_label_certificate_extension hm (RingHom.id F) E A hA X Y

end DirectedRecovery
