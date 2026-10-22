import TransposeFollowup.SL2ComplexConjugation
import TransposeFollowup.SL2TraceCertificate

/-! Four actual matrix columns can be certified by a commutator trace.
The trace-two case is handled exactly; no diagonalization or eigenvalue
separation assumption is needed. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
open scoped commutatorElement
set_option autoImplicit false

variable {K : Type*} [Field K]
local notation "M" => Matrix (Fin 2) (Fin 2) K
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) K

/-- Columns are the row-major coordinates of `I`, `a`, `b`, and `a*b`. -/
def pairSpanMatrix (a b : M) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a 0 0, b 0 0, (a * b) 0 0;
     0, a 0 1, b 0 1, (a * b) 0 1;
     0, a 1 0, b 1 0, (a * b) 1 0;
     1, a 1 1, b 1 1, (a * b) 1 1]

theorem pairSpanMatrix_det (a b : M) :
    (pairSpanMatrix a b).det = (a * b - b * a).det := by
  rw [pairSpanMatrix, Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.succAbove]
  ring

theorem pairSpanMatrix_det_trace_polynomial (a b : M) :
    (pairSpanMatrix a b).det =
      4 * a.det * b.det - (Matrix.trace a) ^ 2 * b.det -
        (Matrix.trace b) ^ 2 * a.det - (Matrix.trace (a * b)) ^ 2 +
        Matrix.trace a * Matrix.trace b * Matrix.trace (a * b) := by
  rw [pairSpanMatrix_det]
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.trace, Matrix.diag]
  ring

theorem pairSpanMatrix_det_commutator (a b : G) :
    (pairSpanMatrix (a : M) (b : M)).det =
      2 - Matrix.trace ((⁅a, b⁆ : G) : M) := by
  have ha : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using a.property
  have hb : b 0 0 * b 1 1 - b 0 1 * b 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using b.property
  rw [pairSpanMatrix_det, commutatorElement_def,
    Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.SL2_inv_expl]
  change ((a : M) * (b : M) - (b : M) * (a : M)).det =
    2 - Matrix.trace ((a : M) * (b : M) *
      !![a 1 1, -a 0 1; -a 1 0, a 0 0] * !![b 1 1, -b 0 1; -b 1 0, b 0 0])
  simp only [Matrix.det_fin_two, Matrix.sub_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.diag,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination 2 * (b 0 0 * b 1 1 - b 0 1 * b 1 0) * ha + 2 * hb

theorem pairSpanMatrix_det_trace_two (a b : G)
    (ha : Matrix.trace (a : M) = 2) :
    (pairSpanMatrix (a : M) (b : M)).det =
      -(Matrix.trace ((a * b : G) : M) - Matrix.trace (b : M)) ^ 2 := by
  rw [pairSpanMatrix_det_trace_polynomial, a.property, b.property, ha]
  change _ = -(Matrix.trace ((a : M) * (b : M)) - Matrix.trace (b : M)) ^ 2
  ring

theorem pairSpanMatrix_det_conjugate (u a b : G) :
    (pairSpanMatrix ((u * a * u⁻¹ : G) : M) ((u * b * u⁻¹ : G) : M)).det =
      (pairSpanMatrix (a : M) (b : M)).det := by
  rw [pairSpanMatrix_det_commutator, pairSpanMatrix_det_commutator]
  have he : ⁅u * a * u⁻¹, u * b * u⁻¹⁆ = u * ⁅a, b⁆ * u⁻¹ := by group
  rw [he, sl2_trace_conjugate]

end TransposeFollowup.SL2Escape
