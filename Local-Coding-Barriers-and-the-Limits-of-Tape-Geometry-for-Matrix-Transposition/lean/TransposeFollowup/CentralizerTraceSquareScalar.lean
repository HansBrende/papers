import TransposeFollowup.ActualScalarReadoutCoefficients

/-! A positive scalar coordinate with an exact two-term product readout.
No inverse determinant occurs in its product identity. The linear readout
uses the two coefficients selected from actual words in the imported module. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

noncomputable def traceSquareScalar (u : G) : ℝ :=
  (2/3 : ℝ) * (Matrix.trace (u:RMat))^2 - 4/3

theorem traceSquareScalar_centered (b : RMat) (u : G) {s t : ℝ}
    (hb : Matrix.trace b=0) (hu : (u:RMat)=scalarAffine b s t) :
    traceSquareScalar u = (8/3 : ℝ)*s^2-4/3 := by
  rw [traceSquareScalar,hu,scalarAffine_eq_smul_add]
  simp [Matrix.trace_add, Matrix.trace_smul, hb]
  ring

theorem traceSquareScalar_near_identity (u : G)
    (hnear : dist (u:RMat) 1 ≤ 1/16) :
    1 ≤ traceSquareScalar u ∧ traceSquareScalar u ≤ 2 := by
  have he := trace_error_le_frobenius_dist (u:RMat) 1
  simp only [Matrix.trace_one,Fintype.card_fin,Nat.cast_ofNat] at he
  have hlow := (abs_le.mp he).1
  have hhigh := (abs_le.mp he).2
  have ht : 15/8 ≤ Matrix.trace (u:RMat) ∧ Matrix.trace (u:RMat) ≤ 17/8 := by
    constructor <;> linarith only [hnear,hlow,hhigh]
  dsimp only [traceSquareScalar]
  constructor <;> nlinarith only [ht.1,ht.2]

theorem traceSquareScalar_product (b : RMat) (u v : G) {s t p q : ℝ}
    (hb : Matrix.trace b=0)
    (hu : (u:RMat)=scalarAffine b s t) (hv : (v:RMat)=scalarAffine b p q) :
    traceSquareScalar u * traceSquareScalar v =
      (2/3 : ℝ)*(traceSquareScalar (u*v)+traceSquareScalar (u*v⁻¹)) := by
  obtain ⟨hprod,hinv,_⟩ := sl2_scalarAffine_product_coordinates b u v hu hv
  simp only [hb,mul_zero,add_zero] at hprod hinv
  have hce := sl2_centered_coordinate_equation b u hb hu
  have hpe := sl2_centered_coordinate_equation b v hb hv
  rw [traceSquareScalar_centered b u hb hu,traceSquareScalar_centered b v hb hv,
    traceSquareScalar_centered b (u*v) hb hprod,traceSquareScalar_centered b (u*v⁻¹) hb hinv]
  linear_combination (-32/9 : ℝ)*b.det*q^2*hce + (32/9 : ℝ)*(s^2-1)*hpe

theorem traceSquareScalar_inverse_final (b : RMat) (u v g : G) {s t p q : ℝ}
    (hb : Matrix.trace b=0)
    (hu : (u:RMat)=scalarAffine b s t) (hv : (v:RMat)=scalarAffine b p q) :
    let D := (b*(g:RMat)-(g:RMat)*b).det
    8*b.det*Matrix.trace ((v*u⁻¹*g*(v*u)*g⁻¹:G):RMat) =
      3*D*traceSquareScalar u + 3*(4*b.det-D)*traceSquareScalar v := by
  dsimp only
  have hce := sl2_centered_coordinate_equation b u hb hu
  have hpe := sl2_centered_coordinate_equation b v hb hv
  rw [sl2_inverse_final_scalar_identity b u v g hb hu hv,
    traceSquareScalar_centered b u hb hu,traceSquareScalar_centered b v hb hv]
  linear_combination -8*(b*(g:RMat)-(g:RMat)*b).det*hce +
    (8*(b*(g:RMat)-(g:RMat)*b).det-32*b.det)*hpe

theorem traceSquareScalar_linear_readout (b : RMat) (u v g : G) {s t p q : ℝ}
    (hb : Matrix.trace b=0) (hdet : b.det≠0)
    (hu : (u:RMat)=scalarAffine b s t) (hv : (v:RMat)=scalarAffine b p q) :
    let D := (b*(g:RMat)-(g:RMat)*b).det
    Matrix.trace ((v*u⁻¹*g*(v*u)*g⁻¹:G):RMat) =
      (3*D/(8*b.det))*traceSquareScalar u +
        (3*(4*b.det-D)/(8*b.det))*traceSquareScalar v := by
  have hh := traceSquareScalar_inverse_final b u v g hb hu hv
  dsimp only at hh ⊢
  field_simp
  nlinarith only [hh]

theorem commutator_conjugate_det (b : RMat) (g : G) (hb : Matrix.trace b=0) :
    let D := (b*(g:RMat)-(g:RMat)*b).det
    (b*matrixConjugationLinear g b-matrixConjugationLinear g b*b).det =
      D*(4*b.det-D) := by
  dsimp only
  have hx : Matrix.trace (matrixConjugationLinear g b)=0 := by
    rw [matrixConjugationLinear_trace,hb]
  have hdet : (matrixConjugationLinear g b).det=b.det := by
    simp only [matrixConjugationLinear_apply,Matrix.det_mul,
      Matrix.SpecialLinearGroup.det_coe,one_mul,mul_one]
  have ht : Matrix.trace (b*matrixConjugationLinear g b) =
      (b*(g:RMat)-(g:RMat)*b).det-2*b.det := by
    have hh := trace_adjoint_pair_coefficient b 1 g hb
    simpa only [matrixConjugationLinear_apply,Matrix.SpecialLinearGroup.coe_one,
      inv_one,one_mul,mul_one] using hh
  have hh := SL2Escape.pairSpanMatrix_det_trace_polynomial b (matrixConjugationLinear g b)
  rw [SL2Escape.pairSpanMatrix_det,hb,hx,hdet,ht] at hh
  rw [hh]
  ring

end TransposeFollowup.SL2Projection
