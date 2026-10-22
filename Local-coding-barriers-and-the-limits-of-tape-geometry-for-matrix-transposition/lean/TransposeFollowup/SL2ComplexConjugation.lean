import TransposeFollowup.SL2QuantitativeEscape

/-! Complex changes of basis as actual SL2 homomorphisms, with native
trace and determinant invariance and explicit real-complex compatibility. -/
namespace TransposeFollowup.SL2Escape
open Classical Matrix
set_option autoImplicit false
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℂ
local notation "M" => Matrix (Fin 2) (Fin 2) ℂ

def complexConjugation (P : Mˣ) : G →* G where
  toFun g := ⟨(P : M) * (g : M) * (↑P⁻¹ : M), by rw [Matrix.det_units_conj]; exact g.property⟩
  map_one' := by apply Subtype.ext; change (P : M) * 1 * (↑P⁻¹ : M) = 1; simp
  map_mul' a b := by
    apply Subtype.ext
    change (P : M) * ((a : M) * (b : M)) * (↑P⁻¹ : M) =
      ((P : M) * (a : M) * (↑P⁻¹ : M)) * ((P : M) * (b : M) * (↑P⁻¹ : M))
    calc
      _ = (P : M) * (a : M) * 1 * (b : M) * (↑P⁻¹ : M) := by noncomm_ring
      _ = (P : M) * (a : M) * ((↑P⁻¹ : M) * (P : M)) * (b : M) * (↑P⁻¹ : M) := by
        rw [Units.inv_mul]
      _ = _ := by noncomm_ring

theorem complexConjugation_trace (P : Mˣ) (g : G) :
    Matrix.trace (complexConjugation P g : M) = Matrix.trace (g : M) :=
  Matrix.trace_units_conj P (g : M)

theorem sl2_trace_conjugate {K : Type*} [Field K]
    (u g : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.trace ((u * g * u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) K) := by
  change Matrix.trace ((u : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
    ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = _
  rw [Matrix.trace_mul_cycle]
  have he : ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (u : Matrix (Fin 2) (Fin 2) K) = 1 :=
    congrArg (fun h : Matrix.SpecialLinearGroup (Fin 2) K => (h : Matrix (Fin 2) (Fin 2) K))
      (inv_mul_cancel u)
  rw [he, one_mul]

theorem complexify_trace (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (Matrix.SpecialLinearGroup.map Complex.ofRealHom g : M) =
      Complex.ofReal (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
  simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Complex.ofRealHom_eq_coe] using
    (AddMonoidHom.map_trace Complex.ofRealHom (g : Matrix (Fin 2) (Fin 2) ℝ)).symm

end TransposeFollowup.SL2Escape
