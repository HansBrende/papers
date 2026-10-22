import TransposeFollowup.MobiusDifferentialTransport

/-! Actual SL(2,R) matrices for translations, lower unipotents and inversion. -/
namespace TransposeFollowup.RealMobius
open Classical
set_option autoImplicit false

def upperUnipotent (t : ℝ) : Group :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

def lowerUnipotent (t : ℝ) : Group :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

def inversionMatrix : Group :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem scaledPullback_upperUnipotent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (f : ℝ → E) (x : ℝ) :
    scaledPullback (upperUnipotent t) f x = f (x + t) := by
  simp [scaledPullback, upperUnipotent, denom, eval, num]

theorem lowerUnipotent_eq_conjugate (t : ℝ) :
    lowerUnipotent t = inversionMatrix * upperUnipotent (-t) * inversionMatrix⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change !![1, 0; t, 1] = (!![0, -1; 1, 0] * !![1, -t; 0, 1]) * !![0, -(-1); -(1), 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end TransposeFollowup.RealMobius
