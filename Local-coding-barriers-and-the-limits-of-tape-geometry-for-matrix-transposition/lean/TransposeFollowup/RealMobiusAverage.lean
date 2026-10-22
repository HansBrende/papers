import TransposeFollowup.RealMobiusL2

/-! The finite symmetric average is a continuous linear contraction,
symmetric for the real inner product. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

noncomputable def actionCLM (g : Group) : RealL2 →L[ℝ] RealL2 :=
  (unitaryAction g).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def averageOperator {c : ℕ} (G : Fin c → Group) : RealL2 →L[ℝ] RealL2 :=
  (2*(c:ℝ))⁻¹ • ∑ p : Fin c,(actionCLM (G p)+actionCLM (G p)⁻¹)

theorem averageOperator_apply {c : ℕ} (G : Fin c → Group) (f : RealL2) :
    averageOperator G f=(2*(c:ℝ))⁻¹ •
      ∑ p : Fin c,(unitaryAction (G p) f+unitaryAction (G p)⁻¹ f) := by
  simp [averageOperator,actionCLM]

theorem unitaryAction_adjoint (g : Group) (f h : RealL2) :
    inner ℝ (unitaryAction g f) h=inner ℝ f (unitaryAction g⁻¹ h) := by
  have hi := unitaryAction_inner g f (unitaryAction g⁻¹ h)
  rw [← unitaryAction_mul,mul_inv_cancel,unitaryAction_one] at hi
  exact hi

theorem averageOperator_symmetric {c : ℕ} (G : Fin c → Group) (f h : RealL2) :
    inner ℝ (averageOperator G f) h=inner ℝ f (averageOperator G h) := by
  simp only [averageOperator_apply,real_inner_smul_left,inner_smul_right,sum_inner,inner_sum,
    inner_add_left,inner_add_right,unitaryAction_adjoint,inv_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact add_comm _ _

theorem averageOperator_norm_le {c : ℕ} (G : Fin c → Group) (hc : 0<c) (f : RealL2) :
    ‖averageOperator G f‖ ≤ ‖f‖ := by
  have hc' : (0:ℝ)<c := by exact_mod_cast hc
  have hi : (0:ℝ) ≤ (2*(c:ℝ))⁻¹ := by positivity
  have hb : ‖∑ p : Fin c,(unitaryAction (G p) f+unitaryAction (G p)⁻¹ f)‖ ≤ (c:ℝ)*(2*‖f‖) := by
    calc
      _ ≤ ∑ p : Fin c,‖unitaryAction (G p) f+unitaryAction (G p)⁻¹ f‖ := norm_sum_le _ _
      _ ≤ ∑ p : Fin c,(‖unitaryAction (G p) f‖+‖unitaryAction (G p)⁻¹ f‖) :=
        Finset.sum_le_sum (fun _ _ => norm_add_le _ _)
      _ = _ := by simp [two_mul,mul_add]
  rw [averageOperator_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hi]
  calc
    _ ≤ (2*(c:ℝ))⁻¹ *((c:ℝ)*(2*‖f‖)) := mul_le_mul_of_nonneg_left hb hi
    _ = ‖f‖ := by field_simp

end TransposeFollowup.RealMobius
