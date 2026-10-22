import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The real-line fractional-linear action of actual determinant-one
matrices. Algebraic identities are stated off the possible pole. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
open scoped MatrixGroups
set_option autoImplicit false

abbrev Group := SL(2, ℝ)

def num (g : Group) (x : ℝ) : ℝ := g 0 0*x+g 0 1
def denom (g : Group) (x : ℝ) : ℝ := g 1 0*x+g 1 1
noncomputable def eval (g : Group) (x : ℝ) : ℝ := num g x/denom g x
def domain (g : Group) : Set ℝ := {x | denom g x≠0}

theorem determinant (g : Group) : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
  simpa only [Matrix.det_fin_two] using g.det_coe

theorem num_inverse (g : Group) (x : ℝ) : num g⁻¹ x=g 1 1*x-g 0 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [num,sub_eq_add_neg]

theorem denom_inverse (g : Group) (x : ℝ) : denom g⁻¹ x= -g 1 0*x+g 0 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [denom]

theorem num_one (x : ℝ) : num 1 x=x := by simp [num]
theorem denom_one (x : ℝ) : denom 1 x=1 := by simp [denom]
theorem eval_one (x : ℝ) : eval 1 x=x := by rw [eval,num_one,denom_one,div_one]

theorem num_mul (g h : Group) (x : ℝ) :
    num (g*h) x=g 0 0*num h x+g 0 1*denom h x := by
  simp [num,denom,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem denom_mul (g h : Group) (x : ℝ) :
    denom (g*h) x=g 1 0*num h x+g 1 1*denom h x := by
  simp [num,denom,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem num_inverse_eval (g : Group) {x : ℝ} (hx : x∈domain g) :
    num g⁻¹ (eval g x)=x/denom g x := by
  have hd : denom g x≠0 := hx
  rw [num_inverse,eval]
  field_simp
  dsimp [num,denom]
  have hdet := congrArg (fun z : ℝ => z*x) (determinant g)
  nlinarith only [hdet]

theorem denom_inverse_eval (g : Group) {x : ℝ} (hx : x∈domain g) :
    denom g⁻¹ (eval g x)=1/denom g x := by
  have hd : denom g x≠0 := hx
  rw [denom_inverse,eval]
  field_simp
  dsimp [num,denom]
  nlinarith only [determinant g]

theorem eval_mem_inverse_domain (g : Group) {x : ℝ} (hx : x∈domain g) :
    eval g x∈domain g⁻¹ := by
  change denom g⁻¹ (eval g x)≠0
  rw [denom_inverse_eval g hx]
  exact one_div_ne_zero hx

theorem inverse_eval_eval (g : Group) {x : ℝ} (hx : x∈domain g) :
    eval g⁻¹ (eval g x)=x := by
  rw [eval,num_inverse_eval g hx,denom_inverse_eval g hx]
  have hd : denom g x≠0 := hx
  field_simp

theorem eval_inverse_eval (g : Group) {x : ℝ} (hx : x∈domain g⁻¹) :
    eval g (eval g⁻¹ x)=x := by
  simpa only [inv_inv] using inverse_eval_eval g⁻¹ hx

theorem eval_injOn (g : Group) : InjOn (eval g) (domain g) := by
  intro x hx y hy h
  have hi := congrArg (eval g⁻¹) h
  simpa only [inverse_eval_eval g hx,inverse_eval_eval g hy] using hi

theorem image_domain (g : Group) : eval g '' domain g=domain g⁻¹ := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact eval_mem_inverse_domain g hx
  · intro y hy
    refine ⟨eval g⁻¹ y,?_,eval_inverse_eval g hy⟩
    simpa only [inv_inv] using eval_mem_inverse_domain g⁻¹ hy

theorem denom_cocycle (g h : Group) {x : ℝ} (hx : x∈domain h) :
    denom (g*h) x=denom g (eval h x)*denom h x := by
  have hd : denom h x≠0 := hx
  rw [denom_mul]
  change _ = (g 1 0*(num h x/denom h x)+g 1 1)*denom h x
  rw [add_mul,mul_assoc,div_mul_cancel₀ _ hd]

theorem eval_mul (g h : Group) {x : ℝ} (hx : x∈domain h) :
    eval (g*h) x=eval g (eval h x) := by
  have hd : denom h x≠0 := hx
  rw [eval,num_mul,denom_mul]
  change _ = (g 0 0*(num h x/denom h x)+g 0 1)/(g 1 0*(num h x/denom h x)+g 1 1)
  rw [mul_div,div_add' _ _ _ hd,mul_div,div_add' _ _ _ hd]
  field_simp

end TransposeFollowup.RealMobius
