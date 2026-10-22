import TransposeFollowup.RealMobiusAlgebra
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Global change of variables for the real fractional-linear action.
The map is bijective off at most one pole, a set of measure zero. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
set_option autoImplicit false

noncomputable def jacobian (g : Group) (x : ℝ) : ℝ := 1/(denom g x)^2

theorem measurable_eval (g : Group) : Measurable (eval g) := by
  unfold eval num denom
  fun_prop

theorem measurableSet_domain (g : Group) : MeasurableSet (domain g) := by
  unfold domain denom
  measurability

theorem domain_compl_finite (g : Group) : (domain g)ᶜ.Finite := by
  by_cases hc : g 1 0=0
  · have hd : g 1 1≠0 := by
      intro hz
      have ht := determinant g
      simp only [hc,hz,mul_zero,sub_self] at ht
      norm_num at ht
    have heq : domain g=univ := by ext x; simp [domain,denom,hc,hd]
    rw [heq,compl_univ]
    exact finite_empty
  · apply (finite_singleton (-g 1 1/g 1 0)).subset
    intro x hx
    have hz : denom g x=0 := by simpa only [domain,mem_compl_iff,mem_ofPred_eq,not_not] using hx
    rw [mem_singleton_iff]
    apply (eq_div_iff hc).2
    dsimp [denom] at hz
    linarith

theorem ae_domain (g : Group) : ∀ᵐ x ∂volume,x∈domain g := by
  rw [ae_iff]
  exact (domain_compl_finite g).measure_zero volume

theorem domain_ae_univ (g : Group) : domain g =ᵐ[volume] univ :=
  ae_eq_univ.mpr (ae_domain g)

theorem hasDerivAt_eval (g : Group) {x : ℝ} (hx : x∈domain g) :
    HasDerivAt (eval g) (jacobian g x) x := by
  have hn := ((hasDerivAt_id x).const_mul (g 0 0)).add_const (g 0 1)
  have hd := ((hasDerivAt_id x).const_mul (g 1 0)).add_const (g 1 1)
  have heq : g 0 0*(g 1 0*x+g 1 1)-(g 0 0*x+g 0 1)*g 1 0=1 := by
    nlinarith only [determinant g]
  have h := hn.div hd hx
  convert h using 1
  · rfl
  · dsimp [jacobian,denom]
    simp only [mul_one,heq]

theorem jacobian_nonneg (g : Group) (x : ℝ) : 0 ≤ jacobian g x := by
  unfold jacobian
  positivity

theorem jacobian_pos (g : Group) {x : ℝ} (hx : x∈domain g) : 0<jacobian g x :=
  one_div_pos.mpr (sq_pos_of_ne_zero hx)

theorem integral_jacobian (g : Group) (f : ℝ → ℝ) :
    (∫ x,jacobian g x*f (eval g x))=∫ y,f y := by
  have hi := integral_image_eq_integral_abs_deriv_smul (measurableSet_domain g)
    (fun x hx => (hasDerivAt_eval g hx).hasDerivWithinAt) (eval_injOn g) f
  simp only [image_domain,abs_of_nonneg (jacobian_nonneg g _),smul_eq_mul] at hi
  rw [← integral_eq_setIntegral (ae_domain g⁻¹) f,
    ← integral_eq_setIntegral (ae_domain g) (fun x => jacobian g x*f (eval g x))] at hi
  exact hi.symm

theorem integrable_jacobian_iff (g : Group) (f : ℝ → ℝ) :
    Integrable (fun x => jacobian g x*f (eval g x)) volume ↔ Integrable f volume := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul (measurableSet_domain g)
    (fun x hx => (hasDerivAt_eval g hx).hasDerivWithinAt) (eval_injOn g) f
  simp only [image_domain,abs_of_nonneg (jacobian_nonneg g _),smul_eq_mul] at hi
  rw [integrableOn_congr_set_ae (domain_ae_univ g⁻¹),integrableOn_univ,
    integrableOn_congr_set_ae (domain_ae_univ g),integrableOn_univ] at hi
  exact hi.symm

end TransposeFollowup.RealMobius
