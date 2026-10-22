import TransposeFollowup.RealMobiusJacobian
import Mathlib.MeasureTheory.Function.L2Space

/-! The global weighted pullback preserves squared integrals and respects
almost-everywhere equality. The matrix product reverses pullback order. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
set_option autoImplicit false

noncomputable def weightedPullback (g : Group) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  |denom g x|⁻¹ *f (eval g x)

theorem weightedPullback_measurable (g : Group) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (weightedPullback g f) := by
  unfold weightedPullback
  have hw : Measurable (fun x => |denom g x|⁻¹) := by unfold denom; fun_prop
  exact hw.mul (hf.comp (measurable_eval g))

theorem weightedPullback_add (g : Group) (f h : ℝ → ℝ) (x : ℝ) :
    weightedPullback g (fun y => f y+h y) x=weightedPullback g f x+weightedPullback g h x := by
  simp only [weightedPullback,mul_add]

theorem weightedPullback_sub (g : Group) (f h : ℝ → ℝ) (x : ℝ) :
    weightedPullback g (fun y => f y-h y) x=weightedPullback g f x-weightedPullback g h x := by
  simp only [weightedPullback,mul_sub]

theorem weightedPullback_smul (g : Group) (f : ℝ → ℝ) (a x : ℝ) :
    weightedPullback g (fun y => a*f y) x=a*weightedPullback g f x := by
  unfold weightedPullback
  ring

theorem weightedPullback_square (g : Group) (f : ℝ → ℝ) (x : ℝ) :
    (weightedPullback g f x)^2=jacobian g x*(f (eval g x))^2 := by
  simp only [weightedPullback,mul_pow,inv_pow,sq_abs,jacobian,one_div]

theorem weightedPullback_integrable_square_iff (g : Group) (f : ℝ → ℝ) :
    Integrable (fun x => (weightedPullback g f x)^2) volume ↔ Integrable (fun x => (f x)^2) volume := by
  simp_rw [weightedPullback_square]
  exact integrable_jacobian_iff g (fun x => (f x)^2)

theorem weightedPullback_integral_square (g : Group) (f : ℝ → ℝ) :
    (∫ x,(weightedPullback g f x)^2)=∫ x,(f x)^2 := by
  simp_rw [weightedPullback_square]
  exact integral_jacobian g (fun x => (f x)^2)

theorem weightedPullback_one (f : ℝ → ℝ) (x : ℝ) : weightedPullback 1 f x=f x := by
  simp only [weightedPullback,denom_one,abs_one,inv_one,eval_one,one_mul]

theorem weightedPullback_mul (g h : Group) (f : ℝ → ℝ) {x : ℝ} (hx : x∈domain h) :
    weightedPullback (g*h) f x=weightedPullback h (weightedPullback g f) x := by
  unfold weightedPullback
  rw [denom_cocycle g h hx,abs_mul,mul_inv,eval_mul g h hx]
  ring

theorem weightedPullback_mul_ae (g h : Group) (f : ℝ → ℝ) :
    weightedPullback (g*h) f =ᵐ[volume] weightedPullback h (weightedPullback g f) :=
  (ae_domain h).mono (fun _ hx => weightedPullback_mul g h f hx)

theorem weightedPullback_ae_congr (g : Group) {f h : ℝ → ℝ} (heq : f =ᵐ[volume] h) :
    weightedPullback g f =ᵐ[volume] weightedPullback g h := by
  have hd : (fun x => (f x-h x)^2) =ᵐ[volume] (fun _ => (0:ℝ)) :=
    heq.mono (fun _ hx => by simp only [hx,sub_self,zero_pow (by decide : 2≠0)])
  have hi : Integrable (fun x => (f x-h x)^2) volume := (integrable_zero ℝ ℝ volume).congr hd.symm
  have hw := (weightedPullback_integrable_square_iff g (fun x => f x-h x)).2 hi
  have hz : (∫ x,(weightedPullback g (fun y => f y-h y) x)^2)=0 := by
    rw [weightedPullback_integral_square]
    exact (integral_congr_ae hd).trans (by simp)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hw).1 hz
  filter_upwards [hae] with x hx
  rw [weightedPullback_sub] at hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

theorem weightedPullback_memLp (g : Group) {f : ℝ → ℝ} (hf : Measurable f)
    (hLp : MemLp f 2 volume) : MemLp (weightedPullback g f) 2 volume :=
  (memLp_two_iff_integrable_sq (weightedPullback_measurable g hf).aestronglyMeasurable).2
    ((weightedPullback_integrable_square_iff g f).2 hLp.integrable_sq)

end TransposeFollowup.RealMobius
