import TransposeFollowup.RationalUnitRestriction
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Derivatives and actual change of variables for the existing rational
Mobius maps. The Jacobian theorem is reused from Mathlib. -/
namespace TransposeFollowup
open Set MeasureTheory
set_option autoImplicit false

namespace RationalMobius
variable (F : RationalMobius)

noncomputable def derivative (x : ℝ) : ℝ := (F.delta:ℝ)/(F.denom x)^2

theorem hasDerivAt_eval {x : ℝ} (hx : x∈Icc (F.lo:ℝ) F.hi) :
    HasDerivAt F.eval (F.derivative x) x := by
  have hn := ((hasDerivAt_id x).const_mul (F.a:ℝ)).add_const (F.b:ℝ)
  have hd := ((hasDerivAt_id x).const_mul (F.c:ℝ)).add_const (F.d:ℝ)
  have h := hn.div hd (F.denom_pos hx).ne'
  convert h using 1
  · rfl
  · dsimp [derivative,delta,denom]
    push_cast
    ring

theorem derivative_pos {x : ℝ} (hx : x∈Icc (F.lo:ℝ) F.hi) : 0<F.derivative x :=
  div_pos F.delta_pos (sq_pos_of_pos (F.denom_pos hx))

theorem continuousOn_derivative : ContinuousOn F.derivative (Icc (F.lo:ℝ) F.hi) := by
  unfold derivative denom
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact pow_ne_zero 2 (F.denom_pos hx).ne'

theorem measurableSet_image_eval {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (F.lo:ℝ) F.hi) : MeasurableSet (F.eval '' A) :=
  hA.image_of_monotoneOn (F.strictMonoOn_eval.monotoneOn.mono hsub)

theorem integral_image_eval {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (F.lo:ℝ) F.hi) (g : ℝ → ℝ) :
    (∫ y in F.eval '' A,g y) = ∫ x in A,F.derivative x*g (F.eval x) := by
  rw [integral_image_eq_integral_abs_deriv_smul hA
    (fun x hx => (F.hasDerivAt_eval (hsub hx)).hasDerivWithinAt)
    (F.strictMonoOn_eval.injOn.mono hsub) g]
  apply setIntegral_congr_fun hA
  intro x hx
  change |F.derivative x| *g (F.eval x)=F.derivative x*g (F.eval x)
  rw [abs_of_pos (F.derivative_pos (hsub hx))]

theorem volume_real_image_eval {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (F.lo:ℝ) F.hi) :
    volume.real (F.eval '' A)=∫ x in A,F.derivative x := by
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using F.integral_image_eval hA hsub (fun _ => 1)

theorem integrableOn_derivative {A : Set ℝ} (hsub : A⊆Icc (F.lo:ℝ) F.hi) :
    IntegrableOn F.derivative A :=
  F.continuousOn_derivative.integrableOn_Icc.mono_set hsub

noncomputable def weightedPullback (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (F.derivative x)*f (F.eval x)

theorem weightedPullback_square {x : ℝ} (hx : x∈Icc (F.lo:ℝ) F.hi) (f : ℝ → ℝ) :
    (F.weightedPullback f x)^2=F.derivative x*(f (F.eval x))^2 := by
  rw [weightedPullback,mul_pow,Real.sq_sqrt (F.derivative_pos hx).le]

theorem weightedPullback_square_integral {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (F.lo:ℝ) F.hi) (f : ℝ → ℝ) :
    (∫ x in A,(F.weightedPullback f x)^2)=∫ y in F.eval '' A,(f y)^2 := by
  rw [F.integral_image_eval hA hsub]
  apply setIntegral_congr_fun hA
  exact fun x hx => F.weightedPullback_square (hsub hx) f

end RationalMobius

namespace RationalUnitMobius
variable (F : RationalUnitMobius)

theorem inverse_inverse : F.inverse.inverse=F := by
  cases F
  simp only [inverse,neg_neg]

theorem inverse_delta : F.inverse.whole.delta=F.whole.delta := by
  dsimp [whole,inverse,RationalMobius.delta]
  ring

theorem inverse_denom_eval {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    F.inverse.whole.denom (F.whole.eval x)=(F.whole.delta:ℝ)/F.whole.denom x := by
  have hq : (F.c:ℝ)*x+F.d≠0 := (F.whole_denom_pos hx).ne'
  dsimp [RationalMobius.denom,RationalMobius.eval,RationalMobius.delta,whole,inverse]
  push_cast
  field_simp
  ring

theorem inverse_eval_eval {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    F.inverse.whole.eval (F.whole.eval x)=x := by
  have hq : F.whole.denom x≠0 := (F.whole_denom_pos hx).ne'
  have hnum : (F.d:ℝ)*F.whole.eval x-F.b=(F.whole.delta:ℝ)*x/F.whole.denom x := by
    apply (eq_div_iff hq).2
    have hv : F.whole.eval x*F.whole.denom x=(F.a:ℝ)*x+F.b := div_mul_cancel₀ _ hq
    calc
      _ = (F.d:ℝ)*(F.whole.eval x*F.whole.denom x)-(F.b:ℝ)*F.whole.denom x := by ring
      _ = _ := by rw [hv]; dsimp [RationalMobius.delta,RationalMobius.denom,whole]; push_cast; ring
  have hd : (F.whole.delta:ℝ)≠0 := F.whole.delta_pos.ne'
  calc
    _ = ((F.d:ℝ)*F.whole.eval x-F.b)/F.inverse.whole.denom (F.whole.eval x) := by
      rw [F.inverse_eval]
      simp only [RationalMobius.denom,whole,inverse,Rat.cast_neg]
    _ = ((F.whole.delta:ℝ)*x/F.whole.denom x)/((F.whole.delta:ℝ)/F.whole.denom x) := by
      rw [hnum,F.inverse_denom_eval hx]
    _ = x := by field_simp

theorem eval_inverse_eval {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    F.whole.eval (F.inverse.whole.eval x)=x := by
  simpa only [inverse_inverse] using F.inverse.inverse_eval_eval hx

theorem inverse_derivative_eval {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    F.inverse.whole.derivative (F.whole.eval x)*F.whole.derivative x=1 := by
  unfold RationalMobius.derivative
  rw [F.inverse_denom_eval hx,F.inverse_delta]
  have hd : (F.whole.delta:ℝ)≠0 := F.whole.delta_pos.ne'
  have hq : F.whole.denom x≠0 := (F.whole_denom_pos hx).ne'
  field_simp

theorem unit_preimage_eq_inverse_image {A : Set ℝ} (hunit : A⊆Icc (0:ℝ) 1)
    (hinv : MapsTo F.inverse.whole.eval A (Icc (0:ℝ) 1)) :
    Icc (0:ℝ) 1 ∩ F.whole.eval ⁻¹' A=F.inverse.whole.eval '' A := by
  ext x
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨F.whole.eval x,hy,F.inverse_eval_eval hx⟩
  · rintro ⟨y,hy,rfl⟩
    refine ⟨hinv hy,?_⟩
    change F.whole.eval (F.inverse.whole.eval y)∈A
    rw [F.eval_inverse_eval (hunit hy)]
    exact hy

end RationalUnitMobius
end TransposeFollowup
