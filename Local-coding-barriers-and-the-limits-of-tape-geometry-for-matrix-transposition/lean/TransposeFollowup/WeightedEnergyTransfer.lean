import TransposeFollowup.WeightedIndicatorError
import Mathlib.MeasureTheory.Function.L2Space

/-! Integrability and energy contraction under the actual weighted pullback,
and transfer of an error bound between two square-integrable functions. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

namespace RationalMobius
variable (G : RationalMobius)

theorem weightedPullback_sub_smul (f g : ℝ → ℝ) (c x : ℝ) :
    G.weightedPullback (fun y => f y-c*g y) x=
      G.weightedPullback f x-c*G.weightedPullback g x := by
  unfold weightedPullback
  ring

theorem weighted_square_integrableOn {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (G.lo:ℝ) G.hi) {f : ℝ → ℝ}
    (hf : Integrable (fun x => (f x)^2) volume) :
    IntegrableOn (fun x => (G.weightedPullback f x)^2) A := by
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul hA
    (fun x hx => (G.hasDerivAt_eval (hsub hx)).hasDerivWithinAt)
    (G.strictMonoOn_eval.injOn.mono hsub) (fun y => (f y)^2)).1 hf.integrableOn
  apply hi.congr_fun ?_ hA
  intro x hx
  change |G.derivative x| *(f (G.eval x))^2=(G.weightedPullback f x)^2
  rw [abs_of_pos (G.derivative_pos (hsub hx)),G.weightedPullback_square (hsub hx)]

theorem weighted_square_integral_le {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (G.lo:ℝ) G.hi) {f : ℝ → ℝ}
    (hf : Integrable (fun x => (f x)^2) volume) :
    (∫ x in A,(G.weightedPullback f x)^2) ≤ ∫ x,(f x)^2 := by
  rw [G.weightedPullback_square_integral hA hsub f]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))

theorem weighted_error_integrableOn {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (G.lo:ℝ) G.hi) {f : ℝ → ℝ} (hf : Measurable f)
    (hsq : Integrable (fun x => (f x)^2) volume) :
    IntegrableOn (fun x => (G.weightedPullback f x-f x)^2) A := by
  have hw := (memLp_two_iff_integrable_sq (G.measurable_weightedPullback hf).aestronglyMeasurable).2
    (G.weighted_square_integrableOn hA hsub hsq)
  have hi := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
    (hsq.integrableOn (s := A))
  exact (hw.sub hi).integrable_sq

theorem weighted_projection_transfer {A : Set ℝ} (hA : MeasurableSet A)
    (hsub : A⊆Icc (G.lo:ℝ) G.hi) {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun x => (f x)^2) volume) (hg2 : Integrable (fun x => (g x)^2) volume) :
    (∫ x in A,(G.weightedPullback f x-f x)^2) ≤
      3*(∫ x in A,(G.weightedPullback g x-g x)^2)+6*(∫ x,(f x-g x)^2) := by
  let e : ℝ → ℝ := fun x => f x-g x
  have he2 : Integrable (fun x => (e x)^2) volume :=
    (((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2).sub
      ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2)).integrable_sq
  have hF := G.weighted_error_integrableOn hA hsub hf hf2
  have hG := G.weighted_error_integrableOn hA hsub hg hg2
  have hW := G.weighted_square_integrableOn hA hsub he2
  have hE := he2.integrableOn (s := A)
  have hR : IntegrableOn (fun x => 3*(G.weightedPullback g x-g x)^2+
      3*(G.weightedPullback e x)^2+3*(e x)^2) A :=
    ((hG.const_mul 3).add (hW.const_mul 3)).add (hE.const_mul 3)
  have hp : ∀ x : ℝ,(G.weightedPullback f x-f x)^2 ≤
      3*(G.weightedPullback g x-g x)^2+3*(G.weightedPullback e x)^2+3*(e x)^2 := by
    intro x
    let a := G.weightedPullback g x-g x
    let b := G.weightedPullback e x
    let c := -e x
    have hid : G.weightedPullback f x-f x=a+b+c := by
      dsimp [a,b,c,e,weightedPullback]
      ring
    have hc : (e x)^2=c^2 := by dsimp [c]; ring
    rw [hid,hc]
    change (a+b+c)^2 ≤ 3*a^2+3*b^2+3*c^2
    nlinarith only [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hb := setIntegral_mono_on hF hR hA (fun x _ => hp x)
  have hi : (∫ x in A,3*(G.weightedPullback g x-g x)^2+
      3*(G.weightedPullback e x)^2+3*(e x)^2)=
      3*(∫ x in A,(G.weightedPullback g x-g x)^2)+
      3*(∫ x in A,(G.weightedPullback e x)^2)+3*(∫ x in A,(e x)^2) := by
    rw [integral_add (f := fun x => 3*(G.weightedPullback g x-g x)^2+3*(G.weightedPullback e x)^2)
      (g := fun x => 3*(e x)^2) ((hG.const_mul 3).add (hW.const_mul 3)) (hE.const_mul 3)]
    rw [integral_add (f := fun x => 3*(G.weightedPullback g x-g x)^2)
      (g := fun x => 3*(G.weightedPullback e x)^2) (hG.const_mul 3) (hW.const_mul 3)]
    rw [integral_const_mul,integral_const_mul,integral_const_mul]
  rw [hi] at hb
  have hw := G.weighted_square_integral_le hA hsub he2
  have he' := setIntegral_le_integral (s := A) he2
    (Filter.Eventually.of_forall (fun x => sq_nonneg (e x)))
  change _ ≤ 3*(∫ x in A,(G.weightedPullback g x-g x)^2)+6*(∫ x,(e x)^2)
  linarith

end RationalMobius

namespace RationalUnitMobius

theorem NearIdentity.weighted_local_error {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) {f : ℝ → ℝ} (hf : Measurable f)
    (hc : IntegrableOn (fun x => (f (G.whole.eval x)-f x)^2) (Icc (0:ℝ) 1))
    (hi : IntegrableOn (fun x => (f x)^2) (Icc (0:ℝ) 1)) :
    IntegrableOn (fun x => (G.whole.weightedPullback f x-f x)^2) (Icc (0:ℝ) 1) ∧
    (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback f x-f x)^2) ≤
      2*(1+32*eta)*(∫ x in Icc (0:ℝ) 1,(f (G.whole.eval x)-f x)^2)+
      2*(32*eta)^2*(∫ x in Icc (0:ℝ) 1,(f x)^2) := by
  have hR : IntegrableOn (fun x => 2*(1+32*eta)*(f (G.whole.eval x)-f x)^2+
      2*(32*eta)^2*(f x)^2) (Icc (0:ℝ) 1) :=
    (hc.const_mul _).add (hi.const_mul _)
  have hm : Measurable (fun x => (G.whole.weightedPullback f x-f x)^2) :=
    ((G.whole.measurable_weightedPullback hf).sub hf).pow_const 2
  have hW : IntegrableOn (fun x => (G.whole.weightedPullback f x-f x)^2) (Icc (0:ℝ) 1) := by
    apply hR.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact h.weighted_difference_pointwise he f hx
  refine ⟨hW,?_⟩
  have hb := setIntegral_mono_on hW hR measurableSet_Icc
    (fun x hx => h.weighted_difference_pointwise he f hx)
  calc
    _ ≤ ∫ x in Icc (0:ℝ) 1,2*(1+32*eta)*(f (G.whole.eval x)-f x)^2+
        2*(32*eta)^2*(f x)^2 := hb
    _ = _ := by
      rw [integral_add (f := fun x => 2*(1+32*eta)*(f (G.whole.eval x)-f x)^2)
        (g := fun x => 2*(32*eta)^2*(f x)^2) (hc.const_mul _) (hi.const_mul _),
        integral_const_mul,integral_const_mul]

end RationalUnitMobius
end TransposeFollowup
