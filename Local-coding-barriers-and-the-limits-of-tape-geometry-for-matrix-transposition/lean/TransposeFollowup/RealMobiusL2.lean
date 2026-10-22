import TransposeFollowup.RealMobiusWeighted
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The real determinant-one matrix group acts by linear isometric
equivalences on L2. The inverse in the definition restores product order. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
set_option autoImplicit false

noncomputable abbrev RealL2 := Lp ℝ 2 (volume : Measure ℝ)

noncomputable def pullbackLp (g : Group) (f : RealL2) : RealL2 :=
  (weightedPullback_memLp g (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).toLp (weightedPullback g f)

theorem pullbackLp_coe (g : Group) (f : RealL2) :
    ⇑(pullbackLp g f) =ᵐ[volume] weightedPullback g f := MemLp.coeFn_toLp _

theorem pullbackLp_add (g : Group) (f h : RealL2) :
    pullbackLp g (f+h)=pullbackLp g f+pullbackLp g h := by
  apply Lp.ext
  have ha : (fun x => (f+h) x) =ᵐ[volume] (fun x => f x+h x) := Lp.coeFn_add f h
  filter_upwards [pullbackLp_coe g (f+h),weightedPullback_ae_congr g ha,
    Lp.coeFn_add (pullbackLp g f) (pullbackLp g h),pullbackLp_coe g f,pullbackLp_coe g h]
    with x h₁ h₂ h₃ h₄ h₅
  change _ = pullbackLp g f x+pullbackLp g h x at h₃
  rw [h₁,h₂,weightedPullback_add,← h₄,← h₅]
  exact h₃.symm

theorem pullbackLp_smul (g : Group) (a : ℝ) (f : RealL2) :
    pullbackLp g (a • f)=a • pullbackLp g f := by
  apply Lp.ext
  have ha : (fun x => (a • f) x) =ᵐ[volume] (fun x => a*f x) := Lp.coeFn_smul a f
  filter_upwards [pullbackLp_coe g (a • f),weightedPullback_ae_congr g ha,
    Lp.coeFn_smul a (pullbackLp g f),pullbackLp_coe g f] with x h₁ h₂ h₃ h₄
  change _ = a*pullbackLp g f x at h₃
  rw [h₁,h₂,weightedPullback_smul,← h₄]
  exact h₃.symm

theorem realL2_norm_sq (f : RealL2) : ‖f‖^2=∫ x,(f x)^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem pullbackLp_norm (g : Group) (f : RealL2) : ‖pullbackLp g f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [realL2_norm_sq,realL2_norm_sq]
  calc
    _ = ∫ x,(weightedPullback g f x)^2 :=
      integral_congr_ae ((pullbackLp_coe g f).mono (fun _ hx => by simp only [hx]))
    _ = _ := weightedPullback_integral_square g f

theorem pullbackLp_one (f : RealL2) : pullbackLp 1 f=f := by
  apply Lp.ext
  exact (pullbackLp_coe 1 f).trans (Filter.Eventually.of_forall (weightedPullback_one f))

theorem pullbackLp_mul (g h : Group) (f : RealL2) :
    pullbackLp (g*h) f=pullbackLp h (pullbackLp g f) := by
  apply Lp.ext
  exact (pullbackLp_coe (g*h) f).trans ((weightedPullback_mul_ae g h f).trans
    ((weightedPullback_ae_congr h (pullbackLp_coe g f)).symm.trans
      (pullbackLp_coe h (pullbackLp g f)).symm))

theorem pullbackLp_inverse_left (g : Group) (f : RealL2) :
    pullbackLp g⁻¹ (pullbackLp g f)=f := by
  rw [← pullbackLp_mul,mul_inv_cancel,pullbackLp_one]

theorem pullbackLp_inverse_right (g : Group) (f : RealL2) :
    pullbackLp g (pullbackLp g⁻¹ f)=f := by
  rw [← pullbackLp_mul,inv_mul_cancel,pullbackLp_one]

noncomputable def pullbackIsometry (g : Group) : RealL2 ≃ₗᵢ[ℝ] RealL2 where
  toFun := pullbackLp g
  invFun := pullbackLp g⁻¹
  left_inv := pullbackLp_inverse_left g
  right_inv := pullbackLp_inverse_right g
  map_add' := pullbackLp_add g
  map_smul' := pullbackLp_smul g
  norm_map' := pullbackLp_norm g

noncomputable def unitaryAction (g : Group) : RealL2 ≃ₗᵢ[ℝ] RealL2 := pullbackIsometry g⁻¹

theorem unitaryAction_one (f : RealL2) : unitaryAction 1 f=f := by
  change pullbackLp (1⁻¹) f=f
  rw [inv_one,pullbackLp_one]

theorem unitaryAction_mul (g h : Group) (f : RealL2) :
    unitaryAction (g*h) f=unitaryAction g (unitaryAction h f) := by
  change pullbackLp (g*h)⁻¹ f=pullbackLp g⁻¹ (pullbackLp h⁻¹ f)
  rw [mul_inv_rev,pullbackLp_mul]

/-- The actual group representation by real linear isometric equivalences. -/
noncomputable def unitaryRepresentation : Group →* (RealL2 ≃ₗᵢ[ℝ] RealL2) where
  toFun := unitaryAction
  map_one' := by ext f : 1; exact unitaryAction_one f
  map_mul' := by intro g h; ext f : 1; exact unitaryAction_mul g h f

theorem unitaryAction_coe (g : Group) (f : RealL2) :
    ⇑(unitaryAction g f) =ᵐ[volume] weightedPullback g⁻¹ f := pullbackLp_coe g⁻¹ f

theorem unitaryAction_inner (g : Group) (f h : RealL2) :
    inner ℝ (unitaryAction g f) (unitaryAction g h)=inner ℝ f h :=
  (unitaryAction g).inner_map_map f h

end TransposeFollowup.RealMobius
