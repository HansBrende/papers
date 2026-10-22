import TransposeFollowup.IndicatorPullbackError

/-! Almost-invariance of the trimmed indicator under the actual
square-root-Jacobian weighted pullback. Integrability is proved before
using the Bochner integral inequality. Centering is a separate obligation. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped symmDiff
set_option autoImplicit false

theorem indicator_one_square (A : Set ℝ) (x : ℝ) :
    (A.indicator (fun _ => (1:ℝ)) x)^2=A.indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x∈A <;> simp [hx]

theorem indicator_one_square_integrable {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) :
    Integrable (fun x => (A.indicator (fun _ => (1:ℝ)) x)^2) volume := by
  have he : (fun x => (A.indicator (fun _ => (1:ℝ)) x)^2)=A.indicator (fun _ => (1:ℝ)) :=
    funext (indicator_one_square A)
  rw [he]
  exact (integrableOn_const (unit_subset_volume_ne_top hunit)).integrable_indicator hA

theorem indicator_one_square_unit_integral {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) :
    (∫ x in Icc (0:ℝ) 1,(A.indicator (fun _ => (1:ℝ)) x)^2)=volume.real A := by
  simp_rw [indicator_one_square]
  rw [integral_indicator_const (1:ℝ) hA,measureReal_restrict_apply hA,
    smul_eq_mul,mul_one,inter_eq_left.mpr hunit]

namespace RationalMobius
variable (G : RationalMobius)

theorem measurable_eval : Measurable G.eval := by unfold eval; fun_prop

theorem measurable_derivative : Measurable G.derivative := by
  unfold derivative denom
  fun_prop

theorem measurable_weightedPullback {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (G.weightedPullback f) := by
  unfold weightedPullback
  exact (G.measurable_derivative.sqrt).mul (hf.comp G.measurable_eval)

end RationalMobius

namespace RationalUnitMobius

theorem NearIdentity.weighted_difference_pointwise {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) (f : ℝ → ℝ)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    (G.whole.weightedPullback f x-f x)^2 ≤
      2*(1+32*eta)*(f (G.whole.eval x)-f x)^2+2*(32*eta)^2*(f x)^2 := by
  let s := Real.sqrt (G.whole.derivative x)
  let u := f (G.whole.eval x)
  let v := f x
  have hs : s^2=G.whole.derivative x :=
    Real.sq_sqrt (G.whole.derivative_pos (by simpa [whole] using hx)).le
  have hd : G.whole.derivative x ≤ 1+32*eta := by
    have hd' := (abs_le.mp (h.derivative_error he hx)).2
    linarith
  have he0 : 0 ≤ 32*eta := mul_nonneg (by norm_num) h.nonneg
  have hw : (s-1)^2 ≤ (32*eta)^2 := by
    have hb := (sq_le_sq₀ (abs_nonneg (s-1)) he0).2 (h.sqrt_derivative_error he hx)
    simpa only [sq_abs] using hb
  change (s*u-v)^2 ≤ 2*(1+32*eta)*(u-v)^2+2*(32*eta)^2*v^2
  calc
    _ = (s*(u-v)+(s-1)*v)^2 := by ring
    _ ≤ 2*(s*(u-v))^2+2*((s-1)*v)^2 := by nlinarith only [sq_nonneg (s*(u-v)-(s-1)*v)]
    _ = 2*G.whole.derivative x*(u-v)^2+2*(s-1)^2*v^2 := by rw [mul_pow,mul_pow,hs]; ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) (sq_nonneg _))

theorem NearIdentity.weighted_indicator_error {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (hinv : MapsTo G.inverse.whole.eval A (Icc (0:ℝ) 1)) :
    IntegrableOn (fun x => (G.whole.weightedPullback (A.indicator (fun _ => (1:ℝ))) x-
      A.indicator (fun _ => (1:ℝ)) x)^2) (Icc (0:ℝ) 1) ∧
    (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (A.indicator (fun _ => (1:ℝ))) x-
      A.indicator (fun _ => (1:ℝ)) x)^2) ≤
      2*(1+32*eta)*volume.real ((G.inverse.whole.eval '' A) ∆ A)+
        2*(32*eta)^2*volume.real A := by
  let f := A.indicator (fun _ => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  have hc := G.indicator_comp_square_integrableOn hA hunit hinv
  have hi := (indicator_one_square_integrable hA hunit).integrableOn (s := Icc (0:ℝ) 1)
  have hR : IntegrableOn (fun x => 2*(1+32*eta)*(f (G.whole.eval x)-f x)^2+
      2*(32*eta)^2*(f x)^2) (Icc (0:ℝ) 1) :=
    (hc.const_mul (2*(1+32*eta))).add (hi.const_mul (2*(32*eta)^2))
  have hw : Measurable (fun x => (G.whole.weightedPullback f x-f x)^2) :=
    ((G.whole.measurable_weightedPullback hf).sub hf).pow_const 2
  have hW : IntegrableOn (fun x => (G.whole.weightedPullback f x-f x)^2) (Icc (0:ℝ) 1) := by
    apply hR.mono' hw.aestronglyMeasurable
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
        (g := fun x => 2*(32*eta)^2*(f x)^2)
        (hc.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul]
      dsimp only [f]
      rw [G.indicator_comp_square_integral hA hunit hinv,indicator_one_square_unit_integral hA hunit]

theorem augmented_small_expansion_weighted_indicator_error {c : ℕ}
    (F : Fin c → RationalUnitMobius) (t : ℚ) (ht : |t|<1) (p : Fin c)
    {eta r sigma : ℝ} (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8) (hr : 8*eta ≤ r)
    {A T : Set ℝ} (hT : MeasurableSet T) (hunit : A⊆Icc (0:ℝ) 1)
    (hTA : T⊆A) (hcentral : T⊆Icc r (1-r))
    (hsmall : volume.real (restrictedImageUnion (augmentedFamily F t ht) A) ≤
      (1+sigma)*volume.real A) :
    let B := 2*sigma*volume.real A+2*(volume.real A-volume.real T)+32*eta*volume.real T
    (∫ x in Icc (0:ℝ) 1,((F p).whole.weightedPullback (T.indicator (fun _ => (1:ℝ))) x-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤ 2*(1+32*eta)*B+2*(32*eta)^2*volume.real T ∧
    (∫ x in Icc (0:ℝ) 1,((F p).inverse.whole.weightedPullback (T.indicator (fun _ => (1:ℝ))) x-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤ 2*(1+32*eta)*B+2*(32*eta)^2*volume.real T := by
  have hb := augmented_small_expansion_symmDiff F t ht p hnear he hr hT hunit hTA hcentral hsmall
  have hp : MapsTo (F p).whole.eval T (Icc (0:ℝ) 1) :=
    fun x hx => hnear.mapsTo_central he hr (hcentral hx)
  have hm : MapsTo (F p).inverse.whole.eval T (Icc (0:ℝ) 1) :=
    fun x hx => hnear.inverse.mapsTo_central he hr (hcentral hx)
  have he0 : 0 ≤ 2*(1+32*eta) := by have h := hnear.nonneg; positivity
  constructor
  · exact (hnear.weighted_indicator_error he hT (hTA.trans hunit) hm).2.trans
      (add_le_add (mul_le_mul_of_nonneg_left hb.2 he0) le_rfl)
  · have hw := (hnear.inverse.weighted_indicator_error he hT (hTA.trans hunit)
      (by simpa only [inverse_inverse] using hp)).2
    rw [inverse_inverse] at hw
    exact hw.trans (add_le_add (mul_le_mul_of_nonneg_left hb.1 he0) le_rfl)

theorem augmented_central_trim_weighted_indicator_error {c K m : ℕ}
    (F : Fin c → RationalUnitMobius) (hK : 2 ≤ K) (hm : 2*m ≤ K) (p : Fin c)
    {eta sigma delta : ℝ} (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8)
    (hr : 8*eta ≤ (m:ℝ)/K) {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let T := gridTrim A (centralCells K m)
    let C := 2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta
    (∫ x in Icc (0:ℝ) 1,((F p).whole.weightedPullback (T.indicator (fun _ => (1:ℝ))) x-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤ (2*(1+32*eta)*C+2*(32*eta)^2)*volume.real A ∧
    (∫ x in Icc (0:ℝ) 1,((F p).inverse.whole.weightedPullback (T.indicator (fun _ => (1:ℝ))) x-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤ (2*(1+32*eta)*C+2*(32*eta)^2)*volume.real A := by
  let T := gridTrim A (centralCells K m)
  let C := 2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta
  have hb := augmented_central_trim_symmDiff F hK hm p hnear he hr hA hunit huniform hsmall
  have hcentral := (centralTrim_loss_bound (by omega : 0<K) hm hA hunit delta huniform).1
  have hp : MapsTo (F p).whole.eval T (Icc (0:ℝ) 1) :=
    fun x hx => hnear.mapsTo_central he hr (hcentral hx)
  have hn : MapsTo (F p).inverse.whole.eval T (Icc (0:ℝ) 1) :=
    fun x hx => hnear.inverse.mapsTo_central he hr (hcentral hx)
  have hmass : volume.real T ≤ volume.real A :=
    measureReal_mono (gridTrim_subset A _) (unit_subset_volume_ne_top hunit)
  have hweight := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg (32*eta)))
  have he0 : 0 ≤ 2*(1+32*eta) := by have h := hnear.nonneg; positivity
  have hcoef : 2*(1+32*eta)*(C*volume.real A)+2*(32*eta)^2*volume.real A=
      (2*(1+32*eta)*C+2*(32*eta)^2)*volume.real A := by ring
  constructor
  · have hw := (hnear.weighted_indicator_error he (gridTrim_measurable hA _)
      (gridTrim_subset_unit A _) hn).2
    exact hw.trans ((add_le_add (mul_le_mul_of_nonneg_left hb.2 he0) hweight).trans_eq hcoef)
  · have hw := (hnear.inverse.weighted_indicator_error he (gridTrim_measurable hA _)
      (gridTrim_subset_unit A _) (by simpa only [inverse_inverse] using hp)).2
    rw [inverse_inverse] at hw
    exact hw.trans ((add_le_add (mul_le_mul_of_nonneg_left hb.1 he0) hweight).trans_eq hcoef)

end RationalUnitMobius
end TransposeFollowup
