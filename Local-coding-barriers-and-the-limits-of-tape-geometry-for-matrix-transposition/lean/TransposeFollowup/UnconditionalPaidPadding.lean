import TransposeFollowup.NormalizedCellCorrelation
import TransposeFollowup.RealMobiusL2
import TransposeFollowup.RealMobiusAverage
import TransposeFollowup.InitialWalkDensityCap
import TransposeFollowup.RestrictedGapFromAutocorrelation
import TransposeFollowup.RationalNearIdentityFamily
import TransposeFollowup.ContinuousNativePadding

/-! Continuous expansion from an explicit normalized restricted-correlation
gap hypothesis. This file proves the reduction, not existence of the gap. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

namespace RationalUnitMobius

/-- The symmetric average of the actual weighted correlations on [0,1]. -/
noncomputable def symmetricCorrelation {c : ℕ} (F : Fin c → RationalUnitMobius)
    (f : ℝ → ℝ) : ℝ :=
  (∑ p : Fin c,((∫ x in Icc (0:ℝ) 1,(F p).whole.weightedPullback f x*f x)+
    (∫ x in Icc (0:ℝ) 1,(F p).inverse.whole.weightedPullback f x*f x)))/(2*(c:ℝ))

/-- The real-function form of the required restricted gap, with closed
grid cells as in the source theorem. Its existence is not asserted here. -/
def RestrictedCorrelationGap {c : ℕ} (F : Fin c → RationalUnitMobius) (K : ℕ) : Prop :=
  ∀ f : ℝ → ℝ,Measurable f → Integrable (fun x => (f x)^2) volume →
    (∀ x : ℝ,x∉Icc (0:ℝ) 1 → f x=0) → (∫ x,(f x)^2)=1 →
    (∀ i : Fin K,(∫ x in Icc ((i.val:ℝ)/K) (((i.val:ℝ)+1)/K),f x)=0) →
    symmetricCorrelation F f<1/2

theorem weighted_correlation_integrableOn (G : RationalUnitMobius) {f : ℝ → ℝ}
    (hf : Measurable f) (hf2 : Integrable (fun x => (f x)^2) volume) :
    IntegrableOn (fun x => G.whole.weightedPullback f x*f x) (Icc (0:ℝ) 1) := by
  have hW := G.whole.weighted_square_integrableOn (A := Icc (0:ℝ) 1) measurableSet_Icc
    (by simp [whole]) hf2
  exact ((memLp_two_iff_integrable_sq
    (G.whole.measurable_weightedPullback hf).aestronglyMeasurable).2 hW).integrable_mul
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2.integrableOn)

theorem symmetricCorrelation_eq_integral_average {c : ℕ} (F : Fin c → RationalUnitMobius)
    {f : ℝ → ℝ} (hf : Measurable f) (hf2 : Integrable (fun x => (f x)^2) volume) :
    symmetricCorrelation F f=
      ∫ x in Icc (0:ℝ) 1,((2*(c:ℝ))⁻¹ *
        ∑ p : Fin c,((F p).whole.weightedPullback f x+(F p).inverse.whole.weightedPullback f x))*f x := by
  have heq : (fun x => ((2*(c:ℝ))⁻¹ *
      ∑ p : Fin c,((F p).whole.weightedPullback f x+(F p).inverse.whole.weightedPullback f x))*f x)=
      fun x => (2*(c:ℝ))⁻¹ *∑ p : Fin c,
        ((F p).whole.weightedPullback f x*f x+(F p).inverse.whole.weightedPullback f x*f x) := by
    funext x
    rw [mul_assoc,Finset.sum_mul]
    simp only [add_mul]
  rw [heq,integral_const_mul,integral_finsetSum Finset.univ
    (f := fun p x => (F p).whole.weightedPullback f x*f x+(F p).inverse.whole.weightedPullback f x*f x)
    (fun p _ =>
    ((F p).weighted_correlation_integrableOn hf hf2).add
      ((F p).inverse.weighted_correlation_integrableOn hf hf2))]
  unfold symmetricCorrelation
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact (integral_add ((F p).weighted_correlation_integrableOn hf hf2)
    ((F p).inverse.weighted_correlation_integrableOn hf hf2)).symm

theorem symmetricCorrelation_lower {c : ℕ} (F : Fin c → RationalUnitMobius)
    (hc : 0<c) (f : ℝ → ℝ) (a : ℝ)
    (h : ∀ p : Fin c,
      a ≤ (∫ x in Icc (0:ℝ) 1,(F p).whole.weightedPullback f x*f x) ∧
      a ≤ (∫ x in Icc (0:ℝ) 1,(F p).inverse.whole.weightedPullback f x*f x)) :
    a ≤ symmetricCorrelation F f := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => add_le_add (h p).1 (h p).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hc' : (0:ℝ)<c := by exact_mod_cast hc
  unfold symmetricCorrelation
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(c:ℝ))).2
  nlinarith only [hs]

theorem weighted_correlation_eq_global (G : RationalUnitMobius) (f : ℝ → ℝ)
    (hsupport : ∀ x : ℝ,x∉Icc (0:ℝ) 1 → f x=0) :
    (∫ x in Icc (0:ℝ) 1,G.whole.weightedPullback f x*f x)=
      ∫ x,G.whole.weightedPullback f x*f x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hsupport x hx,mul_zero])

theorem expansion_of_restrictedCorrelationGap {c K : ℕ} (F : Fin c → RationalUnitMobius)
    (hc : 0<c) (hK : 10000 ≤ K) {eta : ℝ}
    (hnear : ∀ p,(F p).NearIdentity eta) (he : eta ≤ 1/1000000)
    (hgap : RestrictedCorrelationGap F K) :
    ∀ A : Set ℝ,MeasurableSet A → A⊆Icc (0:ℝ) 1 → volume.real A ≤ 1/2 →
      (1+expansionMargin K)*volume.real A ≤ volume.real (restrictedImageUnion
        (augmentedFamily F (unitStep K) (unitStep_small (by omega : 2 ≤ K))) A) := by
  intro A hA hunit hhalf
  by_cases hz : volume.real A=0
  · rw [hz,mul_zero]
    exact measureReal_nonneg
  have hM : 0<volume.real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
  by_contra hnot
  have hsmall := (not_le.mp hnot).le
  have he0 := (hnear ⟨0,hc⟩).nonneg
  have hs := (expansionMargin_pos (by omega : 0<K)).le
  have hd := uniformityTolerance_bounds (by omega : 1 ≤ K)
  have hu := augmented_cell_uniformity F (by omega : 2 ≤ K) hA hunit (expansionMargin K) hs hsmall
  let B := centralCells K (trimWidth K eta)
  let T := gridTrim A B
  have hT : MeasurableSet T := gridTrim_measurable hA B
  have hTu : T⊆Icc (0:ℝ) 1 := gridTrim_subset_unit A B
  have hVlo := (gridTrim_small_projection_error (by omega : 0<K) hA hunit hhalf B
    (uniformityTolerance K) hd.1 hd.2 (by
      dsimp [B]
      simp only [centralCells_compl_card (trimWidth_twice_le hK he0 he),Nat.cast_mul,Nat.cast_ofNat]
      have ht := trimWidth_fraction hK he0 he
      linarith) hu).1
  have hV : 0<∫ x,(cellCenteredIndicator K T x)^2 :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ)<49/100) hM) hVlo
  let f := normalizedCellFunction K T hT hTu
  have hcorr : ∀ p : Fin c,
      (3/4:ℝ) ≤ (∫ x in Icc (0:ℝ) 1,(F p).whole.weightedPullback f x*f x) ∧
      (3/4:ℝ) ≤ (∫ x in Icc (0:ℝ) 1,(F p).inverse.whole.weightedPullback f x*f x) := by
    intro p
    have hp := augmented_correlation_with_parameters F hK hnear he hA hunit hhalf hsmall p
    exact ⟨(F p).normalizedCellFunction_correlation hT hTu hV hp.1,
      (F p).inverse.normalizedCellFunction_correlation hT hTu hV hp.2⟩
  have hl := symmetricCorrelation_lower F hc f (3/4) hcorr
  have hg := hgap f (normalizedCellFunction_measurable hT hTu)
    (normalizedCellFunction_square_integrable hT hTu)
    (fun _ hx => normalizedCellFunction_off_unit hT hTu hx)
    (normalizedCellFunction_square_integral hT hTu hV)
    (normalizedCellFunction_closed_cell_integral hT hTu)
  linarith

theorem open_expansion_of_restrictedCorrelationGap {c K : ℕ} (F : Fin c → RationalUnitMobius)
    (hc : 0<c) (hK : 10000 ≤ K) {eta : ℝ}
    (hnear : ∀ p,(F p).NearIdentity eta) (he : eta ≤ 1/1000000)
    (hgap : RestrictedCorrelationGap F K) :
    ∀ A : Set ℝ,MeasurableSet A → A⊆Icc (0:ℝ) 1 → volume.real A ≤ 1/2 →
      (1+expansionMargin K)*volume.real A ≤ volume.real (mapImageUnion
        (rationalFamilyMaps (clippedFamily
          (augmentedFamily F (unitStep K) (unitStep_small (by omega : 2 ≤ K))))) A) :=
  restricted_expansion_to_open _ _ (expansion_of_restrictedCorrelationGap F hc hK hnear he hgap)

theorem exists_expanding_family_of_eventual_gap {c : ℕ} (F : Fin c → RationalUnitMobius)
    (hc : 0<c) {eta : ℝ} (hnear : ∀ p,(F p).NearIdentity eta) (he : eta ≤ 1/1000000)
    (K₀ : ℕ) (hgap : ∀ K : ℕ,K₀ ≤ K → RestrictedCorrelationGap F K) :
    ∃ (d : ℕ) (H : Fin (d+1) → RationalUnitMobius) (eps : ℝ),0<eps ∧
      ∀ A : Set ℝ,MeasurableSet A → A⊆Icc (0:ℝ) 1 → volume.real A ≤ 1/2 →
        (1+eps)*volume.real A ≤ volume.real (restrictedImageUnion H A) := by
  let K := max 10000 K₀
  have hK : 10000 ≤ K := le_max_left _ _
  refine ⟨c+c+2,augmentedFamily F (unitStep K) (unitStep_small (by omega)),
    expansionMargin K,expansionMargin_pos (by omega),?_⟩
  exact expansion_of_restrictedCorrelationGap F hc hK hnear he (hgap K (le_max_right _ _))

end RationalUnitMobius
end TransposeFollowup


/-! Exact compatibility of the global L2 action with the rational maps
used in the continuous-expansion reduction, for determinant-one data. -/
namespace TransposeFollowup.RationalUnitMobius
open Classical Set MeasureTheory
set_option autoImplicit false

def toRealSL2 (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1) : RealMobius.Group :=
  ⟨!![(F.a:ℝ), (F.b:ℝ); (F.c:ℝ), (F.d:ℝ)],by
    rw [Matrix.det_fin_two_of]
    exact_mod_cast hdet⟩

theorem inverse_determinant_one {F : RationalUnitMobius} (hdet : F.a*F.d-F.b*F.c=1) :
    F.inverse.a*F.inverse.d-F.inverse.b*F.inverse.c=1 := by
  dsimp [inverse]
  nlinarith only [hdet]

theorem toRealSL2_inverse (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1) :
    F.inverse.toRealSL2 (inverse_determinant_one hdet)=(F.toRealSL2 hdet)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [toRealSL2,inverse]

theorem toRealSL2_eval (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1) (x : ℝ) :
    RealMobius.eval (F.toRealSL2 hdet) x=F.whole.eval x := rfl

theorem toRealSL2_denom (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1) (x : ℝ) :
    RealMobius.denom (F.toRealSL2 hdet) x=F.whole.denom x := rfl

theorem toRealSL2_jacobian (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1) (x : ℝ) :
    RealMobius.jacobian (F.toRealSL2 hdet) x=F.whole.derivative x := by
  have hd : (F.whole.delta:ℝ)=1 := by exact_mod_cast hdet
  rw [RealMobius.jacobian,toRealSL2_denom,RationalMobius.derivative,hd]

theorem toRealSL2_weightedPullback (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1)
    (f : ℝ → ℝ) (x : ℝ) :
    RealMobius.weightedPullback (F.toRealSL2 hdet) f x=F.whole.weightedPullback f x := by
  have hd : (F.whole.delta:ℝ)=1 := by exact_mod_cast hdet
  rw [RealMobius.weightedPullback,toRealSL2_denom,toRealSL2_eval,
    RationalMobius.weightedPullback,RationalMobius.derivative,hd,
    Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),Real.sqrt_one,Real.sqrt_sq_eq_abs,one_div]

theorem pullbackLp_rational_coe (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1)
    (f : RealMobius.RealL2) :
    ⇑(RealMobius.pullbackLp (F.toRealSL2 hdet) f) =ᵐ[volume] F.whole.weightedPullback f :=
  (RealMobius.pullbackLp_coe (F.toRealSL2 hdet) f).trans
    (Filter.Eventually.of_forall (F.toRealSL2_weightedPullback hdet f))

theorem pullbackLp_rational_inner (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1)
    (f h : RealMobius.RealL2) :
    inner ℝ (RealMobius.pullbackLp (F.toRealSL2 hdet) f) h=
      ∫ x,F.whole.weightedPullback f x*h x := by
  rw [L2.inner_def]
  simp only [Real.inner_apply]
  exact integral_congr_ae ((pullbackLp_rational_coe F hdet f).mono (fun x hx => by simp only [hx]))

theorem unitaryAction_rational_inner (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1)
    (f h : RealMobius.RealL2) :
    inner ℝ (RealMobius.unitaryAction (F.toRealSL2 hdet) f) h=
      ∫ x,F.inverse.whole.weightedPullback f x*h x := by
  change inner ℝ (RealMobius.pullbackLp (F.toRealSL2 hdet)⁻¹ f) h= _
  rw [← toRealSL2_inverse]
  exact pullbackLp_rational_inner F.inverse (inverse_determinant_one hdet) f h

end TransposeFollowup.RationalUnitMobius


/-! The normalized L2 spectral-gap premise implies the function-form
premise already used to derive continuous expansion. No gap existence
result is assumed implicitly or asserted by this file. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

namespace RealMobius

def RestrictedL2Gap {c : ℕ} (G : Fin c → Group) (K : ℕ) : Prop :=
  ∀ f : RealL2,‖f‖=1 → (∀ᵐ x ∂volume,x∉Icc (0:ℝ) 1 → f x=0) →
    (∀ i : Fin K,(∫ x in Icc ((i.val:ℝ)/K) (((i.val:ℝ)+1)/K),f x)=0) →
    inner ℝ (averageOperator G f) f<1/2

end RealMobius

namespace RationalUnitMobius

theorem weightedPullback_ae_congr (F : RationalUnitMobius) (hdet : F.a*F.d-F.b*F.c=1)
    {f h : ℝ → ℝ} (heq : f =ᵐ[volume] h) :
    F.whole.weightedPullback f =ᵐ[volume] F.whole.weightedPullback h := by
  have he := RealMobius.weightedPullback_ae_congr (F.toRealSL2 hdet) heq
  filter_upwards [he] with x hx
  simpa only [toRealSL2_weightedPullback] using hx

theorem symmetricCorrelation_ae_congr {c : ℕ} (F : Fin c → RationalUnitMobius)
    (hdet : ∀ p,(F p).a*(F p).d-(F p).b*(F p).c=1)
    {f h : ℝ → ℝ} (heq : f =ᵐ[volume] h) : symmetricCorrelation F f=symmetricCorrelation F h := by
  unfold symmetricCorrelation
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg₂ (· + ·)
  · apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [((F p).weightedPullback_ae_congr (hdet p) heq).mul heq] with x hx _
    exact hx
  · apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [((F p).inverse.weightedPullback_ae_congr (inverse_determinant_one (hdet p)) heq).mul heq]
      with x hx _
    exact hx

theorem averageOperator_rational_correlation {c : ℕ} (F : Fin c → RationalUnitMobius)
    (hdet : ∀ p,(F p).a*(F p).d-(F p).b*(F p).c=1) (f : RealMobius.RealL2)
    (hsupport : ∀ᵐ x ∂volume,x∉Icc (0:ℝ) 1 → f x=0) :
    inner ℝ (RealMobius.averageOperator (fun p => (F p).toRealSL2 (hdet p)) f) f=
      symmetricCorrelation F f := by
  have hi : ∀ H : RationalUnitMobius,(∫ x in Icc (0:ℝ) 1,H.whole.weightedPullback f x*f x)=
      ∫ x,H.whole.weightedPullback f x*f x := by
    intro H
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport] with x hx
    intro hu
    rw [hx hu,mul_zero]
  have hp : ∀ p : Fin c,
      inner ℝ (RealMobius.unitaryAction ((F p).toRealSL2 (hdet p)) f) f=
        ∫ x in Icc (0:ℝ) 1,(F p).inverse.whole.weightedPullback f x*f x := by
    intro p
    rw [unitaryAction_rational_inner,hi]
  have hm : ∀ p : Fin c,
      inner ℝ (RealMobius.unitaryAction ((F p).toRealSL2 (hdet p))⁻¹ f) f=
        ∫ x in Icc (0:ℝ) 1,(F p).whole.weightedPullback f x*f x := by
    intro p
    change inner ℝ (RealMobius.pullbackLp (((F p).toRealSL2 (hdet p))⁻¹)⁻¹ f) f= _
    rw [inv_inv,pullbackLp_rational_inner,hi]
  simp only [RealMobius.averageOperator_apply,real_inner_smul_left,sum_inner,inner_add_left]
  unfold symmetricCorrelation
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [hp,hm,add_comm]

theorem restrictedCorrelationGap_of_L2Gap {c K : ℕ} (F : Fin c → RationalUnitMobius)
    (hdet : ∀ p,(F p).a*(F p).d-(F p).b*(F p).c=1)
    (hgap : RealMobius.RestrictedL2Gap (fun p => (F p).toRealSL2 (hdet p)) K) :
    RestrictedCorrelationGap F K := by
  intro f hf hf2 hsupport hnorm hcells
  have hLp := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2
  let u : RealMobius.RealL2 := hLp.toLp f
  have hu : ⇑u =ᵐ[volume] f := MemLp.coeFn_toLp _
  have hunorm : ‖u‖=1 := by
    have hs : ‖u‖^2=1 := by
      rw [RealMobius.realL2_norm_sq]
      exact (integral_congr_ae (hu.mono (fun _ hx => by simp only [hx]))).trans hnorm
    nlinarith only [hs,norm_nonneg u]
  have husupport : ∀ᵐ x ∂volume,x∉Icc (0:ℝ) 1 → u x=0 :=
    hu.mono (fun x hx hunit => hx.trans (hsupport x hunit))
  have hucells : ∀ i : Fin K,(∫ x in Icc ((i.val:ℝ)/K) (((i.val:ℝ)+1)/K),u x)=0 := by
    intro i
    exact (setIntegral_congr_ae measurableSet_Icc (hu.mono (fun _ hx _ => hx))).trans (hcells i)
  have hb := hgap u hunorm husupport hucells
  rw [averageOperator_rational_correlation F hdet u husupport,
    symmetricCorrelation_ae_congr F hdet hu] at hb
  exact hb

theorem expansion_of_restrictedL2Gap {c K : ℕ} (F : Fin c → RationalUnitMobius)
    (hc : 0<c) (hK : 10000 ≤ K) {eta : ℝ}
    (hnear : ∀ p,(F p).NearIdentity eta) (he : eta ≤ 1/1000000)
    (hdet : ∀ p,(F p).a*(F p).d-(F p).b*(F p).c=1)
    (hgap : RealMobius.RestrictedL2Gap (fun p => (F p).toRealSL2 (hdet p)) K) :
    ∀ A : Set ℝ,MeasurableSet A → A⊆Icc (0:ℝ) 1 → volume.real A ≤ 1/2 →
      (1+expansionMargin K)*volume.real A ≤ volume.real (restrictedImageUnion
        (augmentedFamily F (unitStep K) (unitStep_small (by omega : 2 ≤ K))) A) :=
  expansion_of_restrictedCorrelationGap F hc hK hnear he (restrictedCorrelationGap_of_L2Gap F hdet hgap)

end RationalUnitMobius
end TransposeFollowup


/-! Unconditional restricted spectral gap for a finite rational free family
in any prescribed identity neighborhood. The density cap and the gap use
the same family, fixed before the smoothing scale and walk length. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_rational_restricted_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ (r K : ℕ) (g : Fin (2^(3*r)) → Group), 5 ≤ r ∧ 10000 ≤ K ∧
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2^(3*r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2^(3*r) ∧
      (∀ t, HasDenominator (dyadicDenominator r) (g t) ∧
        realEmbedding (g t) ∈ mobiusIdentityBall ε ∧
        (realEmbedding (g t))⁻¹ ∈ mobiusIdentityBall ε) ∧
      RestrictedL2Gap (realEmbedding ∘ g) K := by
  obtain ⟨k, N₀, J₀, _hk, _hN₀, hfamily⟩ :=
    exists_initial_walk_density_cap (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨N, Jgap, _hN, hNmin, _hJgap, hscales⟩ :=
    exists_restricted_gap_from_autocorrelation_flatness_above k N₀
  obtain ⟨ε₀, hε₀, _hε₀one, hgap⟩ := hscales 1 (by norm_num)
  let ε₁ := min ε (min ε₀ (1/32))
  have hε₁ : 0 < ε₁ := lt_min hε (lt_min hε₀ (by norm_num))
  obtain ⟨r, hr, _hnear, hrad⟩ := exists_dyadic_radius_near hε₁
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨g, hg, hgr, hcard, hcardr, hball, Jr, _hJr, hcap⟩ := hfamily r hr
  let J := max Jgap Jr
  obtain ⟨K, hK⟩ := exists_nat_gt (max (10000 : ℝ) (16384*Real.pi^2*2^(3*J)))
  have hKlarge : 10000 ≤ K := by exact_mod_cast ((le_max_left _ _).trans hK.le)
  have hKpos : 0 < K := by omega
  have hgrid : 16384*Real.pi^2*(2 : ℝ)^(3*J) ≤ (K : ℝ)^2 := by
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    exact ((le_max_right _ _).trans hK.le).trans (by nlinarith only [hKone])
  have hballs : mobiusIdentityBall (dyadicRadius r) ⊆ mobiusIdentityBall ε := by
    intro a ha
    exact ha.trans_le ((sq_le_sq₀ (dyadicRadius_pos r).le hε.le).mpr
      (hrad.le.trans (min_le_left _ _)))
  refine ⟨r, K, g, hr, hKlarge, hg, hgr, hcard, hcardr,
    fun t => ⟨(hball t).1, hballs (hball t).2.1, hballs (hball t).2.2⟩, ?_⟩
  apply hgap (dyadicRadius r) (dyadicRadius_pos r)
    (hrad.le.trans ((min_le_right _ _).trans (min_le_left _ _))) J (le_max_left _ _)
    (realEmbedding ∘ g) (by positivity)
    (fun t => mobiusIdentityBall_subset_entryBox_two (dyadicRadius_pos r)
      (dyadicRadius_le_one r) (hball t).2.1) K hKpos hgrid
  intro j hj m hlen hlog
  refine ⟨((1/4 : ℝ)^j)^(-(1/4 : ℝ)), by positivity, ?_, ?_⟩
  · apply le_of_eq
    calc
      _ = (4 : ℝ)^((j : ℝ)/2) := by
        rw [quarter_pow_rpow_neg, ← Real.rpow_mul_natCast (by norm_num)]
        congr 1
        ring
      _ = ((2 : ℝ)^2)^((j : ℝ)/2) := by norm_num
      _ = (2 : ℝ)^((2 : ℝ)*((j : ℝ)/2)) :=
        (Real.rpow_natCast_mul (by norm_num) 2 _).symm
      _ = (2 : ℝ)^(j : ℝ) := by congr 1; ring
      _ = _ := Real.rpow_natCast _ _
  · apply Filter.Eventually.of_forall
    intro x
    apply hcap N j (2^m) hNmin ((le_max_right _ _).trans hj) hlen
    simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using hlog

end TransposeFollowup.RationalFreePair


/-! Existence of a finite rational continuous expander on the unit interval.
The restricted spectral gap is proved for the same rational coefficients;
clipping, auxiliary translations and endpoint removal reuse the existing
continuous-expansion interfaces. No gap or expansion hypothesis remains. -/
namespace TransposeFollowup
open Classical MeasureTheory Set RationalFreePair RationalUnitMobius RealMobius
set_option autoImplicit false

theorem exists_rational_continuous_expander :
    ∃ (c : ℕ) (F : Fin (c+1) → RationalMobius) (eps : ℝ), 0 < eps ∧
      (∀ p, MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain
        (Icc (0 : ℝ) 1)) ∧
      ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 → volume.real S ≤ 1/2 →
        (1+eps)*volume.real S ≤ volume.real (mapImageUnion (rationalFamilyMaps F) S) := by
  let : MeasurableSpace RealMobius.Group := borel RealMobius.Group
  let : BorelSpace RealMobius.Group := ⟨rfl⟩
  obtain ⟨r, K, g, _hr, hK, _hg, _hgr, _hcard, _hcardr, hball, hgap⟩ :=
    exists_rational_restricted_gap (by norm_num : (0 : ℝ) < 1/1000000)
  have hdet (t : Fin (2^(3*r))) : g t 0 0*g t 1 1-g t 0 1*g t 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (g t).property
  have hsmall (t : Fin (2^(3*r))) :
      (g t 0 0-1)^2+(g t 0 1)^2+(g t 1 0)^2+(g t 1 1-1)^2 < (1/16 : ℚ) := by
    have h := (hball t).2.1
    change ((g t 0 0 : ℝ)-1)^2+(g t 0 1 : ℝ)^2+(g t 1 0 : ℝ)^2+
      ((g t 1 1 : ℝ)-1)^2 < (1/1000000 : ℝ)^2 at h
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact h.trans (by norm_num : (1/1000000 : ℝ)^2 < 1/16)
  let F : Fin (2^(3*r)) → RationalUnitMobius := fun t =>
    of_squared_near_identity (g t 0 0) (g t 0 1) (g t 1 0) (g t 1 1)
      (by rw [hdet]; norm_num) (hsmall t)
  have hFdet (t) : (F t).a*(F t).d-(F t).b*(F t).c=1 := hdet t
  have hFnear (t) : (F t).NearIdentity (1/1000000) :=
    NearIdentity.of_squared (by norm_num) (hball t).2.1.le
  have hcompat : (fun t => (F t).toRealSL2 (hFdet t))=realEmbedding ∘ g := by
    funext t
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hFgap : RestrictedL2Gap (fun t => (F t).toRealSL2 (hFdet t)) K := by
    rw [hcompat]
    exact hgap
  let H := augmentedFamily F (unitStep K) (unitStep_small (by omega : 2 ≤ K))
  refine ⟨2^(3*r)+2^(3*r)+2, clippedFamily H, expansionMargin K,
    expansionMargin_pos (by omega), clippedFamily_mapsTo H, ?_⟩
  exact open_expansion_of_restrictedCorrelationGap F (by positivity) hK hFnear le_rfl
    (restrictedCorrelationGap_of_L2Gap F hFdet hFgap)

end TransposeFollowup


/-! A fully paid native extension of every machine, with the literal
zero-slack cut inequality and the original M* conclusion. The continuous
expander, rational overlap generation, blank-start prefix, cleanup and
input reset are all discharged by imported proved constructions. -/
namespace TransposeFollowup.PaidPadding
open Classical FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
open Filter Topology
set_option autoImplicit false

/-- Absolute time, state and tape overheads are chosen before the payload machine.
The construction preserves every payload computation and supplies the full cut limit. -/
theorem exists_uniform_paid_padding :
    ∃ A H K₀ E : ℕ, ∀ M : Transpose.TM, ∃ M' : Transpose.TM,
      M'.q+1=H+(M.q+1) ∧ M'.k=K₀+(M.k+E)*max 1 M.g.size ∧ cellBits M'=3 ∧
      (∀ n : ℕ, 1 ≤ n → ∀ w out : List Bool, w.length=Transpose.inputLength n →
        ∀ t : ℕ, Transpose.ComputesWithin M w out t →
        ∃ T ≤ A*w.length+t, ∃ d : Transpose.Config M',
          Transpose.stepN M' w T (Transpose.init M')=some d ∧
          Transpose.step M' w d=none ∧ d.outRev.reverse=out ∧
          CutIneq n (cellBits M') (blockSize (cellBits M') n) T 0 0
            (fun p τ => workTraj M' w τ p)) ∧
      ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → (∀ i, 1 ≤ ns i) →
        ∀ ws outs : ℕ → List Bool, (∀ i, (ws i).length=Transpose.inputLength (ns i)) →
        ∀ a : ℕ, (∀ i, Transpose.ComputesWithin M (ws i) (outs i)
          (a*Transpose.inputLength (ns i))) →
        ∃ Ts : ℕ → ℕ,
          (∀ i, Ts i ≤ (A+a)*Transpose.inputLength (ns i) ∧
            ∃ d : Transpose.Config M',
              Transpose.stepN M' (ws i) (Ts i) (Transpose.init M')=some d ∧
              Transpose.step M' (ws i) d=none ∧ d.outRev.reverse=outs i ∧
              CutIneq (ns i) (cellBits M') (blockSize (cellBits M') (ns i)) (Ts i) 0 0
                (fun p τ => workTraj M' (ws i) τ p)) ∧
          NativeRunLimits.Conclusion M' ns ws Ts (A+a) := by
  obtain ⟨c, F, eps, heps, hmap, hexp⟩ := exists_rational_continuous_expander
  obtain ⟨K, extra, hcompile⟩ := continuous_uniform_computation_with_cut F hmap eps heps hexp
  let A := PaidPayload.coefficient (r:=c+1+c) (rationalSymmetricFamily F) K
  refine ⟨A, (PaidClean.nativeMachine (r:=c+1+c) (rationalSymmetricFamily F) K).q+1,
    53+rationalPageCount (rationalSymmetricFamily F), extra, ?_⟩
  intro M
  let M' := machine (c:=c+1+c) (rationalSymmetricFamily F) K M extra
  have hbits : cellBits M'=3 := cellBits_eq _ _ _ _
  have hrun (n : ℕ) (hn : 1 ≤ n) (w out : List Bool) (hw : w.length=Transpose.inputLength n)
      (t : ℕ) (ht : Transpose.ComputesWithin M w out t) :
      ∃ T ≤ A*w.length+t, ∃ d : Transpose.Config M',
        Transpose.stepN M' w T (Transpose.init M')=some d ∧
        Transpose.step M' w d=none ∧ d.outRev.reverse=out ∧
        CutIneq n (cellBits M') (blockSize (cellBits M') n) T 0 0
          (fun p τ => workTraj M' w τ p) := by
    rw [hbits]
    exact hcompile M n hn w out hw t ht
  refine ⟨M', (SequentialFive.fixed_resources
    (PaidPayload.prefixProgram (r:=c+1+c) (rationalSymmetricFamily F) K)
    (PaidPayload.payloadProgram (StationaryTapes.machine M extra))).2.2,
    (fixed_resources (c:=c+1+c) (rationalSymmetricFamily F) K M extra).1, hbits, hrun, ?_⟩
  intro ns hns hn ws outs hw a hc
  choose Ts ht ds hs hh ho hcut using
    (fun i => hrun (ns i) (hn i) (ws i) (outs i) (hw i)
      (a*Transpose.inputLength (ns i)) (hc i))
  have htime (i) : Ts i ≤ (A+a)*Transpose.inputLength (ns i) := by
    simpa only [hw i, Nat.add_mul] using ht i
  exact ⟨Ts, fun i => ⟨htime i, ds i, hs i, hh i, ho i, hcut i⟩,
    NativeRunLimits.of_cut M' ns hns ws Ts (A+a) htime hcut⟩

end TransposeFollowup.PaidPadding
