import TransposeFollowup.CellCenteredAlmostInvariant

/-! A concrete parameter margin: the actual weighted error is at most
one sixteenth of the cell-centered variance, for generators and inverses. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

theorem cellCentered_error_budget_margin {sigma delta theta eta : ℝ}
    (hs0 : 0 ≤ sigma) (hd0 : 0 ≤ delta) (ht0 : 0 ≤ theta) (he0 : 0 ≤ eta)
    (hs : sigma ≤ 1/2000) (hd : delta ≤ 1/100) (ht : theta ≤ 1/2000) (he : eta ≤ 1/1000000) :
    6*(2*(1+32*eta)*(2*sigma+2*theta*(1+delta)+32*eta)+2*(32*eta)^2)+
      3*(2*(1+32*eta)*(16*eta)+2*(32*eta)^2+(delta+theta*(1+delta))^2+theta) ≤ 49/1600 := by
  calc
    _ ≤ 6*(2*(1+32*(1/1000000:ℝ))*(2*(1/2000)+2*(1/2000)*(1+1/100)+32*(1/1000000))+
        2*(32*(1/1000000))^2)+
      3*(2*(1+32*(1/1000000))*(16*(1/1000000))+2*(32*(1/1000000))^2+
        (1/100+(1/2000)*(1+1/100))^2+1/2000) := by gcongr
    _ ≤ _ := by norm_num

namespace RationalUnitMobius

theorem weighted_correlation_of_error (G : RationalUnitMobius) {f : ℝ → ℝ}
    (hf : Measurable f) (hf2 : Integrable (fun x => (f x)^2) volume)
    (hsupport : ∀ x : ℝ,x∉Icc (0:ℝ) 1 → f x=0)
    (herror : (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback f x-f x)^2) ≤
      (1/16)*(∫ x,(f x)^2)) :
    (3/4)*(∫ x,(f x)^2) ≤ ∫ x in Icc (0:ℝ) 1,G.whole.weightedPullback f x*f x := by
  have hsub : Icc (0:ℝ) 1⊆Icc (G.whole.lo:ℝ) G.whole.hi := by simp [whole]
  have hW := G.whole.weighted_square_integrableOn measurableSet_Icc hsub hf2
  have hF := hf2.integrableOn (s := Icc (0:ℝ) 1)
  have hE := G.whole.weighted_error_integrableOn measurableSet_Icc hsub hf hf2
  have hProd : IntegrableOn (fun x => G.whole.weightedPullback f x*f x) (Icc (0:ℝ) 1) :=
    ((memLp_two_iff_integrable_sq
    (G.whole.measurable_weightedPullback hf).aestronglyMeasurable).2 hW).integrable_mul
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hF)
  have hL : IntegrableOn (fun x => (7/8)*(f x)^2-
      2*(G.whole.weightedPullback f x-f x)^2) (Icc (0:ℝ) 1) :=
    (hF.const_mul (7/8)).sub (hE.const_mul 2)
  have hb := setIntegral_mono_on hL hProd measurableSet_Icc (fun x _ => by
    have hs := sq_nonneg (4*(G.whole.weightedPullback f x-f x)+f x)
    nlinarith only [hs])
  rw [integral_sub (f := fun x => (7/8)*(f x)^2)
    (g := fun x => 2*(G.whole.weightedPullback f x-f x)^2)
    (hF.const_mul _) (hE.const_mul _),integral_const_mul,integral_const_mul] at hb
  have hu : (∫ x in Icc (0:ℝ) 1,(f x)^2)=∫ x,(f x)^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hsupport x hx]; norm_num)
  rw [hu] at hb
  linarith

theorem augmented_central_relative_error {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) (p : Fin c) {eta sigma delta : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/1000000) (hr : 8*eta ≤ (m:ℝ)/K)
    (hs0 : 0 ≤ sigma) (hs : sigma ≤ 1/2000) (hd0 : 0 ≤ delta) (hd : delta ≤ 1/100)
    (ht : 2*(m:ℝ)/(K:ℝ) ≤ 1/2000) {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (hhalf : volume.real A ≤ 1/2)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let T := gridTrim A (centralCells K m)
    (∫ x in Icc (0:ℝ) 1,((F p).whole.weightedPullback (cellCenteredIndicator K T) x-
      cellCenteredIndicator K T x)^2) ≤ (1/16)*(∫ x,(cellCenteredIndicator K T x)^2) ∧
    (∫ x in Icc (0:ℝ) 1,((F p).inverse.whole.weightedPullback (cellCenteredIndicator K T) x-
      cellCenteredIndicator K T x)^2) ≤ (1/16)*(∫ x,(cellCenteredIndicator K T x)^2) := by
  let T := gridTrim A (centralCells K m)
  let theta := 2*(m:ℝ)/(K:ℝ)
  let C := 2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta
  let D := 2*(1+32*eta)*C+2*(32*eta)^2
  let J := 2*(1+32*eta)*(16*eta)+2*(32*eta)^2
  let Q := (delta+theta*(1+delta))^2+theta
  have he8 : eta ≤ 1/8 := by linarith
  have hb := augmented_central_cellCentered_error F hK hm p hnear he8 hr hA hunit hd0 huniform hsmall
  have ht0 : 0 ≤ theta := by dsimp [theta]; positivity
  have hbudget := cellCentered_error_budget_margin hs0 hd0 ht0 hnear.nonneg hs hd ht he
  have heq : 6*D+3*(J+Q)=
      6*(2*(1+32*eta)*(2*sigma+2*theta*(1+delta)+32*eta)+2*(32*eta)^2)+
      3*(2*(1+32*eta)*(16*eta)+2*(32*eta)^2+(delta+theta*(1+delta))^2+theta) := by
    dsimp [D,J,Q,C,theta]
    ring
  rw [← heq] at hbudget
  have hV := (gridTrim_small_projection_error (by omega : 0<K) hA hunit hhalf (centralCells K m)
    delta hd0 hd (by
      simp only [centralCells_compl_card hm,Nat.cast_mul,Nat.cast_ofNat]
      linarith) huniform).1
  have hM : 0 ≤ volume.real A := measureReal_nonneg
  have hM2 : (volume.real A)^2 ≤ (1/2)*volume.real A := by
    have hh := mul_le_mul_of_nonneg_right hhalf hM
    nlinarith only [hh]
  have hJQ : 0 ≤ J+Q := by have he0 := hnear.nonneg; dsimp [J,Q]; positivity
  have hbound : 6*D*volume.real A+6*(J+Q)*(volume.real A)^2 ≤
      (1/16)*(∫ x,(cellCenteredIndicator K T x)^2) := by
    calc
      _ ≤ (6*D+3*(J+Q))*volume.real A := by
        have hh := mul_le_mul_of_nonneg_left hM2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hJQ)
        nlinarith only [hh]
      _ ≤ (49/1600)*volume.real A := mul_le_mul_of_nonneg_right hbudget hM
      _ ≤ _ := by linarith only [hV]
  exact ⟨hb.1.trans hbound,hb.2.trans hbound⟩

theorem augmented_central_correlation {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) (p : Fin c) {eta sigma delta : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/1000000) (hr : 8*eta ≤ (m:ℝ)/K)
    (hs0 : 0 ≤ sigma) (hs : sigma ≤ 1/2000) (hd0 : 0 ≤ delta) (hd : delta ≤ 1/100)
    (ht : 2*(m:ℝ)/(K:ℝ) ≤ 1/2000) {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (hhalf : volume.real A ≤ 1/2)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let T := gridTrim A (centralCells K m)
    let f := cellCenteredIndicator K T
    (3/4)*(∫ x,(f x)^2) ≤ (∫ x in Icc (0:ℝ) 1,(F p).whole.weightedPullback f x*f x) ∧
    (3/4)*(∫ x,(f x)^2) ≤ (∫ x in Icc (0:ℝ) 1,(F p).inverse.whole.weightedPullback f x*f x) := by
  have hb := augmented_central_relative_error F hK hm p hnear he hr hs0 hs hd0 hd ht
    hA hunit hhalf huniform hsmall
  have hT := gridTrim_measurable hA (centralCells K m)
  have hTu := gridTrim_subset_unit A (centralCells K m)
  have hf := cellCenteredIndicator_measurable (K := K) hT
  have hf2 := (cellCenteredIndicator_memLp (K := K) hT hTu 2).integrable_sq
  have hsupport : ∀ x : ℝ,x∉Icc (0:ℝ) 1 → cellCenteredIndicator K (gridTrim A (centralCells K m)) x=0 :=
    fun _ hx => cellCenteredIndicator_off_unit hTu hx
  exact ⟨(F p).weighted_correlation_of_error hf hf2 hsupport hb.1,
    (F p).inverse.weighted_correlation_of_error hf hf2 hsupport hb.2⟩

end RationalUnitMobius
end TransposeFollowup
