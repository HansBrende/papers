import TransposeFollowup.UnitBoundaryError
import TransposeFollowup.CellCenteredVariance

/-! Explicit centering and projection costs for the actual cell-centered
indicator. The unit boundary contribution and all deleted-cell projection
terms remain in the final bound. Normalization is not assumed in this file. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem gridStep_measurable {K : ℕ} (v : Fin K → ℝ) : Measurable (gridStep v) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (gridCell_measurable i)

theorem centeredIndicator_measurable {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (centeredIndicator A) :=
  (measurable_const.indicator hA).sub (measurable_const.indicator measurableSet_Icc)

theorem cellCenteredIndicator_measurable {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (cellCenteredIndicator K A) :=
  (measurable_const.indicator hA).sub (gridStep_measurable _)

theorem centeredIndicator_memLp {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (p : ℝ≥0∞) : MemLp (centeredIndicator A) p volume :=
  (memLp_indicator_const p hA (1:ℝ) (Or.inr (unit_subset_volume_ne_top hunit))).sub
    (memLp_indicator_const p measurableSet_Icc (volume.real A) (Or.inr (by simp)))

theorem centeredIndicator_decomposition (A : Set ℝ) (x : ℝ) :
    centeredIndicator A x=A.indicator (fun _ => (1:ℝ)) x-
      volume.real A*(Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x∈Icc (0:ℝ) 1 <;> simp [centeredIndicator,hx]

namespace RationalUnitMobius

theorem weighted_centering_identity (G : RationalUnitMobius) (A : Set ℝ) (x : ℝ) :
    G.whole.weightedPullback (centeredIndicator A) x-centeredIndicator A x=
      (G.whole.weightedPullback (A.indicator (fun _ => (1:ℝ))) x-A.indicator (fun _ => (1:ℝ)) x)-
      volume.real A*(G.whole.weightedPullback ((Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ))) x-
        (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x) := by
  simp only [RationalMobius.weightedPullback,centeredIndicator_decomposition]
  ring

theorem NearIdentity.weighted_centered_error {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (hinv : MapsTo G.inverse.whole.eval A (Icc (0:ℝ) 1)) :
    IntegrableOn (fun x => (G.whole.weightedPullback (centeredIndicator A) x-
      centeredIndicator A x)^2) (Icc (0:ℝ) 1) ∧
    (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (centeredIndicator A) x-centeredIndicator A x)^2) ≤
      2*(∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (A.indicator (fun _ => (1:ℝ))) x-
        A.indicator (fun _ => (1:ℝ)) x)^2)+
      2*(volume.real A)^2*(2*(1+32*eta)*(16*eta)+2*(32*eta)^2) := by
  let u := A.indicator (fun _ => (1:ℝ))
  let v := (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ))
  have hH := G.whole.weighted_error_integrableOn (A := Icc (0:ℝ) 1) measurableSet_Icc
    (by simp [whole]) (centeredIndicator_measurable hA) (centeredIndicator_memLp hA hunit 2).integrable_sq
  have hI := (h.weighted_indicator_error he hA hunit hinv).1
  have hU := h.weighted_unitIndicator_error he
  have hR : IntegrableOn (fun x => 2*(G.whole.weightedPullback u x-u x)^2+
      2*(volume.real A)^2*(G.whole.weightedPullback v x-v x)^2) (Icc (0:ℝ) 1) :=
    (hI.const_mul 2).add (hU.1.const_mul (2*(volume.real A)^2))
  have hp : ∀ x : ℝ,(G.whole.weightedPullback (centeredIndicator A) x-centeredIndicator A x)^2 ≤
      2*(G.whole.weightedPullback u x-u x)^2+
      2*(volume.real A)^2*(G.whole.weightedPullback v x-v x)^2 := by
    intro x
    rw [G.weighted_centering_identity A x]
    change ((G.whole.weightedPullback u x-u x)-volume.real A*(G.whole.weightedPullback v x-v x))^2 ≤ _
    nlinarith only [sq_nonneg ((G.whole.weightedPullback u x-u x)+
      volume.real A*(G.whole.weightedPullback v x-v x))]
  refine ⟨hH,?_⟩
  have hb := setIntegral_mono_on hH hR measurableSet_Icc (fun x _ => hp x)
  calc
    _ ≤ ∫ x in Icc (0:ℝ) 1,2*(G.whole.weightedPullback u x-u x)^2+
        2*(volume.real A)^2*(G.whole.weightedPullback v x-v x)^2 := hb
    _ = 2*(∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback u x-u x)^2)+
        2*(volume.real A)^2*(∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback v x-v x)^2) := by
      rw [integral_add (f := fun x => 2*(G.whole.weightedPullback u x-u x)^2)
        (g := fun x => 2*(volume.real A)^2*(G.whole.weightedPullback v x-v x)^2)
        (hI.const_mul 2) (hU.1.const_mul _),integral_const_mul,integral_const_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hU.2
      (mul_nonneg (by norm_num) (sq_nonneg _)))

theorem NearIdentity.weighted_cellCentered_error {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) (K : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (hinv : MapsTo G.inverse.whole.eval A (Icc (0:ℝ) 1)) :
    IntegrableOn (fun x => (G.whole.weightedPullback (cellCenteredIndicator K A) x-
      cellCenteredIndicator K A x)^2) (Icc (0:ℝ) 1) ∧
    (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (cellCenteredIndicator K A) x-
      cellCenteredIndicator K A x)^2) ≤
      6*(∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (A.indicator (fun _ => (1:ℝ))) x-
        A.indicator (fun _ => (1:ℝ)) x)^2)+
      6*(volume.real A)^2*(2*(1+32*eta)*(16*eta)+2*(32*eta)^2)+
      6*(∫ x,(centeredIndicator A x-cellCenteredIndicator K A x)^2) := by
  have hf := cellCenteredIndicator_measurable (K := K) hA
  have hf2 := (cellCenteredIndicator_memLp (K := K) hA hunit 2).integrable_sq
  have hg := centeredIndicator_measurable hA
  have hg2 := (centeredIndicator_memLp hA hunit 2).integrable_sq
  have hb := G.whole.weighted_projection_transfer (A := Icc (0:ℝ) 1) measurableSet_Icc (by simp [whole]) hf hg hf2 hg2
  have heq : (fun x => (cellCenteredIndicator K A x-centeredIndicator A x)^2)=
      fun x => (centeredIndicator A x-cellCenteredIndicator K A x)^2 := by funext x; ring
  rw [heq] at hb
  have hc := (h.weighted_centered_error he hA hunit hinv).2
  refine ⟨G.whole.weighted_error_integrableOn (A := Icc (0:ℝ) 1) measurableSet_Icc (by simp [whole]) hf hf2,?_⟩
  linarith

theorem augmented_central_cellCentered_error {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) (p : Fin c) {eta sigma delta : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8) (hr : 8*eta ≤ (m:ℝ)/K)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (hdelta : 0 ≤ delta)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let T := gridTrim A (centralCells K m)
    let theta := 2*(m:ℝ)/(K:ℝ)
    let C := 2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta
    let D := 2*(1+32*eta)*C+2*(32*eta)^2
    let J := 2*(1+32*eta)*(16*eta)+2*(32*eta)^2
    let Q := (delta+theta*(1+delta))^2+theta
    (∫ x in Icc (0:ℝ) 1,((F p).whole.weightedPullback (cellCenteredIndicator K T) x-
      cellCenteredIndicator K T x)^2) ≤ 6*D*volume.real A+6*(J+Q)*(volume.real A)^2 ∧
    (∫ x in Icc (0:ℝ) 1,((F p).inverse.whole.weightedPullback (cellCenteredIndicator K T) x-
      cellCenteredIndicator K T x)^2) ≤ 6*D*volume.real A+6*(J+Q)*(volume.real A)^2 := by
  let T := gridTrim A (centralCells K m)
  let theta := 2*(m:ℝ)/(K:ℝ)
  let C := 2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta
  let D := 2*(1+32*eta)*C+2*(32*eta)^2
  let J := 2*(1+32*eta)*(16*eta)+2*(32*eta)^2
  let Q := (delta+theta*(1+delta))^2+theta
  have hT := gridTrim_measurable hA (centralCells K m)
  have hTu := gridTrim_subset_unit A (centralCells K m)
  have hcentral := (centralTrim_loss_bound (by omega : 0<K) hm hA hunit delta huniform).1
  have hI := augmented_central_trim_weighted_indicator_error F hK hm p hnear he hr hA hunit huniform hsmall
  have hP := gridTrim_projection_error_explicit (by omega : 0<K) hA hunit (centralCells K m)
    delta hdelta huniform
  simp only [centralCells_compl_card hm,Nat.cast_mul,Nat.cast_ofNat] at hP
  have hmass : volume.real T ≤ volume.real A :=
    measureReal_mono (gridTrim_subset A _) (unit_subset_volume_ne_top hunit)
  have hmass2 : (volume.real T)^2 ≤ (volume.real A)^2 :=
    (sq_le_sq₀ measureReal_nonneg measureReal_nonneg).2 hmass
  have hJ : 0 ≤ J := by have h0 := hnear.nonneg; dsimp [J]; positivity
  have hstep : ∀ (G : RationalUnitMobius),G.NearIdentity eta →
      MapsTo G.inverse.whole.eval T (Icc (0:ℝ) 1) →
      (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (T.indicator (fun _ => (1:ℝ))) x-
        T.indicator (fun _ => (1:ℝ)) x)^2) ≤ D*volume.real A →
      (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (cellCenteredIndicator K T) x-
        cellCenteredIndicator K T x)^2) ≤ 6*D*volume.real A+6*(J+Q)*(volume.real A)^2 := by
    intro G hG hinv hB
    have hb := (hG.weighted_cellCentered_error he K hT hTu hinv).2
    calc
      _ ≤ 6*(∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback (T.indicator (fun _ => (1:ℝ))) x-
          T.indicator (fun _ => (1:ℝ)) x)^2)+6*(volume.real T)^2*J+
          6*(∫ x,(centeredIndicator T x-cellCenteredIndicator K T x)^2) := hb
      _ ≤ 6*(D*volume.real A)+6*(volume.real A)^2*J+6*(Q*(volume.real A)^2) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass2 (by norm_num)) hJ))
          (mul_le_mul_of_nonneg_left hP (by norm_num))
      _ = _ := by ring
  refine ⟨hstep (F p) hnear ?_ hI.1,hstep (F p).inverse hnear.inverse ?_ hI.2⟩
  · exact fun x hx => hnear.inverse.mapsTo_central he hr (hcentral hx)
  · simpa only [inverse_inverse] using
      (show MapsTo (F p).whole.eval T (Icc (0:ℝ) 1) from
        fun x hx => hnear.mapsTo_central he hr (hcentral hx))

end RationalUnitMobius
end TransposeFollowup
