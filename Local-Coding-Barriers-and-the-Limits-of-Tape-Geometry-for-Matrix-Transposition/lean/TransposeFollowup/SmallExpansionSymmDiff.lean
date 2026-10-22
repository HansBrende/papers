import TransposeFollowup.NearIdentityMobius
import TransposeFollowup.TranslationExpansion
import TransposeFollowup.GridTrimming

/-! Small image expansion forces a small symmetric difference with each
image of a trimmed set. Both discarded mass and Jacobian distortion are
charged explicitly; the cover need not itself be assumed measurable. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped symmDiff
set_option autoImplicit false

theorem symmDiff_common_cover {X T E : Set ℝ} (hX : MeasurableSet X)
    (hT : MeasurableSet T) (hE : E⊆Icc (0:ℝ) 1) (hXE : X⊆E) (hTE : T⊆E) :
    volume.real (X ∆ T) ≤ 2*volume.real E-volume.real X-volume.real T := by
  have hxfin := unit_subset_volume_ne_top (hXE.trans hE)
  have htfin := unit_subset_volume_ne_top (hTE.trans hE)
  have hu := measureReal_mono (union_subset hXE hTE) (unit_subset_volume_ne_top hE)
  rw [measureReal_symmDiff_eq hX hT hxfin htfin,
    measureReal_sdiff' hT hxfin htfin,measureReal_sdiff' hX htfin hxfin,union_comm T X]
  linarith

namespace RationalUnitMobius

theorem generator_image_subset_restricted {c : ℕ} (F : Fin c → RationalUnitMobius)
    (p : Fin c) {A T : Set ℝ} (hunit : A⊆Icc (0:ℝ) 1) (hTA : T⊆A)
    (hmap : MapsTo (F p).whole.eval T (Icc (0:ℝ) 1)) :
    (F p).whole.eval '' T⊆restrictedImageUnion F A := by
  rintro y ⟨x,hx,rfl⟩
  exact Set.mem_iUnion.mpr ⟨p,x,⟨⟨hunit (hTA hx),hmap hx⟩,hTA hx⟩,rfl⟩

theorem family_subset_augmented {c : ℕ} (F : Fin c → RationalUnitMobius)
    (t : ℚ) (ht : |t|<1) (A : Set ℝ) :
    restrictedImageUnion F A⊆restrictedImageUnion (augmentedFamily F t ht) A := by
  rw [augmented_restrictedImageUnion]
  exact subset_union_left.trans subset_union_left

theorem inverse_family_subset_augmented {c : ℕ} (F : Fin c → RationalUnitMobius)
    (t : ℚ) (ht : |t|<1) (A : Set ℝ) :
    restrictedImageUnion (fun p => (F p).inverse) A⊆
      restrictedImageUnion (augmentedFamily F t ht) A := by
  rw [augmented_restrictedImageUnion]
  exact subset_union_right.trans subset_union_left

theorem NearIdentity.symmDiff_bound {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) {T E : Set ℝ}
    (hT : MeasurableSet T) (hunit : T⊆Icc (0:ℝ) 1) (hE : E⊆Icc (0:ℝ) 1)
    (hTE : T⊆E) (himage : G.whole.eval '' T⊆E) :
    volume.real ((G.whole.eval '' T) ∆ T) ≤ 2*volume.real E-(2-32*eta)*volume.real T := by
  have hx := G.whole.measurableSet_image_eval hT (by simpa [whole] using hunit)
  have hb := symmDiff_common_cover hx hT hE himage hTE
  have hl := (h.volume_distortion he hT hunit).1
  nlinarith only [hb,hl]

theorem augmented_small_expansion_symmDiff {c : ℕ} (F : Fin c → RationalUnitMobius)
    (t : ℚ) (ht : |t|<1) (p : Fin c) {eta r sigma : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8) (hr : 8*eta ≤ r)
    {A T : Set ℝ} (hT : MeasurableSet T) (hunit : A⊆Icc (0:ℝ) 1)
    (hTA : T⊆A) (hcentral : T⊆Icc r (1-r))
    (hsmall : volume.real (restrictedImageUnion (augmentedFamily F t ht) A) ≤
      (1+sigma)*volume.real A) :
    volume.real (((F p).whole.eval '' T) ∆ T) ≤
      2*sigma*volume.real A+2*(volume.real A-volume.real T)+32*eta*volume.real T ∧
    volume.real (((F p).inverse.whole.eval '' T) ∆ T) ≤
      2*sigma*volume.real A+2*(volume.real A-volume.real T)+32*eta*volume.real T := by
  let E := restrictedImageUnion (augmentedFamily F t ht) A
  have hE : E⊆Icc (0:ℝ) 1 := restrictedImageUnion_subset_unit _ A
  have hAE : A⊆E := (auxiliary_identity_subset t ht hunit).trans
    (auxiliary_subset_augmented F t ht A)
  have hTu := hTA.trans hunit
  have hp : (F p).whole.eval '' T⊆E :=
    (generator_image_subset_restricted F p hunit hTA
      (fun x hx => hnear.mapsTo_central he hr (hcentral hx))).trans
      (family_subset_augmented F t ht A)
  have hm : (F p).inverse.whole.eval '' T⊆E :=
    (generator_image_subset_restricted (fun p => (F p).inverse) p hunit hTA
      (fun x hx => hnear.inverse.mapsTo_central he hr (hcentral hx))).trans
      (inverse_family_subset_augmented F t ht A)
  have bp := hnear.symmDiff_bound he hT hTu hE (hTA.trans hAE) hp
  have bm := hnear.inverse.symmDiff_bound he hT hTu hE (hTA.trans hAE) hm
  change volume.real E ≤ _ at hsmall
  constructor <;> nlinarith only [bp,bm,hsmall]

theorem augmented_central_trim_symmDiff {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) (p : Fin c) {eta sigma delta : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8) (hr : 8*eta ≤ (m:ℝ)/K)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let T := gridTrim A (centralCells K m)
    volume.real (((F p).whole.eval '' T) ∆ T) ≤
      (2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta)*volume.real A ∧
    volume.real (((F p).inverse.whole.eval '' T) ∆ T) ≤
      (2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta)*volume.real A := by
  let T := gridTrim A (centralCells K m)
  have hk : 0<K := by omega
  have hcentral : T⊆Icc ((m:ℝ)/K) (1-(m:ℝ)/K) :=
    inter_subset_right.trans (centralCells_subset_interval hk)
  have hb := augmented_small_expansion_symmDiff F (unitStep K) (unitStep_small hK) p
    hnear he hr (gridTrim_measurable hA _) hunit (gridTrim_subset A _) hcentral hsmall
  have hl := (centralTrim_loss_bound hk hm hA hunit delta huniform).2
  have hmass : volume.real T ≤ volume.real A :=
    measureReal_mono (gridTrim_subset A _) (unit_subset_volume_ne_top hunit)
  have hweight := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 32) hnear.nonneg)
  change volume.real A-volume.real T ≤ _ at hl
  have hbudget : 2*sigma*volume.real A+2*(volume.real A-volume.real T)+32*eta*volume.real T ≤
      (2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta)*volume.real A := by
    calc
      _ ≤ 2*sigma*volume.real A+2*((2*(m:ℝ)/(K:ℝ))*(1+delta)*volume.real A)+
          32*eta*volume.real A :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (by norm_num))) hweight
      _ = _ := by ring
  exact ⟨hb.1.trans hbudget,hb.2.trans hbudget⟩

end RationalUnitMobius
end TransposeFollowup
