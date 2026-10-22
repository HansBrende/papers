import TransposeFollowup.ClosedRationalExpansion
import Mathlib.MeasureTheory.Group.Measure

/-! The translation step of the continuous expansion proof. The actual
augmented family contains the original set and every legal positive or
negative translate. Moving one cell into its neighbor forces a measure
gain at least the difference of their occupied measures. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

theorem unit_subset_volume_ne_top {S : Set ℝ} (hS : S⊆Icc (0:ℝ) 1) : volume S≠⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono hS)

theorem translate_volume_real (t : ℝ) (S : Set ℝ) :
    volume.real ((fun x : ℝ => x+t) '' S)=volume.real S := by
  have he : (fun x : ℝ => x+t) '' S=(fun y : ℝ => y+(-t)) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y-t,hy,by ring⟩
  rw [he]
  exact congrArg ENNReal.toReal (measure_preimage_add_right volume (-t) S)

namespace RationalUnitMobius

theorem restrictedImageUnion_subset_unit {c : ℕ} (F : Fin c → RationalUnitMobius) (S : Set ℝ) :
    restrictedImageUnion F S⊆Icc (0:ℝ) 1 := by
  rintro y hy
  obtain ⟨p,x,⟨⟨_,hx⟩,_⟩,rfl⟩:=Set.mem_iUnion.mp hy
  exact hx

theorem auxiliary_identity_subset (t : ℚ) (ht : |t|<1) {S : Set ℝ} (hS : S⊆Icc (0:ℝ) 1) :
    S⊆restrictedImageUnion (auxiliaries t ht) S := by
  intro x hx
  have he:=(auxiliary_eval t ht x).2.2
  exact Set.mem_iUnion.mpr ⟨2,x,⟨⟨hS hx,by simpa only [mem_preimage,he] using hS hx⟩,hx⟩,he⟩

theorem auxiliary_add_subset (t : ℚ) (ht : |t|<1) {S B : Set ℝ}
    (hS : S⊆Icc (0:ℝ) 1) (hB : B⊆S) (hshift : (fun x : ℝ => x+t) '' B⊆Icc (0:ℝ) 1) :
    (fun x : ℝ => x+t) '' B⊆restrictedImageUnion (auxiliaries t ht) S := by
  rintro y ⟨x,hx,rfl⟩
  have he:=(auxiliary_eval t ht x).1
  exact Set.mem_iUnion.mpr ⟨0,x,⟨⟨hS (hB hx),by
    simpa only [mem_preimage,he] using hshift ⟨x,hx,rfl⟩⟩,hB hx⟩,he⟩

theorem auxiliary_sub_subset (t : ℚ) (ht : |t|<1) {S B : Set ℝ}
    (hS : S⊆Icc (0:ℝ) 1) (hB : B⊆S) (hshift : (fun x : ℝ => x-t) '' B⊆Icc (0:ℝ) 1) :
    (fun x : ℝ => x-t) '' B⊆restrictedImageUnion (auxiliaries t ht) S := by
  rintro y ⟨x,hx,rfl⟩
  have he:=(auxiliary_eval t ht x).2.1
  exact Set.mem_iUnion.mpr ⟨1,x,⟨⟨hS (hB hx),by
    simpa only [mem_preimage,he] using hshift ⟨x,hx,rfl⟩⟩,hB hx⟩,he⟩

theorem auxiliary_subset_augmented {c : ℕ} (F : Fin c → RationalUnitMobius)
    (t : ℚ) (ht : |t|<1) (S : Set ℝ) :
    restrictedImageUnion (auxiliaries t ht) S⊆restrictedImageUnion (augmentedFamily F t ht) S := by
  rw [augmented_restrictedImageUnion]
  exact subset_union_right

end RationalUnitMobius

/-- A set and a translated part of it are both contained in E. If that
part lands in D, its excess over the original occupancy of D is new mass. -/
theorem translated_part_gain {A C D E : Set ℝ} (t : ℝ) (hA : MeasurableSet A)
    (hE : E⊆Icc (0:ℝ) 1) (hAE : A⊆E)
    (hBE : (fun x : ℝ => x+t) '' (A∩C)⊆E)
    (hBD : (fun x : ℝ => x+t) '' (A∩C)⊆D) :
    volume.real A+volume.real (A∩C)-volume.real (A∩D)≤volume.real E := by
  let B := (fun x : ℝ => x+t) '' (A∩C)
  have hAfin : volume A≠⊤:=unit_subset_volume_ne_top (hAE.trans hE)
  have hBfin : volume B≠⊤:=unit_subset_volume_ne_top (hBE.trans hE)
  have hEq:=measureReal_union_add_inter' (μ:=volume) (s:=A) (t:=B) hA hAfin hBfin
  have hUnion : volume.real (A∪B)≤volume.real E:=
    measureReal_mono (union_subset hAE hBE) (unit_subset_volume_ne_top hE)
  have hInter : volume.real (A∩B)≤volume.real (A∩D):=
    measureReal_mono (inter_subset_inter_right A hBD) (measure_ne_top_of_subset inter_subset_left hAfin)
  have hB : volume.real B=volume.real (A∩C):=translate_volume_real t (A∩C)
  linarith

def unitStep (K : ℕ) : ℚ := 1/(K:ℚ)

theorem unitStep_cast (K : ℕ) : (unitStep K:ℝ)=1/(K:ℝ) := by
  simp [unitStep]

theorem unitStep_small {K : ℕ} (hK : 2≤K) : |unitStep K|<1 := by
  have hk : (1:ℚ)<K:=by exact_mod_cast (show 1<K by omega)
  have hp : (0:ℚ)<K:=lt_trans (by norm_num) hk
  rw [unitStep,abs_of_pos (div_pos (by norm_num) hp)]
  exact (div_lt_one hp).mpr hk

theorem gridCell_step_shift {K : ℕ} (i j : Fin K) (hji : j.val=i.val+1) :
    MapsTo (fun x : ℝ => x+(unitStep K:ℝ)) (gridCell i) (gridCell j) ∧
    MapsTo (fun x : ℝ => x-(unitStep K:ℝ)) (gridCell j) (gridCell i) := by
  have hK : (0:ℝ)<K:=by exact_mod_cast (show 0<K by have := i.isLt;omega)
  have ht : (K:ℝ)*(unitStep K:ℝ)=1 := by rw [unitStep_cast,mul_one_div_cancel hK.ne']
  have hj : (j.val:ℝ)=(i.val:ℝ)+1:=by exact_mod_cast hji
  constructor
  · intro x hx
    change (i.val:ℝ)<(K:ℝ)*x ∧ (K:ℝ)*x<(i.val:ℝ)+1 at hx
    change (j.val:ℝ)<(K:ℝ)*(x+(unitStep K:ℝ)) ∧ (K:ℝ)*(x+(unitStep K:ℝ))<(j.val:ℝ)+1
    constructor <;> nlinarith [hx.1,hx.2]
  · intro x hx
    change (j.val:ℝ)<(K:ℝ)*x ∧ (K:ℝ)*x<(j.val:ℝ)+1 at hx
    change (i.val:ℝ)<(K:ℝ)*(x-(unitStep K:ℝ)) ∧ (K:ℝ)*(x-(unitStep K:ℝ))<(i.val:ℝ)+1
    constructor <;> nlinarith [hx.1,hx.2]

namespace RationalUnitMobius

theorem augmented_adjacent_gain {c K : ℕ} (F : Fin c → RationalUnitMobius) (hK : 2≤K)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (i j : Fin K) (hji : j.val=i.val+1) :
    volume.real A+|volume.real (A∩gridCell i)-volume.real (A∩gridCell j)|≤
      volume.real (restrictedImageUnion (augmentedFamily F (unitStep K) (unitStep_small hK)) A) := by
  let E := restrictedImageUnion (augmentedFamily F (unitStep K) (unitStep_small hK)) A
  have hE : E⊆Icc (0:ℝ) 1:=restrictedImageUnion_subset_unit _ A
  have hAE : A⊆E:=(auxiliary_identity_subset _ (unitStep_small hK) hunit).trans
    (auxiliary_subset_augmented F _ (unitStep_small hK) A)
  have hp : (fun x : ℝ => x+(unitStep K:ℝ)) '' (A∩gridCell i)⊆gridCell j := by
    rintro y ⟨x,hx,rfl⟩
    exact (gridCell_step_shift i j hji).1 hx.2
  have hm : (fun x : ℝ => x-(unitStep K:ℝ)) '' (A∩gridCell j)⊆gridCell i := by
    rintro y ⟨x,hx,rfl⟩
    exact (gridCell_step_shift i j hji).2 hx.2
  have hPE : (fun x : ℝ => x+(unitStep K:ℝ)) '' (A∩gridCell i)⊆E :=
    (auxiliary_add_subset _ (unitStep_small hK) hunit inter_subset_left
      (hp.trans (gridCell_subset_unit j))).trans (auxiliary_subset_augmented F _ _ A)
  have hME : (fun x : ℝ => x-(unitStep K:ℝ)) '' (A∩gridCell j)⊆E :=
    (auxiliary_sub_subset _ (unitStep_small hK) hunit inter_subset_left
      (hm.trans (gridCell_subset_unit i))).trans (auxiliary_subset_augmented F _ _ A)
  have hpos:=translated_part_gain (unitStep K:ℝ) hA hE hAE hPE hp
  have hneg:=translated_part_gain (-(unitStep K:ℝ)) hA hE hAE
    (by simpa only [sub_eq_add_neg] using hME) (by simpa only [sub_eq_add_neg] using hm)
  have hab : |volume.real (A∩gridCell i)-volume.real (A∩gridCell j)|≤
      volume.real E-volume.real A := abs_le.mpr ⟨by linarith,by linarith⟩
  linarith

end RationalUnitMobius
end TransposeFollowup
