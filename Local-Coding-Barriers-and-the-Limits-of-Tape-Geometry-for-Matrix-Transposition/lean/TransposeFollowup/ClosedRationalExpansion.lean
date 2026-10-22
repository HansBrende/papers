import TransposeFollowup.RationalUnitRestriction

/-! Closed-domain image expansion transfers exactly to the open-domain
interface. Only finitely many endpoint images are removed, so equality
holds even for outer measures of arbitrary sets. Native padding adapters
are isolated in ClosedNativePadding to keep this analytic API independent. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

def rationalClosedImageUnion {c : ℕ} (F : Fin c → RationalMobius) (S : Set ℝ) : Set ℝ :=
  ⋃ p,(F p).eval '' (Icc ((F p).lo:ℝ) (F p).hi ∩ S)

def rationalEndpointImages {c : ℕ} (F : Fin c → RationalMobius) : Set ℝ :=
  Set.range (fun p => (F p).eval (F p).lo) ∪ Set.range (fun p => (F p).eval (F p).hi)

theorem rationalEndpointImages_volume {c : ℕ} (F : Fin c → RationalMobius) :
    volume (rationalEndpointImages F)=0 :=
  ((Set.finite_range _).union (Set.finite_range _)).measure_zero volume

theorem rational_open_image_subset_closed {c : ℕ} (F : Fin c → RationalMobius) (S : Set ℝ) :
    mapImageUnion (rationalFamilyMaps F) S⊆rationalClosedImageUnion F S := by
  intro y hy
  obtain ⟨p,x,⟨hx,hS⟩,he⟩:=Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨p,x,⟨Ioo_subset_Icc_self hx,hS⟩,he⟩

theorem rational_closed_image_cover {c : ℕ} (F : Fin c → RationalMobius) (S : Set ℝ) :
    rationalClosedImageUnion F S⊆
      mapImageUnion (rationalFamilyMaps F) S ∪ rationalEndpointImages F := by
  intro y hy
  obtain ⟨p,x,⟨hx,hS⟩,rfl⟩:=Set.mem_iUnion.mp hy
  by_cases hl : x=((F p).lo:ℝ)
  · exact Or.inr (Or.inl ⟨p,by rw [hl]⟩)
  by_cases hh : x=((F p).hi:ℝ)
  · exact Or.inr (Or.inr ⟨p,by rw [hh]⟩)
  exact Or.inl (Set.mem_iUnion.mpr ⟨p,x,⟨⟨lt_of_le_of_ne hx.1 (Ne.symm hl),
    lt_of_le_of_ne hx.2 hh⟩,hS⟩,rfl⟩)

theorem rational_closed_image_volume {c : ℕ} (F : Fin c → RationalMobius) (S : Set ℝ) :
    volume (rationalClosedImageUnion F S)=volume (mapImageUnion (rationalFamilyMaps F) S) := by
  apply le_antisymm
  · calc
      _ ≤ volume (mapImageUnion (rationalFamilyMaps F) S ∪ rationalEndpointImages F) :=
        measure_mono (rational_closed_image_cover F S)
      _ ≤ volume (mapImageUnion (rationalFamilyMaps F) S)+volume (rationalEndpointImages F) :=
        measure_union_le _ _
      _ = _ := by rw [rationalEndpointImages_volume,add_zero]
  · exact measure_mono (rational_open_image_subset_closed F S)

theorem rational_closed_image_volume_real {c : ℕ} (F : Fin c → RationalMobius) (S : Set ℝ) :
    volume.real (rationalClosedImageUnion F S)=volume.real (mapImageUnion (rationalFamilyMaps F) S) :=
  congrArg ENNReal.toReal (rational_closed_image_volume F S)

namespace RationalUnitMobius

/-- Precisely the closed unit input/output restriction in the source construction. -/
def restrictedImageUnion {c : ℕ} (F : Fin c → RationalUnitMobius) (S : Set ℝ) : Set ℝ :=
  ⋃ p,(F p).whole.eval '' ((Icc (0:ℝ) 1 ∩ (F p).whole.eval ⁻¹' Icc (0:ℝ) 1) ∩ S)

def clippedFamily {c : ℕ} (F : Fin c → RationalUnitMobius) : Fin c → RationalMobius :=
  fun p => (F p).clipped

theorem restrictedImageUnion_eq_closed {c : ℕ} (F : Fin c → RationalUnitMobius) (S : Set ℝ) :
    restrictedImageUnion F S=rationalClosedImageUnion (clippedFamily F) S := by
  unfold restrictedImageUnion rationalClosedImageUnion clippedFamily
  simp_rw [clipped_domain,clipped_eval]

theorem restrictedImageUnion_volume_real {c : ℕ} (F : Fin c → RationalUnitMobius) (S : Set ℝ) :
    volume.real (restrictedImageUnion F S)=
      volume.real (mapImageUnion (rationalFamilyMaps (clippedFamily F)) S) := by
  rw [restrictedImageUnion_eq_closed,rational_closed_image_volume_real]

theorem clippedFamily_mapsTo {c : ℕ} (F : Fin c → RationalUnitMobius) (p : Fin c) :
    MapsTo (rationalFamilyMaps (clippedFamily F) p).map
      (rationalFamilyMaps (clippedFamily F) p).domain (Icc (0:ℝ) 1) :=
  (F p).clipped_open_mapsTo

theorem restricted_expansion_to_open {c : ℕ} (F : Fin c → RationalUnitMobius) (eps : ℝ)
    (hexp : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (restrictedImageUnion F S)) :
    ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion (rationalFamilyMaps (clippedFamily F)) S) := by
  intro S hS hunit hvol
  simpa only [restrictedImageUnion_volume_real] using hexp S hS hunit hvol

theorem augmented_restrictedImageUnion {c : ℕ} (F : Fin c → RationalUnitMobius)
    (t : ℚ) (ht : |t|<1) (S : Set ℝ) :
    restrictedImageUnion (augmentedFamily F t ht) S=
      restrictedImageUnion F S ∪ restrictedImageUnion (fun p => (F p).inverse) S ∪
        restrictedImageUnion (auxiliaries t ht) S := by
  ext y
  simp only [restrictedImageUnion,augmentedFamily,Set.mem_iUnion,Set.mem_union]
  constructor
  · rintro ⟨p,hp⟩
    induction p using Fin.addCases with
    | left p =>
      induction p using Fin.addCases with
      | left p => exact Or.inl (Or.inl ⟨p,by simpa only [Fin.addCases_left] using hp⟩)
      | right p => exact Or.inl (Or.inr ⟨p,by simpa only [Fin.addCases_left,Fin.addCases_right] using hp⟩)
    | right p => exact Or.inr ⟨p,by simpa only [Fin.addCases_right] using hp⟩
  · rintro ((⟨p,hp⟩ | ⟨p,hp⟩) | ⟨p,hp⟩)
    · exact ⟨Fin.castAdd 3 (Fin.castAdd c p),by simpa only [Fin.addCases_left] using hp⟩
    · exact ⟨Fin.castAdd 3 (Fin.natAdd c p),by simpa only [Fin.addCases_left,Fin.addCases_right] using hp⟩
    · exact ⟨Fin.natAdd (c+c) p,by simpa only [Fin.addCases_right] using hp⟩

end RationalUnitMobius


end TransposeFollowup
