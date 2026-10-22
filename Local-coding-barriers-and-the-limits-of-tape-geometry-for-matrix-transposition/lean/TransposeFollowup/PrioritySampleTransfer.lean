import TransposeFollowup.AffinePriorityLabels

/-! Exact transfer of union and symmetric-difference counts through an
injective evaluation, and from integer grid values to the finite priority
universe. All image facts are applications of existing mathlib APIs. -/
namespace TransposeFollowup.AffineMotion
open Classical Finset Set
open scoped ENNReal
set_option autoImplicit false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem image_union_card_of_injOn (A B : Finset α) (f : α → β)
    (hf : Set.InjOn f (↑(A ∪ B))) :
    (A.image f ∪ B.image f).card=(A ∪ B).card := by
  rw [← Finset.image_union]
  exact Finset.card_image_of_injOn hf

theorem image_disagreement_card_of_injOn (A B : Finset α) (f : α → β)
    (hf : Set.InjOn f (↑(A ∪ B))) :
    ((A.image f ∪ B.image f) \ (A.image f ∩ B.image f)).card=
      ((A ∪ B) \ (A ∩ B)).card := by
  have hs : A ∩ B ⊆ A ∪ B := Finset.inter_subset_left.trans Finset.subset_union_left
  have he : ((A ∪ B) \ (A ∩ B)).image f=
      (A.image f ∪ B.image f) \ (A.image f ∩ B.image f) := by
    rw [Finset.image_sdiff_of_injOn hf hs,Finset.image_union,
      Finset.image_inter_of_injOn A B (by simpa only [Finset.coe_union] using hf)]
  rw [← he]
  exact Finset.card_image_of_injOn (hf.mono (fun _ hx => (Finset.mem_sdiff.mp hx).1))

theorem image_disagreement_ratio_of_injOn (A B : Finset α) (f : α → β)
    (hf : Set.InjOn f (↑(A ∪ B))) (δ : ℝ≥0∞)
    (hδ : (((A ∪ B) \ (A ∩ B)).card : ℝ≥0∞) ≤ δ*(A ∪ B).card) :
    (((A.image f ∪ B.image f) \ (A.image f ∩ B.image f)).card : ℝ≥0∞) ≤
      δ*(A.image f ∪ B.image f).card := by
  rw [image_disagreement_card_of_injOn A B f hf,image_union_card_of_injOn A B f hf]
  exact hδ

theorem gridSample_values_image {ι : Type*} [Fintype ι]
    (C : Finset ℤ) (q : ι → ℤ) (hq : ∀ i, q i ∈ C) :
    (gridSample C q).image (fun z : C => z.val)=Finset.univ.image q := by
  ext z
  constructor
  · intro hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
  · intro hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨⟨q i,hq i⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,rfl⟩,rfl⟩

theorem gridSample_disagreement_ratio {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Finset ℤ) (q : ι → ℤ) (r : κ → ℤ)
    (hq : ∀ i, q i ∈ C) (hr : ∀ j, r j ∈ C) (δ : ℝ≥0∞)
    (hδ : (((Finset.univ.image q ∪ Finset.univ.image r) \
      (Finset.univ.image q ∩ Finset.univ.image r)).card : ℝ≥0∞) ≤
      δ*(Finset.univ.image q ∪ Finset.univ.image r).card) :
    (((gridSample C q ∪ gridSample C r) \ (gridSample C q ∩ gridSample C r)).card : ℝ≥0∞) ≤
      δ*(gridSample C q ∪ gridSample C r).card := by
  rw [← gridSample_values_image C q hq,← gridSample_values_image C r hr] at hδ
  have hinj : Set.InjOn (fun z : C => z.val) (↑(gridSample C q ∪ gridSample C r)) :=
    Subtype.val_injective.injOn
  simpa only [image_disagreement_card_of_injOn _ _ _ hinj,
    image_union_card_of_injOn _ _ _ hinj] using hδ

end TransposeFollowup.AffineMotion
