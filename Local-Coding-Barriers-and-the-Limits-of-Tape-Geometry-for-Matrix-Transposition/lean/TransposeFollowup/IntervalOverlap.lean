import TransposeFollowup.GridCellMeasure
import Mathlib.Topology.Order.IntermediateValue

/-! Open interval overlap under a continuous strictly increasing map is
decided by clipped endpoints. Nonempty overlap is equivalent to positive
Lebesgue length, so a lone endpoint never creates an edge. -/

namespace TransposeFollowup

open Set MeasureTheory
set_option autoImplicit false

def clippedImage (f : ℝ → ℝ) (a b s t u v : ℝ) : Set ℝ :=
  (f '' (Ioo a b ∩ Ioo s t)) ∩ Ioo u v

theorem clippedImage_eq_Ioo {f : ℝ → ℝ} {a b s t u v : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b))
    (hclip : max a s < min b t) :
    clippedImage f a b s t u v = Ioo (max (f (max a s)) u) (min (f (min b t)) v) := by
  have hsub : Icc (max a s) (min b t) ⊆ Icc a b := by
    intro x hx
    exact ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  rw [clippedImage, Ioo_inter_Ioo,
    (hc.mono hsub).image_Ioo_of_strictMonoOn hclip.le (hm.mono hsub), Ioo_inter_Ioo]

theorem clippedImage_empty {f : ℝ → ℝ} {a b s t u v : ℝ}
    (hclip : ¬max a s < min b t) : clippedImage f a b s t u v = ∅ := by
  rw [clippedImage, Ioo_inter_Ioo, Ioo_eq_empty hclip]
  simp

theorem clippedImage_nonempty_iff {f : ℝ → ℝ} {a b s t u v : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    (clippedImage f a b s t u v).Nonempty ↔
      max a s < min b t ∧ max (f (max a s)) u < min (f (min b t)) v := by
  by_cases hclip : max a s < min b t
  · rw [clippedImage_eq_Ioo hc hm hclip, nonempty_Ioo]
    exact (and_iff_right hclip).symm
  · rw [clippedImage_empty hclip]
    simp [hclip]

theorem clippedImage_positive_iff {f : ℝ → ℝ} {a b s t u v : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    0 < volume.real (clippedImage f a b s t u v) ↔
      (clippedImage f a b s t u v).Nonempty := by
  by_cases hclip : max a s < min b t
  · rw [clippedImage_eq_Ioo hc hm hclip, Real.volume_real_Ioo, nonempty_Ioo]
    simp only [lt_max_iff, lt_self_iff_false, or_false, sub_pos]
  · rw [clippedImage_empty hclip]
    simp

theorem interval_overlap_iff {f : ℝ → ℝ} {a b s t u v : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    (∃ x ∈ Ioo a b, x ∈ Ioo s t ∧ f x ∈ Ioo u v) ↔
      max a s < min b t ∧ max (f (max a s)) u < min (f (min b t)) v := by
  rw [← clippedImage_nonempty_iff hc hm]
  constructor
  · rintro ⟨x, hxd, hxs, hfx⟩
    exact ⟨f x, ⟨x, ⟨hxd, hxs⟩, rfl⟩, hfx⟩
  · rintro ⟨y, ⟨x, ⟨hxd, hxs⟩, rfl⟩, hfx⟩
    exact ⟨x, hxd, hxs, hfx⟩

end TransposeFollowup
