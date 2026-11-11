import AdaptiveTransfer.FeedbackCoordinates
import LeanMachine.GridPartition

/-! Literal matrix coordinates, row groups, and chronological column windows.
Rectangle capacities are derived from coordinate cardinalities. -/

namespace AdaptiveTransfer
open TransposeFollowup LeanMachine Finset Classical

abbrev FeedbackMatrixBit (d b : ℕ) := Fin d × Fin d × Fin b

def feedbackRowOwner {d b : ℕ} (group : Fin d → Fin d) : FeedbackMatrixBit d b → Fin d :=
  fun i => group i.1

noncomputable def feedbackColumns {d b : ℕ} (columns : Finset (Fin d)) :
    Finset (FeedbackMatrixBit d b) := univ.filter (fun i => i.2.1 ∈ columns)

theorem feedback_rectangle_card {d b : ℕ} (group : Fin d → Fin d)
    (columns : Finset (Fin d)) (a : Fin d) :
    (ownedCoordinates (feedbackRowOwner (b := b) group) a ∩ feedbackColumns columns).card =
      ((univ : Finset (Fin d)).filter (fun r => group r = a)).card * columns.card * b := by
  have he : ownedCoordinates (feedbackRowOwner (b := b) group) a ∩ feedbackColumns columns =
      ((univ : Finset (Fin d)).filter (fun r => group r = a)).product
        (columns.product (univ : Finset (Fin b))) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hr, hc⟩ := mem_inter.mp hi
      have hr' : group i.1 = a := (mem_filter.mp hr).2
      have hc' : i.2.1 ∈ columns := (mem_filter.mp hc).2
      exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, hr'⟩,
        mem_product.mpr ⟨hc', mem_univ _⟩⟩
    · intro hi
      obtain ⟨hr, hc⟩ := mem_product.mp hi
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hr).2⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_product.mp hc).1⟩⟩
  rw [he]
  change Finset.card (_ ×ˢ (_ ×ˢ (univ : Finset (Fin b)))) = _
  rw [Finset.card_product, Finset.card_product, card_univ, Fintype.card_fin]
  ring

theorem feedback_grid_rectangle_le {d b g θ : ℕ} (hg : 0 < g) (hθ : θ < g)
    (columns : Finset (Fin d)) (a : Fin d) :
    (ownedCoordinates (feedbackRowOwner (b := b) (ShiftedGrid.finiteLabel d g θ hg hθ)) a ∩
      feedbackColumns columns).card ≤ g * columns.card * b := by
  rw [feedback_rectangle_card]
  exact Nat.mul_le_mul_right b (Nat.mul_le_mul_right columns.card
    (ShiftedGrid.finiteLabel_fiber_card_le d g θ hg hθ a))

/-- The fixed output order may be any permutation of the columns. -/
noncomputable def feedbackWindowColumns {d w : ℕ} (hw : 0 < w) (order : Equiv.Perm (Fin d))
    (a : Fin ⌈(d : ℝ)/w⌉₊) : Finset (Fin d) :=
  ((univ : Finset (Fin d)).filter (fun r => ShiftedGrid.windowLabel d w hw r = a)).image order

theorem feedbackWindowColumns_card_le {d w : ℕ} (hw : 0 < w) (order : Equiv.Perm (Fin d))
    (a : Fin ⌈(d : ℝ)/w⌉₊) : (feedbackWindowColumns hw order a).card ≤ w := by
  rw [feedbackWindowColumns, card_image_of_injective _ order.injective]
  exact ShiftedGrid.windowLabel_fiber_card_le d w hw a

theorem feedbackWindowColumns_cover {d w : ℕ} (hw : 0 < w) (order : Equiv.Perm (Fin d))
    (j : Fin d) : ∃ a, j ∈ feedbackWindowColumns hw order a := by
  refine ⟨ShiftedGrid.windowLabel d w hw (order.symm j), mem_image.mpr ?_⟩
  exact ⟨order.symm j, mem_filter.mpr ⟨mem_univ _, rfl⟩, order.apply_symm_apply j⟩

theorem feedback_matrix_window_cover {d b w : ℕ} (hw : 0 < w)
    (order : Equiv.Perm (Fin d)) (i : FeedbackMatrixBit d b) :
    ∃ a, i ∈ feedbackColumns (b := b) (feedbackWindowColumns hw order a) := by
  obtain ⟨a, ha⟩ := feedbackWindowColumns_cover hw order i.2.1
  exact ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩⟩

theorem feedback_matrix_window_card_le {d b g θ w : ℕ} (hg : 0 < g) (hθ : θ < g)
    (hw : 0 < w) (order : Equiv.Perm (Fin d)) (a : Fin d) (j : Fin ⌈(d : ℝ)/w⌉₊) :
    (ownedCoordinates (feedbackRowOwner (b := b) (ShiftedGrid.finiteLabel d g θ hg hθ)) a ∩
      feedbackColumns (feedbackWindowColumns hw order j)).card ≤ g * w * b :=
  (feedback_grid_rectangle_le hg hθ _ a).trans (Nat.mul_le_mul_right b
    (Nat.mul_le_mul_left g (feedbackWindowColumns_card_le hw order j)))

end AdaptiveTransfer
