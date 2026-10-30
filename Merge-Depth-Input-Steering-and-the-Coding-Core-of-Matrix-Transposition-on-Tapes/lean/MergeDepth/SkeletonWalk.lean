import BoundedNesting.OwnerLoad

/-!
# Skeleton walks

The *skeleton walk* of a walk `x` at scale `w ≥ 1` is `t ↦ ⌊x t / w⌋`: the block of `w` cells that
contains the head. It is again a walk (`isWalk_skel`).

`entries_skel_subset`: an entry of a block by the skeleton walk is an entry of one of the two end
cells of the block by the walk, if the walk starts at cell `0`. So if the walk enters every cell at
most `ℓ` times, its skeleton walk enters every block at most `2ℓ` times (`card_entries_skel_le`).
-/

namespace MergeDepth

open Finset BoundedNesting

/-- The skeleton walk of `x` at scale `w`: the index of the block of `w` cells containing `x t`. -/
def skel (w : ℤ) (x : ℕ → ℤ) : ℕ → ℤ := fun t => x t / w

/-- The block of `a` brackets `a`: `w ⌊a/w⌋ ≤ a < w ⌊a/w⌋ + w`. -/
theorem block_bounds {w : ℤ} (hw : 0 < w) (a : ℤ) : w * (a / w) ≤ a ∧ a < w * (a / w) + w := by
  have h := Int.mul_ediv_add_emod a w
  have h0 := Int.emod_nonneg a hw.ne'
  have h1 := Int.emod_lt_of_pos a hw
  constructor <;> linarith

theorem block_gap {w : ℤ} (hw : 0 < w) {q q' : ℤ} (h : q < q') : w * q + w ≤ w * q' := by
  have : w * (q + 1) ≤ w * q' := mul_le_mul_of_nonneg_left (by omega) hw.le
  linarith

/-- One step of a walk moves its block by at most one. -/
theorem skel_step {w : ℤ} (hw : 0 < w) {a b : ℤ} (h : |b - a| ≤ 1) :
    |b / w - a / w| ≤ 1 := by
  have h1 := abs_le.mp h
  obtain ⟨ha0, ha1⟩ := block_bounds hw a
  obtain ⟨hb0, hb1⟩ := block_bounds hw b
  rw [abs_le]
  constructor
  · by_contra hc
    have := block_gap hw (show b / w + 1 < a / w by omega)
    linarith
  · by_contra hc
    have := block_gap hw (show a / w + 1 < b / w by omega)
    linarith

/-- The skeleton walk of a walk is a walk. -/
theorem isWalk_skel {w : ℤ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) : IsWalk (skel w x) :=
  fun t => skel_step hw (hx t)

/-- When the block changes in one step, the walk moves to an end cell of the new block, which it
did not occupy before. -/
theorem end_cell_of_block_change {w : ℤ} (hw : 0 < w) {a b : ℤ} (h : |b - a| ≤ 1)
    (hne : a / w ≠ b / w) : (b = w * (b / w) ∨ b = w * (b / w) + w - 1) ∧ a ≠ b := by
  have h1 := abs_le.mp h
  obtain ⟨ha0, ha1⟩ := block_bounds hw a
  obtain ⟨hb0, hb1⟩ := block_bounds hw b
  refine ⟨?_, fun hab => hne (by rw [hab])⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := block_gap hw hlt
    left
    linarith
  · have := block_gap hw hgt
    right
    linarith

/-- **Entries of the skeleton walk.** If the walk starts at cell `0`, every entry of block `b` by
its skeleton walk is an entry of one of the end cells `w b` and `w b + w - 1` by the walk. -/
theorem entries_skel_subset {w : ℤ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) (h0 : x 0 = 0)
    (b : ℤ) (T : ℕ) :
    entries (skel w x) b T ⊆ entries x (w * b) T ∪ entries x (w * b + w - 1) T := by
  intro t ht
  obtain ⟨htT, hb, ht0⟩ := mem_filter.mp ht
  simp only [skel] at hb ht0
  rcases ht0 with rfl | hne
  · -- time `0`: the walk is at cell `0 = w ⋅ 0`
    have : b = 0 := by rw [← hb, h0, Int.zero_ediv]
    subst this
    exact mem_union_left _ (mem_filter.mpr ⟨htT, by simp [h0], Or.inl rfl⟩)
  · have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · exact absurd hb (by simpa using hne)
      · exact h
    have hstep : |x t - x (t - 1)| ≤ 1 := by
      have := hx (t - 1)
      rwa [Nat.sub_add_cancel ht1] at this
    obtain ⟨hend, hmove⟩ := end_cell_of_block_change hw hstep (by rw [hb]; exact hne)
    rw [hb] at hend
    rcases hend with he | he
    · exact mem_union_left _ (mem_filter.mpr ⟨htT, he, Or.inr (fun h => hmove (h.trans he.symm))⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨htT, he, Or.inr (fun h => hmove (h.trans he.symm))⟩)

/-- **Bounded entry passes to skeleton walks.** If a walk starting at cell `0` enters every cell at
most `ℓ` times, its skeleton walk enters every block at most `2ℓ` times. -/
theorem card_entries_skel_le {w : ℤ} (hw : 0 < w) {x : ℕ → ℤ} (hx : IsWalk x) (h0 : x 0 = 0)
    {ℓ T : ℕ} (hℓ : ∀ c, (entries x c T).card ≤ ℓ) (b : ℤ) :
    (entries (skel w x) b T).card ≤ 2 * ℓ :=
  calc (entries (skel w x) b T).card
      ≤ (entries x (w * b) T ∪ entries x (w * b + w - 1) T).card :=
        card_le_card (entries_skel_subset hw hx h0 b T)
    _ ≤ (entries x (w * b) T).card + (entries x (w * b + w - 1) T).card := card_union_le _ _
    _ ≤ 2 * ℓ := by have := hℓ (w * b); have := hℓ (w * b + w - 1); omega

end MergeDepth
