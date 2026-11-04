import BoundedStackDepth.Budgets
import BoundedStackDepth.WrapGlobal

/-!
# The weight of the events

The events of a frame system weigh `2^{scale}` each. For the WRAP and time-edge sums:
* `sum_turns_weight_le`: the turning points of a walk weigh at most `2(T − 1)` (`2^{band m} ≤ m` and (P2));
* `card_segStarts_le`: there are at most `#frames + T` segment starts (one per frame start, and a restart
  determines its frame, the innermost frame of its time);
* `sum_segStarts_weight_le`: the segment starts weigh at most the segments' weight plus their number (a
  segment start without own times has scale `0`).
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {S : FrameSystem}

/-- The turning points of a walk weigh at most `2(T − 1)`. -/
theorem sum_turns_weight_le (hx : IsWalk S.x) :
    ∑ s ∈ turnsOf S, 2 ^ band (prom S.x S.T s) ≤ 2 * (S.T - 1) := by
  calc ∑ s ∈ turnsOf S, 2 ^ band (prom S.x S.T s) ≤ ∑ s ∈ turnsOf S, prom S.x S.T s :=
        sum_le_sum fun s hs => pow_band_le (by have := (mem_filter.mp hs).2; omega)
    _ ≤ ∑ s ∈ range S.T, prom S.x S.T s := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ 2 * (S.T - 1) := sum_prom_le_two_mul hx S.T

/-- There are at most `#frames + T` segment starts. -/
theorem card_segStarts_le : (segStarts S).card ≤ S.frames.card + S.T := by
  classical
  have hsplit : segStarts S ⊆ (S.frames.image fun F => (F, F.1)) ∪
      ((range S.T).image fun t => (S.inner t, t)) := by
    intro Fs hFs
    obtain ⟨hmem, hst⟩ := mem_filter.mp hFs
    obtain ⟨hF, ht⟩ := mem_product.mp hmem
    rcases hst with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨Fs.1, hF, by rw [← h]⟩)
    · refine mem_union_right _ (mem_image.mpr ⟨Fs.2, ht, ?_⟩)
      rw [inner_eq h.2.2]
  calc (segStarts S).card ≤ _ := card_le_card hsplit
    _ ≤ _ := card_union_le _ _
    _ ≤ S.frames.card + S.T := Nat.add_le_add card_image_le (card_image_le.trans (card_range _).le)

/-- The segment starts weigh at most the segments' weight plus their number. -/
theorem sum_segStarts_weight_le :
    ∑ Fs ∈ segStarts S, 2 ^ segScale S Fs.1 Fs.2 ≤
      ∑ σ ∈ S.segments, 2 ^ band (S.segMax σ) + (segStarts S).card := by
  classical
  rw [← sum_filter_add_sum_filter_not (segStarts S) (· ∈ S.segments)]
  refine Nat.add_le_add ?_ ?_
  · calc ∑ Fs ∈ (segStarts S).filter (· ∈ S.segments), 2 ^ segScale S Fs.1 Fs.2
        = ∑ Fs ∈ (segStarts S).filter (· ∈ S.segments), 2 ^ band (S.segMax Fs) :=
          sum_congr rfl fun Fs _ => by rw [segScale_eq]
      _ ≤ ∑ σ ∈ S.segments, 2 ^ band (S.segMax σ) :=
          sum_le_sum_of_subset fun Fs hFs => (mem_filter.mp hFs).2
  · calc ∑ Fs ∈ (segStarts S).filter (· ∉ S.segments), 2 ^ segScale S Fs.1 Fs.2
        = ∑ Fs ∈ (segStarts S).filter (· ∉ S.segments), 1 := sum_congr rfl fun Fs hFs => by
          rw [segScale_eq]
          have hnot := (mem_filter.mp hFs).2
          have : S.segTimes Fs = ∅ := by
            refine filter_eq_empty_iff.mpr fun t ht he => hnot ?_
            exact mem_image.mpr ⟨t, ht, he⟩
          simp [segMax, this]
      _ ≤ (segStarts S).card := by
          rw [sum_const, smul_eq_mul, mul_one]
          exact card_filter_le _ _

/-- The band of `M` is at most `M`. -/
theorem band_le_self (M : ℕ) : band M ≤ M := Nat.log_le_self 2 M

/-- For a walk, the running maximum at `t` is at most `t`. -/
theorem runMax_le_self (hx : IsWalk S.x) (F : ℕ × ℕ) (t : ℕ) : S.runMax F t ≤ t := by
  refine runMax_le fun t' _ h1 h2 => ?_
  have := hx.lip h1
  omega

/-- A positive group's floor is at least the group. -/
theorem le_flr {h₀ r g : ℕ} (hr : r < h₀) (hg : 1 ≤ g) : g ≤ flr h₀ r g := by
  unfold flr
  have : h₀ * g = h₀ * (g - 1) + h₀ := by rw [← Nat.mul_succ]; congr 1; omega
  have : g - 1 ≤ h₀ * (g - 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The group of a rise at a time before `T` is below `T`. -/
theorem lt_of_rise (hx : IsWalk S.x) {h₀ r t g : ℕ} (hr : r < h₀) (htT : t < S.T)
    (h : S.RiseAt h₀ r t g) : g < S.T := by
  have h1 := le_flr hr h.1
  have h2 := h.2.2.2.2.2
  have h3 := band_le_self (S.runMax (S.inner t) t)
  have h4 := runMax_le_self hx (S.inner t) t
  omega

/-- The group of a last-stint end at a time before `T` is below `T`. -/
theorem lt_of_lastStint (hx : IsWalk S.x) {h₀ r t g : ℕ} (hr : r < h₀) (htT : t < S.T)
    (h : S.LastStintAt h₀ r t g) : g < S.T := by
  have h1 := le_flr hr h.1
  have h2 := h.2.1
  have h3 := band_le_self (S.runMax (S.inner (t - 1)) (t - 1))
  have h4 := runMax_le_self hx (S.inner (t - 1)) (t - 1)
  omega

end BoundedStackDepth
