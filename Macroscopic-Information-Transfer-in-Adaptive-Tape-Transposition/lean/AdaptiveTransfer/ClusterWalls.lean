import NativeRelations.OneFreeHeadSmallExcursion

/-! Slab offset averaging for bounded-speed integer carriers. Each displacement
can change a slab index for at most its absolute length many offsets. -/

namespace AdaptiveTransfer
open Finset NativeRelations BoundedNesting
open scoped BigOperators

private theorem card_offsets_add_le (W : ℕ) (hW : 1 ≤ W) (z : ℤ) (n : ℕ) :
    ((range W).filter fun u => slabIdx W u z ≠ slabIdx W u (z + n)).card ≤ n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : ((range W).filter fun u => slabIdx W u z ≠ slabIdx W u (z + (n + 1 : ℕ))) ⊆
        ((range W).filter fun u => slabIdx W u z ≠ slabIdx W u (z + n)) ∪
        ((range W).filter fun u => slabIdx W u (z + n) ≠ slabIdx W u (z + (n + 1 : ℕ))) := by
      intro u hu
      obtain ⟨hu, hn⟩ := mem_filter.mp hu
      by_cases he : slabIdx W u z = slabIdx W u (z + n)
      · exact mem_union_right _ (mem_filter.mpr ⟨hu, fun hh => hn (he.trans hh)⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hu, he⟩)
    have hone := card_offset_transitions_step_le_one hW
      (z₁ := z + n) (z₂ := z + (n + 1 : ℕ)) (by push_cast; simp)
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

theorem card_offset_transitions_step_le_abs {W : ℕ} (hW : 1 ≤ W) (z₁ z₂ : ℤ) :
    ((range W).filter fun u => slabIdx W u z₁ ≠ slabIdx W u z₂).card ≤ (z₂ - z₁).natAbs := by
  by_cases hz : z₁ ≤ z₂
  · have hn : ((z₂ - z₁).natAbs : ℤ) = z₂ - z₁ := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have he : z₁ + ((z₂ - z₁).natAbs : ℤ) = z₂ := by omega
    simpa only [he] using card_offsets_add_le W hW z₁ (z₂ - z₁).natAbs
  · have hn : ((z₁ - z₂).natAbs : ℤ) = z₁ - z₂ := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have he : z₂ + ((z₁ - z₂).natAbs : ℤ) = z₁ := by omega
    have hh := card_offsets_add_le W hW z₂ (z₁ - z₂).natAbs
    rw [he] at hh
    have habs : (z₁ - z₂).natAbs = (z₂ - z₁).natAbs := by rw [← Int.natAbs_neg, neg_sub]
    simpa only [habs, ne_comm] using hh

/-- One offset pays at most total variation divided by slab width. -/
theorem exists_offset_slabTransitions_le_variation (y : ℕ → ℤ) {W : ℕ} (hW : 1 ≤ W)
    (T : ℕ) :
    ∃ u < W, (slabTransitions y W T u).card ≤
      (∑ t ∈ range (T - 1), (y (t + 1) - y t).natAbs) / W := by
  classical
  let V := ∑ t ∈ range (T - 1), (y (t + 1) - y t).natAbs
  have hsum : ∑ u ∈ range W, (slabTransitions y W T u).card ≤ V := by
    calc
      _ = ∑ u ∈ range W, ∑ t ∈ range (T - 1),
          if slabIdx W u (y t) ≠ slabIdx W u (y (t + 1)) then 1 else 0 := by
        apply sum_congr rfl
        intro u _
        exact card_filter _ _
      _ = ∑ t ∈ range (T - 1), ∑ u ∈ range W,
          if slabIdx W u (y t) ≠ slabIdx W u (y (t + 1)) then 1 else 0 := sum_comm
      _ = ∑ t ∈ range (T - 1),
          ((range W).filter fun u => slabIdx W u (y t) ≠ slabIdx W u (y (t + 1))).card := by
        apply sum_congr rfl
        intro t _
        exact (card_filter _ _).symm
      _ ≤ V := sum_le_sum fun t _ => card_offset_transitions_step_le_abs hW (y t) (y (t + 1))
  by_contra hall
  push Not at hall
  have hlower : ∑ _u ∈ range W, (V / W + 1) ≤
      ∑ u ∈ range W, (slabTransitions y W T u).card :=
    sum_le_sum fun u hu => hall u (mem_range.mp hu)
  rw [sum_const, card_range, smul_eq_mul] at hlower
  have hdiv := Nat.div_add_mod V W
  have hmod := Nat.mod_lt V (by omega : 0 < W)
  nlinarith

/-- A speed-m carrier incurs at most floor(m(T-1)/W) walls. -/
theorem exists_offset_slabTransitions_le_speed {y : ℕ → ℤ} {W m : ℕ}
    (hW : 1 ≤ W) (T : ℕ) (hy : ∀ t < T - 1, (y (t + 1) - y t).natAbs ≤ m) :
    ∃ u < W, (slabTransitions y W T u).card ≤ m * (T - 1) / W := by
  obtain ⟨u, hu, hc⟩ := exists_offset_slabTransitions_le_variation y hW T
  refine ⟨u, hu, hc.trans (Nat.div_le_div_right ?_)⟩
  calc
    _ ≤ ∑ _t ∈ range (T - 1), m := sum_le_sum fun t ht => hy t (mem_range.mp ht)
    _ = _ := by simp [Nat.mul_comm]

end AdaptiveTransfer
