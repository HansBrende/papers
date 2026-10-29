import LeanMachine.WeightedCircularGap
import Mathlib.Data.Nat.Choose.Sum

/-! Circular gap moments by counting empty forward arcs. This connects the
actual increasing anchor enumeration to subset counting, without an
auxiliary probability model or a positive-composition bijection. -/

namespace LeanMachine.CyclicSelection

open Finset
open scoped BigOperators Classical
noncomputable section

theorem self_not_mem_forward_arc {L a j : ℕ} (ha : a < L) (hj : j < L) :
    a ∉ arc L (a + 1) j := by
  rintro h
  obtain ⟨t, ht, he⟩ := mem_image.mp h
  have ht' := mem_range.mp ht
  have h := WeightedCircularGap.forward_mod_add ha (show 1 + t < L by omega)
  rw [← Nat.add_assoc, he] at h
  simp [forward] at h
  omega

/-- The end of each enumerated gap is another anchor, including wraparound. -/
theorem next_anchor {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i : ℕ} (hi : i < S.card) :
    (point L S hS i + gap L S hS i) % L ∈ S := by
  have he : point L S hS i + gap L S hS i = point L S hS (i + 1) := by
    unfold gap
    exact Nat.add_sub_of_le (point_mono hS hSL (by omega))
  rw [he]
  exact WeightedCircularGap.next_anchor_mem hS hSL hi

/-- A gap exceeds `j` precisely when its next `j` positions are unselected. -/
theorem gap_tail_iff {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) {i j : ℕ} (hi : i < S.card) (hj : j < L) :
    j < gap L S hS i ↔ Disjoint S (arc L (point L S hS i + 1) j) := by
  have ha : point L S hS i < L := mem_range.mp (hSL (point_mem hS hi))
  constructor
  · intro hg
    apply disjoint_left.mpr
    intro z hz harc
    obtain ⟨t, ht, rfl⟩ := mem_image.mp harc
    have ht' := mem_range.mp ht
    have hd : forward L (point L S hS i) ((point L S hS i + 1 + t) % L) = 1 + t := by
      simpa [Nat.add_assoc] using WeightedCircularGap.forward_mod_add ha (show 1 + t < L by omega)
    rcases anchor_offset_zero_or_gap_le hS hSL hi hz with h | h <;> omega
  · intro hd
    by_contra hg
    have hp := gap_pos hS hSL hi
    have hnext := next_anchor hS hSL hi
    apply disjoint_left.mp hd hnext
    refine mem_image.mpr ⟨gap L S hS i - 1, mem_range.mpr (by omega), ?_⟩
    congr 1
    omega

theorem sum_odd (n : ℕ) : (∑ j ∈ range n, (2 * (j : ℝ) + 1)) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Sum a function over the actual sorted anchors. -/
theorem sum_points {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (f : ℕ → ℝ) :
    (∑ i ∈ range S.card, f (point L S hS i)) = ∑ a ∈ S, f a := by
  apply sum_bij (fun i _ => point L S hS i)
  · exact fun i hi => point_mem hS (mem_range.mp hi)
  · intro i hi j hj he
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := point_strict hS hSL hlt hj'.le
      omega
    · have := point_strict hS hSL hlt hi'.le
      omega
  · intro a ha
    obtain ⟨i, hi, he⟩ := exists_point_eq hS ha
    exact ⟨i, mem_range.mpr hi, he⟩
  · intros; rfl

/-- The squared-gap sum is a weighted count of empty forward arcs. -/
theorem sum_gap_sq_eq_tails {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) :
    (∑ i ∈ range S.card, (gap L S hS i : ℝ) ^ 2) =
      ∑ a ∈ S, ∑ j ∈ range L,
        if Disjoint S (arc L (a + 1) j) then (2 * (j : ℝ) + 1) else 0 := by
  rw [← sum_points hS hSL]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [← sum_odd]
  have he : (range L).filter (fun j => j < gap L S hS i) = range (gap L S hS i) := by
    ext j
    simp only [mem_filter, mem_range]
    have hg := gap_le hS hSL hi'
    omega
  rw [← he, sum_filter]
  apply sum_congr rfl
  intro j hj
  simp only [gap_tail_iff hS hSL hi' (mem_range.mp hj)]

/-- Squared actual circular gaps; the empty set contributes zero. -/
def squareGapSum (L : ℕ) (S : Finset ℕ) : ℝ :=
  if hS : S.Nonempty then ∑ i ∈ range S.card, (gap L S hS i : ℝ) ^ 2 else 0

theorem squareGapSum_eq_tails {L : ℕ} {S : Finset ℕ} (hSL : S ⊆ range L) :
    squareGapSum L S = ∑ a ∈ S, ∑ j ∈ range L,
      if Disjoint S (arc L (a + 1) j) then (2 * (j : ℝ) + 1) else 0 := by
  by_cases hS : S.Nonempty
  · simpa only [squareGapSum, dite_eq_left hS] using sum_gap_sq_eq_tails hS hSL
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp [squareGapSum, he]

/-- The existing normalized point-gap area, extended by zero at the empty set. -/
def pointGapArea (L : ℕ) (S : Finset ℕ) : ℝ := squareGapSum L S / (2 * (L : ℝ) ^ 2)

theorem pointGapArea_eq {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) :
    pointGapArea L S = GapErosion.pointArea (range S.card) (gap L S hS) L := by
  simp only [pointGapArea, squareGapSum, dite_eq_left hS, GapErosion.pointArea]

end
end LeanMachine.CyclicSelection
