import LeanMachine.CyclicSelection
import LeanMachine.GapErosion

set_option autoImplicit false

/-!
# Segment windows and the point area of dense anchor sets

Two elementary bounds for the gap-area memo.

* `window_cover`: a chain `α 0, α 1, …, α N` whose segments carry windows of
  width `w s` that all meet `S`, with every two consecutive widths summing to
  at most `G`, has every window of width `G` inside `[α 0, α N]` meeting `S`.
* `pointArea_le_of_dense`: an anchor set on the circle of length `L` that
  contains `L - 1` and meets every window `[u, u + g]` inside `[0, X]` has
  frozen point area at most
  `((g + 1) L + (L - X + g + 1) ^ 2 + (g + 1) ^ 2) / (2 L ^ 2)`.
  The sharper form `pointArea_le_of_dense'` drops the last summand.
-/

namespace SourceCovers.GapBound

open Finset LeanMachine LeanMachine.CyclicSelection
open scoped BigOperators

/-! ## Segment windows -/

/-- A point at or above `α 0` and below `α m` lies in a segment
`[α s, α (s + 1))` with `s < m`. No monotonicity of `α` is needed. -/
theorem exists_segment {α : ℕ → ℕ} {z : ℕ} (h0 : α 0 ≤ z) :
    ∀ m, z < α m → ∃ s < m, α s ≤ z ∧ z < α (s + 1) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    by_cases hm : z < α m
    · obtain ⟨s, hs, h1, h2⟩ := ih hm
      exact ⟨s, by omega, h1, h2⟩
    · exact ⟨m, by omega, by omega, h⟩

/-- Theorem 1 (segment windows). Windows of width `w s` inside the segment
`[α s, α (s + 1)]` meet `S`; two consecutive widths sum to at most `G`. Then
every window of width `G` inside `[α 0, α N]` meets `S`. -/
theorem window_cover {α w : ℕ → ℕ} {N G : ℕ} {S : Set ℕ}
    (hα : ∀ s < N, α s + w s ≤ α (s + 1))
    (hseg : ∀ s < N, ∀ z, α s ≤ z → z + w s ≤ α (s + 1) → ∃ u ∈ S, z ≤ u ∧ u ≤ z + w s)
    (hG : ∀ s < N, w s ≤ G) (hG2 : ∀ s, s + 1 < N → w s + w (s + 1) ≤ G) (hG1 : 1 ≤ G) :
    ∀ z, α 0 ≤ z → z + G ≤ α N → ∃ u ∈ S, z ≤ u ∧ u ≤ z + G := by
  intro z hz0 hzN
  obtain ⟨s, hsN, hs1, hs2⟩ := exists_segment hz0 N (by omega)
  have hws := hG s hsN
  by_cases hfit : z + w s ≤ α (s + 1)
  · -- The window `[z, z + w s]` fits in segment `s`.
    obtain ⟨u, hu, hu1, hu2⟩ := hseg s hsN z hs1 hfit
    exact ⟨u, hu, hu1, by omega⟩
  · -- It sticks out of segment `s`, so segment `s + 1` exists and its first
    -- window lies inside `(z, z + G]`.
    have hs1N : s + 1 < N := by
      by_contra hcon
      have hsN' : s + 1 = N := by omega
      rw [hsN'] at hfit
      omega
    obtain ⟨u, hu, hu1, hu2⟩ := hseg (s + 1) hs1N (α (s + 1)) le_rfl (hα (s + 1) hs1N)
    have h2 := hG2 s hs1N
    exact ⟨u, hu, by omega, by omega⟩

/-! ## Point area of a dense anchor set -/

/-- The anchor positions clipped to `[T, L - 1]`; it telescopes the far gaps. -/
noncomputable def clip (L T : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (i : ℕ) : ℕ :=
  max (min (point L S hS i) (L - 1)) T

theorem clip_mono {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L) (T : ℕ) :
    Monotone (clip L T S hS) := by
  intro i j hij
  have := point_mono hS hSL hij
  unfold clip
  omega

/-- If `L - 1` is an anchor, it is the last one. -/
theorem point_last {L : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hL1 : L - 1 ∈ S) : point L S hS (S.card - 1) = L - 1 := by
  obtain ⟨k, hk, hkp⟩ := exists_point_eq (L := L) hS hL1
  have hmono := point_mono hS hSL (show k ≤ S.card - 1 by omega)
  have hmem := mem_range.mp
    (hSL (point_mem (L := L) hS (show S.card - 1 < S.card by omega)))
  omega

/-- Every gap is either short (at most `g + 1`) or a far gap: at most
`L - X + g + 1` and equal to the increment of the clipped profile. -/
theorem gap_cases {L X g : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hL1 : L - 1 ∈ S) (hgX : g ≤ X)
    (hdense : ∀ u, u + g ≤ X → ∃ s ∈ S, u ≤ s ∧ s ≤ u + g)
    {i : ℕ} (hi : i < S.card) :
    gap L S hS i ≤ g + 1 ∨
      (gap L S hS i ≤ L - X + g + 1 ∧
        gap L S hS i = clip L (X - g) S hS (i + 1) - clip L (X - g) S hS i) := by
  have hab := point_strict hS hSL (Nat.lt_succ_self i) (show i + 1 ≤ S.card by omega)
  unfold gap clip
  by_cases hlast : i + 1 = S.card
  · -- The wraparound gap: from `L - 1` to `L + min S`, and `min S ≤ g`.
    left
    obtain ⟨s, hs, -, hs2⟩ := hdense 0 (by omega)
    have hmin := S.min'_le s hs
    have e1 : point L S hS (i + 1) = L + S.min' hS := by
      rw [hlast]
      exact point_card L S hS
    have e2 : point L S hS i = L - 1 := by
      have h := point_last hS hSL hL1
      rwa [show S.card - 1 = i by omega] at h
    omega
  · have hb : point L S hS (i + 1) < L :=
      mem_range.mp (hSL (point_mem (L := L) hS (show i + 1 < S.card by omega)))
    by_cases hnear : point L S hS i + 1 + g ≤ X
    · -- A window just after `point i` contains the next anchor.
      left
      obtain ⟨s, hs, hs1, hs2⟩ := hdense (point L S hS i + 1) hnear
      obtain ⟨k, hk, hks⟩ := exists_point_eq (L := L) hS hs
      have hik : i + 1 ≤ k := by
        by_contra hcon
        have := point_mono hS hSL (show k ≤ i by omega)
        omega
      have := point_mono hS hSL hik
      omega
    · -- A far gap lies inside `[X - g, L - 1]`.
      right
      constructor <;> omega

theorem gap_sq_le {L X g : ℕ} {S : Finset ℕ} (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hL1 : L - 1 ∈ S) (hgX : g ≤ X)
    (hdense : ∀ u, u + g ≤ X → ∃ s ∈ S, u ≤ s ∧ s ≤ u + g)
    {i : ℕ} (hi : i < S.card) :
    gap L S hS i ^ 2 ≤ (g + 1) * gap L S hS i +
      (L - X + g + 1) * (clip L (X - g) S hS (i + 1) - clip L (X - g) S hS i) := by
  rcases gap_cases hS hSL hL1 hgX hdense hi with h | ⟨h1, h2⟩
  · calc gap L S hS i ^ 2 = gap L S hS i * gap L S hS i := sq _
      _ ≤ (g + 1) * gap L S hS i := Nat.mul_le_mul h le_rfl
      _ ≤ _ := Nat.le_add_right _ _
  · calc gap L S hS i ^ 2 = gap L S hS i * gap L S hS i := sq _
      _ ≤ (L - X + g + 1) * gap L S hS i := Nat.mul_le_mul h1 le_rfl
      _ = (L - X + g + 1) * (clip L (X - g) S hS (i + 1) - clip L (X - g) S hS i) := by
          rw [← h2]
      _ ≤ _ := Nat.le_add_left _ _

/-- The squared gaps of a dense anchor set, in `ℕ`. -/
theorem sum_gap_sq_le {L X g : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (hL1 : L - 1 ∈ S) (hgX : g ≤ X)
    (hdense : ∀ u, u + g ≤ X → ∃ s ∈ S, u ≤ s ∧ s ≤ u + g) :
    ∑ i ∈ range S.card, gap L S hS i ^ 2 ≤ (g + 1) * L + (L - X + g + 1) ^ 2 := by
  have hterm : ∀ i ∈ range S.card, gap L S hS i ^ 2 ≤ (g + 1) * gap L S hS i +
      (L - X + g + 1) * (clip L (X - g) S hS (i + 1) - clip L (X - g) S hS i) :=
    fun i hi => gap_sq_le hS hSL hL1 hgX hdense (mem_range.mp hi)
  have htel := sum_range_tsub (clip_mono hS hSL (X - g)) S.card
  have hend : clip L (X - g) S hS S.card - clip L (X - g) S hS 0 ≤ L - X + g + 1 := by
    have hc := point_card L S hS
    unfold clip
    rw [hc]
    omega
  calc ∑ i ∈ range S.card, gap L S hS i ^ 2
      ≤ ∑ i ∈ range S.card, ((g + 1) * gap L S hS i +
          (L - X + g + 1) * (clip L (X - g) S hS (i + 1) - clip L (X - g) S hS i)) :=
        sum_le_sum hterm
    _ = (g + 1) * L + (L - X + g + 1) *
          (clip L (X - g) S hS S.card - clip L (X - g) S hS 0) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_gap hS hSL, htel]
    _ ≤ (g + 1) * L + (L - X + g + 1) * (L - X + g + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul le_rfl hend) _
    _ = (g + 1) * L + (L - X + g + 1) ^ 2 := by rw [sq]

/-- Sharper form of Theorem 2, without the summand `(g + 1) ^ 2`. The hypothesis
`X ≤ L` is not needed. -/
theorem pointArea_le_of_dense' {L X g : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (hL1 : L - 1 ∈ S) (hgX : g ≤ X)
    (hdense : ∀ u, u + g ≤ X → ∃ s ∈ S, u ≤ s ∧ s ≤ u + g) :
    GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L ≤
      (((g + 1) * L + (L - X + g + 1) ^ 2 : ℕ) : ℝ) / (2 * (L : ℝ) ^ 2) := by
  unfold GapErosion.pointArea
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast sum_gap_sq_le hS hSL hL1 hgX hdense

/-- Theorem 2 (point area from density). -/
theorem pointArea_le_of_dense {L X g : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L) (hL1 : L - 1 ∈ S) (hgX : g ≤ X) (hXL : X ≤ L)
    (hdense : ∀ u, u + g ≤ X → ∃ s ∈ S, u ≤ s ∧ s ≤ u + g) :
    GapErosion.pointArea (range S.card) (CyclicSelection.gap L S hS) L ≤
      (((g + 1) * L + (L - X + g + 1) ^ 2 + (g + 1) ^ 2 : ℕ) : ℝ) / (2 * (L : ℝ) ^ 2) := by
  -- `hXL` is kept for the requested shape; `pointArea_le_of_dense'` does without it.
  have _hXL := hXL
  refine (pointArea_le_of_dense' hS hSL hL1 hgX hdense).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.le_add_right _ _

end SourceCovers.GapBound
