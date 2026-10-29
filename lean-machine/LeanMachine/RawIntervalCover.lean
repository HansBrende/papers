import LeanMachine.ShiftedGridUnion
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! Minimum closed-real-interval covers of finite natural coordinates.
An interval of length at most one grid width costs at most two blocks,
uniformly in the shift. Empty sets and overlapping covers are included. -/

namespace LeanMachine

open Classical Finset
open scoped BigOperators
noncomputable section

namespace ShiftedGrid

/-- A set of diameter at most one width meets at most two blocks. -/
theorem blockUnion_card_le_of_span {L w : ℕ} (hw : 0 < w) (θ : ℕ)
    (S : Finset ℕ) (hspan : ∀ a ∈ S, ∀ b ∈ S, b ≤ a + w) :
    (blockUnion L w θ S).card ≤ 2 * w := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hlabels : label w θ (S.max' hS) ≤ label w θ (S.min' hS) + 1 := by
    calc
      _ ≤ label w θ (S.min' hS + w) :=
        label_mono w θ (hspan _ (S.min'_mem hS) _ (S.max'_mem hS))
      _ = _ := by simp only [label, Nat.add_right_comm _ w θ, Nat.add_div_right _ hw]
  have hsub : blockUnion L w θ S ⊆ blockUnion L w θ {S.min' hS, S.max' hS} := by
    intro z hz
    obtain ⟨y, hy, he⟩ := mem_blockUnion.mp hz
    have hl := label_mono w θ (S.min'_le _ hy)
    have hu := label_mono w θ (S.le_max' _ hy)
    have hcases : label w θ y = label w θ (S.min' hS) ∨
        label w θ y = label w θ (S.max' hS) := by omega
    rcases hcases with h | h
    · exact mem_blockUnion.mpr ⟨_, by simp, he.trans h⟩
    · exact mem_blockUnion.mpr ⟨_, by simp, he.trans h⟩
  have hcard : ({S.min' hS, S.max' hS} : Finset ℕ).card ≤ 2 := by
    simpa using card_insert_le (S.min' hS) {S.max' hS}
  exact (card_le_card hsub).trans
    (((blockUnion_card_le hw θ _).trans (min_le_right ..)).trans
      ((Nat.mul_le_mul_left w hcard).trans_eq (Nat.mul_comm w 2)))

end ShiftedGrid

namespace RawIntervalCover

/-- The intervals may overlap and their endpoints need not be integers. -/
def Covers (S : Finset ℕ) (r : ℝ) (I : Finset (ℝ × ℝ)) : Prop :=
  (∀ p ∈ I, p.1 ≤ p.2 ∧ p.2 - p.1 ≤ r) ∧
    ∀ y ∈ S, ∃ p ∈ I, p.1 ≤ y ∧ (y : ℝ) ≤ p.2

theorem Covers.mono_radius {S : Finset ℕ} {r s : ℝ} {I : Finset (ℝ × ℝ)}
    (h : Covers S r I) (hrs : r ≤ s) : Covers S s I :=
  ⟨fun p hp => ⟨(h.1 p hp).1, (h.1 p hp).2.trans hrs⟩, h.2⟩

theorem exists_cover (S : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ n : ℕ, ∃ I : Finset (ℝ × ℝ), Covers S r I ∧ I.card ≤ n := by
  refine ⟨S.card, S.image (fun y : ℕ => ((y : ℝ), (y : ℝ))), ⟨?_, ?_⟩, card_image_le⟩
  · intro p hp
    obtain ⟨y, _, rfl⟩ := mem_image.mp hp
    exact ⟨le_rfl, by simpa using hr⟩
  · intro y hy
    exact ⟨_, mem_image_of_mem _ hy, le_rfl, le_rfl⟩

/-- Minimum cardinality of a closed interval cover with length at most
`max r 0`. For nonnegative `r`, this is exactly the usual covering number. -/
def number (S : Finset ℕ) (r : ℝ) : ℕ :=
  Nat.find (exists_cover S (le_max_right r 0))

theorem number_le {S : Finset ℕ} {r : ℝ} {I : Finset (ℝ × ℝ)}
    (h : Covers S r I) : number S r ≤ I.card :=
  Nat.find_min' _ ⟨I, h.mono_radius (le_max_left r 0), le_rfl⟩

/-- A minimum is attained; no compactness or optimizer is assumed. -/
theorem exists_min_cover (S : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ I : Finset (ℝ × ℝ), Covers S r I ∧ I.card = number S r := by
  obtain ⟨I, hI, hc⟩ := Nat.find_spec (exists_cover S (le_max_right r 0))
  rw [max_eq_left hr] at hI
  exact ⟨I, hI, hc.antisymm (number_le hI)⟩

@[simp] theorem number_empty (r : ℝ) : number ∅ r = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact number_le (I := ∅) (by simp [Covers])

/-- Every interval costs at most two full blocks, at every shift. -/
theorem blockUnion_card_le_of_cover {L w : ℕ} (hw : 0 < w) (θ : ℕ)
    {S : Finset ℕ} {r : ℝ} {I : Finset (ℝ × ℝ)}
    (h : Covers S r I) (hrw : r ≤ w) :
    (ShiftedGrid.blockUnion L w θ S).card ≤ min L (2 * w * I.card) := by
  let C := fun p : ℝ × ℝ => S.filter fun y : ℕ => p.1 ≤ (y : ℝ) ∧ (y : ℝ) ≤ p.2
  have hsub : ShiftedGrid.blockUnion L w θ S ⊆
      I.biUnion (fun p => ShiftedGrid.blockUnion L w θ (C p)) := by
    intro z hz
    obtain ⟨y, hy, he⟩ := ShiftedGrid.mem_blockUnion.mp hz
    obtain ⟨p, hp, hlo, hhi⟩ := h.2 y hy
    exact mem_biUnion.mpr ⟨p, hp, ShiftedGrid.mem_blockUnion.mpr
      ⟨y, mem_filter.mpr ⟨hy, hlo, hhi⟩, he⟩⟩
  apply le_min (by simpa using card_le_univ (s := ShiftedGrid.blockUnion L w θ S))
  calc
    _ ≤ ∑ p ∈ I, (ShiftedGrid.blockUnion L w θ (C p)).card :=
      (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _p ∈ I, 2 * w := by
      apply sum_le_sum
      intro p hp
      apply ShiftedGrid.blockUnion_card_le_of_span hw θ
      intro a ha b hb
      have ha' := (mem_filter.mp ha).2
      have hb' := (mem_filter.mp hb).2
      have hlen := (h.1 p hp).2.trans hrw
      exact_mod_cast (show (b : ℝ) ≤ (a : ℝ) + w by linarith)
    _ = _ := by simp [Nat.mul_comm]

theorem blockUnion_card_le {L w : ℕ} (hw : 0 < w) (θ : ℕ)
    (S : Finset ℕ) {r : ℝ} (hr : 0 ≤ r) (hrw : r ≤ w) :
    (ShiftedGrid.blockUnion L w θ S).card ≤ min L (2 * w * number S r) := by
  obtain ⟨I, hI, hc⟩ := exists_min_cover S hr
  simpa only [hc] using blockUnion_card_le_of_cover hw θ hI hrw

/-- One interval can require two blocks, even for two adjacent raw bits. -/
theorem two_block_factor_sharp :
    Covers {0, 1} 1 {(0, 1)} ∧ (ShiftedGrid.blockUnion 2 1 0 {0, 1}).card = 2 := by
  constructor
  · norm_num [Covers]
  · decide

end RawIntervalCover
end
end LeanMachine
