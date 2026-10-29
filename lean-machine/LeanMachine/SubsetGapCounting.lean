import LeanMachine.CyclicGapTails
import Mathlib.Data.Finset.Powerset

/-! Exact counting of the empty forward arcs in uniform fixed-size subsets. -/

namespace LeanMachine.CyclicSelection

open Finset
open scoped BigOperators Classical
noncomputable section

theorem card_subsets_containing_avoiding {α : Type*} [DecidableEq α]
    (U B : Finset α) (a : α) {k : ℕ} (hBU : B ⊆ U)
    (haU : a ∈ U) (haB : a ∉ B) (hk : 0 < k) :
    ((U.powersetCard k).filter fun S => a ∈ S ∧ Disjoint S B).card =
      (U.card - B.card - 1).choose (k - 1) := by
  have he : (U.powersetCard k).filter (fun S => a ∈ S ∧ Disjoint S B) =
      ((U \ B).powersetCard k).filter ({a} ⊆ ·) := by
    ext S
    simp only [mem_filter, mem_powersetCard, singleton_subset_iff]
    constructor
    · rintro ⟨⟨hSU, hcard⟩, haS, hd⟩
      refine ⟨⟨?_, hcard⟩, haS⟩
      exact fun x hx => mem_sdiff.mpr ⟨hSU hx, disjoint_left.mp hd hx⟩
    · rintro ⟨⟨hS, hcard⟩, haS⟩
      refine ⟨⟨hS.trans sdiff_subset, hcard⟩, haS, disjoint_left.mpr ?_⟩
      exact fun x hx => (mem_sdiff.mp (hS hx)).2
  rw [he, card_filter_powersetCard_subset {a} (U \ B) k
    (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨haU, haB⟩)) (by simpa using Nat.succ_le_of_lt hk),
    card_sdiff_of_subset hBU, card_singleton]

theorem card_gap_tails {L k a j : ℕ} (ha : a < L) (hj : j < L) (hk : 0 < k) :
    (((range L).powersetCard k).filter fun S =>
      a ∈ S ∧ Disjoint S (arc L (a + 1) j)).card = (L - 1 - j).choose (k - 1) := by
  have hL : 0 < L := by omega
  rw [card_subsets_containing_avoiding _ _ _ (arc_subset hL)
    (mem_range.mpr ha) (self_not_mem_forward_arc ha hj) hk,
    card_range, arc_card hj.le]
  congr 1
  omega

/-- Hockey-stick sum with a zero-padded initial segment. -/
theorem sum_range_choose_fixed (N r : ℕ) :
    (∑ q ∈ range N, q.choose r) = N.choose (r + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Nat.choose_succ_succ]; exact Nat.add_comm _ _

/-- Weighted reversed hockey-stick identity, including boundary cases. -/
theorem sum_odd_choose (N r : ℕ) :
    (∑ j ∈ range N, (2 * (j : ℝ) + 1) * (N - 1 - j).choose r) =
      N.choose (r + 1) + 2 * (N.choose (r + 2) : ℝ) := by
  have hsum (n : ℕ) : (∑ q ∈ range n, (q.choose r : ℝ)) = n.choose (r + 1) := by
    exact_mod_cast sum_range_choose_fixed n r
  have hw (n : ℕ) :
      (∑ q ∈ range n, (2 * ((n : ℝ) - 1 - q) + 1) * q.choose r) =
        n.choose (r + 1) + 2 * (n.choose (r + 2) : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have he : (∑ q ∈ range n, (2 * ((n + 1 : ℕ) - 1 - (q : ℝ)) + 1) * q.choose r) =
          (∑ q ∈ range n, (2 * ((n : ℝ) - 1 - q) + 1) * q.choose r) +
            2 * ∑ q ∈ range n, (q.choose r : ℝ) := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intros
        push_cast
        ring
      rw [he, ih, hsum, Nat.choose_succ_succ n r, Nat.choose_succ_succ n (r + 1)]
      push_cast
      ring
  rw [← hw, ← sum_range_reflect (fun j => (2 * (j : ℝ) + 1) * (N - 1 - j).choose r) N]
  apply sum_congr rfl
  intro q hq
  have hq' := mem_range.mp hq
  have he : N - 1 - (N - 1 - q) = q := by omega
  rw [he, Nat.cast_sub (show q ≤ N - 1 by omega), Nat.cast_sub (show 1 ≤ N by omega)]
  norm_num

/-- Exact unnormalized second moment over all fixed-size circle subsets. -/
theorem sum_squareGapSum {N k : ℕ} (hk : 0 < k) :
    (∑ S ∈ (range N).powersetCard k, squareGapSum N S) =
      N * ((N.choose k : ℝ) + 2 * N.choose (k + 1)) := by
  let P := (range N).powersetCard k
  have hsum : (∑ S ∈ P, squareGapSum N S) =
      ∑ S ∈ P, ∑ a ∈ range N, ∑ j ∈ range N,
        if a ∈ S ∧ Disjoint S (arc N (a + 1) j) then (2 * (j : ℝ) + 1) else 0 := by
    apply sum_congr rfl
    intro S hS
    have hSN := (mem_powersetCard.mp hS).1
    rw [squareGapSum_eq_tails hSN]
    calc
      _ = ∑ a ∈ S, ∑ j ∈ range N,
          if a ∈ S ∧ Disjoint S (arc N (a + 1) j) then (2 * (j : ℝ) + 1) else 0 := by
        apply sum_congr rfl
        intro a ha
        simp only [ha, true_and]
      _ = _ := sum_subset hSN (by intro a _ ha; simp [ha])
  rw [hsum, sum_comm]
  have ha : ∀ a ∈ range N,
      (∑ S ∈ P, ∑ j ∈ range N,
        if a ∈ S ∧ Disjoint S (arc N (a + 1) j) then (2 * (j : ℝ) + 1) else 0) =
      N.choose k + 2 * (N.choose (k + 1) : ℝ) := by
    intro a ha
    rw [sum_comm]
    calc
      _ = ∑ j ∈ range N, (2 * (j : ℝ) + 1) * (N - 1 - j).choose (k - 1) := by
        apply sum_congr rfl
        intro j hj
        rw [← sum_filter, sum_const, nsmul_eq_mul,
          card_gap_tails (mem_range.mp ha) (mem_range.mp hj) hk, mul_comm]
      _ = _ := by
        rw [sum_odd_choose]
        have hk₁ : k - 1 + 1 = k := by omega
        have hk₂ : k - 1 + 2 = k + 1 := by omega
        rw [hk₁, hk₂]
  simp only [sum_congr rfl ha, sum_const, card_range, nsmul_eq_mul]

/-- Exact mean point-gap area; singletons and the full set are also covered. -/
theorem mean_pointGapArea {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    (∑ S ∈ (range N).powersetCard k, pointGapArea N S) / N.choose k =
      (2 * (N : ℝ) - k + 1) / (2 * N * (k + 1)) := by
  have hN : 0 < N := hk.trans_le hkN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hF : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hkN
  have hc : (N.choose (k + 1) : ℝ) * (k + 1) = N.choose k * ((N : ℝ) - k) := by
    exact_mod_cast Nat.choose_succ_right_eq N k
  simp only [pointGapArea, ← sum_div]
  rw [sum_squareGapSum hk]
  field_simp
  nlinarith [hc]

end
end LeanMachine.CyclicSelection
