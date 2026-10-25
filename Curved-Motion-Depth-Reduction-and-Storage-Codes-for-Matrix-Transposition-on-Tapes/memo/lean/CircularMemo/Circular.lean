import CircularMemo.Elimination
import MotionDepthCodes.CircularClique

/-! # All circular ratios below three

The interleaved order on the three independent intervals of an Andrásfai
graph supplies the elimination hypothesis. The existing Bondy–Hell map
then transfers the result to every circular clique below ratio three.
-/

namespace CircularMemo

open Finset MotionDepthCodes

def interleavedOrder (k : ℕ) (v : Fin (3 * k - 1)) : ℕ :=
  if v.val < k then 3 * v.val
  else if v.val < 2 * k then 3 * (v.val - k) + 1
  else 3 * (v.val - 2 * k) + 2

theorem neighbor_order {k : ℕ} (hk : 2 ≤ k) {v w : Fin (3 * k - 1)}
    (hadj : (circularClique (3 * k - 1) k).Adj v w) :
    interleavedOrder k w < interleavedOrder k v ∨
      (v.val < k ∧ k ≤ w.val ∧ w.val < 2 * k) ∨
      (k ≤ v.val ∧ v.val < 2 * k ∧ 2 * k ≤ w.val) ∨
      (2 * k ≤ v.val ∧ w.val < k) := by
  have hv := v.isLt
  have hw := w.isLt
  have hne := SimpleGraph.ne_of_adj _ hadj
  have hn : v.val ≠ w.val := fun e => hne (Fin.ext e)
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · rw [circularClique_adj_of_lt hlt] at hadj
    unfold interleavedOrder
    split_ifs <;> omega
  · have ha := hadj.symm
    rw [circularClique_adj_of_lt hgt] at ha
    unfold interleavedOrder
    split_ifs <;> omega

/-- Every Andrásfai graph has the weighted polymatroid half bound. -/
theorem rateBound_andrasfai (k : ℕ) (hk : 2 ≤ k) :
    RateBound (nbhd (circularClique (3 * k - 1) k)) (1 / 2) := by
  intro h hh hv
  let A : Finset (Fin (3 * k - 1)) := univ.filter (fun v => v.val < k)
  let B : Finset (Fin (3 * k - 1)) :=
    univ.filter (fun v => k ≤ v.val ∧ v.val < 2 * k)
  let C : Finset (Fin (3 * k - 1)) := univ.filter (fun v => 2 * k ≤ v.val)
  have he : 2 * h univ ≤ h A + h B + h C := by
    apply three_part_elimination hh A B C
    intro S hS
    have hex : Set.Nonempty {v : Fin (3 * k - 1) | v ∉ S} := by
      by_contra! hempty
      apply hS
      apply eq_univ_of_forall
      intro v
      by_contra hvS
      have hm : v ∈ ({v : Fin (3 * k - 1) | v ∉ S} : Set _) := hvS
      rw [hempty] at hm
      exact hm
    obtain ⟨v, hvS, hmin⟩ := Set.exists_min_image {v | v ∉ S}
      (interleavedOrder k) (Set.toFinite _) hex
    have hn (w : Fin (3 * k - 1))
        (hw : w ∈ nbhd (circularClique (3 * k - 1) k) v) (hwS : w ∉ S) :
        (v.val < k ∧ k ≤ w.val ∧ w.val < 2 * k) ∨
        (k ≤ v.val ∧ v.val < 2 * k ∧ 2 * k ≤ w.val) ∨
        (2 * k ≤ v.val ∧ w.val < k) := by
      have ha : (circularClique (3 * k - 1) k).Adj v w := by
        simpa only [nbhd, mem_filter, mem_univ, true_and] using hw
      exact (neighbor_order hk ha).resolve_left (not_lt_of_ge (hmin w hwS))
    refine ⟨v, hvS, ?_⟩
    by_cases ha : v.val < k
    · left
      refine ⟨by simp [A, ha], hh.insert_eq_of_subset (B := S ∪ B) ?_ (hv v)⟩
      intro w hw
      by_cases hwS : w ∈ S
      · exact mem_union_left B hwS
      · apply mem_union_right
        have ht := hn w hw hwS
        simp only [B, mem_filter, mem_univ, true_and]
        omega
    · by_cases hb : v.val < 2 * k
      · right; left
        refine ⟨by simp [B]; omega,
          hh.insert_eq_of_subset (B := S ∪ C) ?_ (hv v)⟩
        intro w hw
        by_cases hwS : w ∈ S
        · exact mem_union_left C hwS
        · apply mem_union_right
          have ht := hn w hw hwS
          simp only [C, mem_filter, mem_univ, true_and]
          omega
      · right; right
        refine ⟨by simp [C]; omega,
          hh.insert_eq_of_subset (B := S ∪ A) ?_ (hv v)⟩
        intro w hw
        by_cases hwS : w ∈ S
        · exact mem_union_left A hwS
        · apply mem_union_right
          have ht := hn w hw hwS
          simp only [A, mem_filter, mem_univ, true_and]
          omega
  have hs : (∑ v ∈ A, h {v}) + (∑ v ∈ B, h {v}) + (∑ v ∈ C, h {v}) =
      ∑ v, h {v} := by
    simp only [A, B, C, sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases ha : v.val < k
    · have hb : ¬ (k ≤ v.val ∧ v.val < 2 * k) := by omega
      have hc : ¬ 2 * k ≤ v.val := by omega
      simp [ha, hb, hc]
    · by_cases hb : v.val < 2 * k
      · have hc : ¬ 2 * k ≤ v.val := by omega
        simp [ha, hb, hc, show k ≤ v.val by omega]
      · simp [ha, hb, show 2 * k ≤ v.val by omega]
  have hA := hh.le_sum_singleton A
  have hB := hh.le_sum_singleton B
  have hC := hh.le_sum_singleton C
  linarith

/-- This strictly extends the earlier `p * 5 ≤ 14 * q` range. -/
theorem rateBound_circularClique_lt_three {p q : ℕ} (hq : 0 < q) (hpq : p < 3 * q) :
    RateBound (nbhd (circularClique p q)) (1 / 2) := by
  let k := q + 1
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hn : 0 < 3 * k - 1 := by omega
  have hineq : p * k ≤ (3 * k - 1) * q := by
    have he : 3 * k - 1 + 1 = 3 * k := by omega
    dsimp [k] at *
    nlinarith
  exact RateBound.of_graphHom (by norm_num)
    (circularCliqueHom p q (3 * k - 1) k hn (by omega) hineq)
    (rateBound_andrasfai k hk)

/-- The new range also applies to every graph mapping to such a target. -/
theorem rateBound_of_circularHom {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {p q : ℕ}
    (hq : 0 < q) (hpq : p < 3 * q) (φ : G →g circularClique p q) :
    RateBound (nbhd G) (1 / 2) :=
  RateBound.of_graphHom (by norm_num) φ (rateBound_circularClique_lt_three hq hpq)

/-- The exact earlier range, including its degenerate denominator-zero
case, is a corollary of the new family theorem. -/
theorem rateBound_circularClique_oldRange {p q : ℕ} (h : p * 5 ≤ 14 * q) :
    RateBound (nbhd (circularClique p q)) (1 / 2) := by
  by_cases hq : 0 < q
  · exact rateBound_circularClique_lt_three hq (by nlinarith)
  · have hp : p = 0 := by nlinarith
    subst p
    intro g hg _
    simp [hg.empty]

end CircularMemo
