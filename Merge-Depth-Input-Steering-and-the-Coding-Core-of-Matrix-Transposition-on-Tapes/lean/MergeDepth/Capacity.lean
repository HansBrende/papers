import MergeDepth.ColdGenie

/-!
# The number of deep cells (Proposition 3.17)

The deep cells are the eighth paper's `heavyPairs xs T V`, the pairs `(h, c)` such that head `h`
enters cell `c` more than `V` times, and the deep hops are the long hops outside its `lightHops`.

* `card_deep_mul_le`: `|R| (V + 1) ≤ kT` (the eighth paper's `card_heavyPairs_mul_le`).
* `card_deepHops_le`: `N_R ≤ kT`.
* `two_mul_card_deepHops_le`: `2 N_R ≤ |R| (T - 1)`: the long hops of one head at one cell end in
  disjoint intervals `(p, u]` of length at least two inside `[1, T - 1]`.
* `card_deep_le_of_lt`: if `|R| (T - 1) < 2kT` and `T > 2k + 1`, then `|R| ≤ 2k`.
-/

namespace MergeDepth

open Finset BoundedNesting

variable {k : ℕ}

/-- The deep hops: long hops outside the light hops. -/
def deepHops (xs : Fin k → ℕ → ℤ) (T V : ℕ) : Finset (Fin k × ℕ × ℕ) :=
  allHops xs T \ lightHops xs T V

theorem card_deep_mul_le (xs : Fin k → ℕ → ℤ) (T V : ℕ) :
    (heavyPairs xs T V).card * (V + 1) ≤ k * T :=
  card_heavyPairs_mul_le xs T V

theorem card_deepHops_le (xs : Fin k → ℕ → ℤ) (T V : ℕ) : (deepHops xs T V).card ≤ k * T :=
  (card_le_card sdiff_subset).trans (card_allHops_le xs T)

/-- The long hops of one head at one cell end in disjoint intervals of length at least two. -/
theorem two_mul_card_hopsAt_le (x : ℕ → ℤ) (T : ℕ) (c : ℤ) :
    2 * ((hops x T).filter fun e => x e.1 = c).card ≤ T - 1 := by
  classical
  set S := (hops x T).filter fun e => x e.1 = c
  -- the intervals `(p, u]` are disjoint subsets of `[1, T - 1]`
  have hdisj : (S : Set (ℕ × ℕ)).PairwiseDisjoint fun e => Ioc e.1 e.2 := by
    intro e he e' he' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro τ h1 h2
    obtain ⟨hh, hc⟩ := mem_filter.mp he
    obtain ⟨hh', hc'⟩ := mem_filter.mp he'
    obtain ⟨hp, hu⟩ := hop_unique (mem_hops.mp hh) (mem_hops.mp hh') (hc.trans hc'.symm)
      (mem_Ioc.mp h1) (mem_Ioc.mp h2)
    exact hne (Prod.ext hp hu)
  have hsub : S.biUnion (fun e => Ioc e.1 e.2) ⊆ Icc 1 (T - 1) := by
    intro τ hτ
    obtain ⟨e, he, hτ⟩ := mem_biUnion.mp hτ
    have := mem_hops.mp (mem_filter.mp he).1
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hτ
    exact mem_Icc.mpr ⟨by omega, by have := this.2.1; omega⟩
  have hcard := card_le_card hsub
  rw [card_biUnion hdisj, Nat.card_Icc] at hcard
  calc 2 * S.card = ∑ _e ∈ S, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ S, (Ioc e.1 e.2).card := by
        refine sum_le_sum fun e he => ?_
        have := (mem_hops.mp (mem_filter.mp he).1).1
        rw [Nat.card_Ioc]
        omega
    _ ≤ T - 1 := by omega

/-- **`2 N_R ≤ |R| (T - 1)`.** -/
theorem two_mul_card_deepHops_le (xs : Fin k → ℕ → ℤ) (T V : ℕ) :
    2 * (deepHops xs T V).card ≤ (heavyPairs xs T V).card * (T - 1) := by
  classical
  -- every deep hop is a hop of its head at a heavy pair
  have hsub : deepHops xs T V ⊆ (heavyPairs xs T V).biUnion fun hc =>
      ((hops (xs hc.1) T).filter fun e => xs hc.1 e.1 = hc.2).image fun e => (hc.1, e) := by
    intro η hη
    obtain ⟨hA, hL⟩ := mem_sdiff.mp hη
    have hheavy : (η.1, xs η.1 η.2.1) ∈ heavyPairs xs T V := by
      by_contra hn
      exact hL (mem_filter.mpr ⟨hA, hn⟩)
    refine mem_biUnion.mpr ⟨_, hheavy, mem_image.mpr ⟨η.2, mem_filter.mpr ⟨?_, rfl⟩, rfl⟩⟩
    exact mem_hops.mpr (mem_allHops.mp hA)
  calc 2 * (deepHops xs T V).card
      ≤ 2 * ((heavyPairs xs T V).biUnion fun hc =>
          ((hops (xs hc.1) T).filter fun e => xs hc.1 e.1 = hc.2).image fun e => (hc.1, e)).card :=
        Nat.mul_le_mul_left _ (card_le_card hsub)
    _ ≤ 2 * ∑ hc ∈ heavyPairs xs T V,
          (((hops (xs hc.1) T).filter fun e => xs hc.1 e.1 = hc.2).image fun e => (hc.1, e)).card :=
        Nat.mul_le_mul_left _ card_biUnion_le
    _ ≤ 2 * ∑ hc ∈ heavyPairs xs T V, ((hops (xs hc.1) T).filter fun e => xs hc.1 e.1 = hc.2).card :=
        Nat.mul_le_mul_left _ (sum_le_sum fun _ _ => card_image_le)
    _ = ∑ hc ∈ heavyPairs xs T V, 2 * ((hops (xs hc.1) T).filter fun e => xs hc.1 e.1 = hc.2).card := by
        rw [mul_sum]
    _ ≤ ∑ _hc ∈ heavyPairs xs T V, (T - 1) :=
        sum_le_sum fun hc _ => two_mul_card_hopsAt_le (xs hc.1) T hc.2
    _ = (heavyPairs xs T V).card * (T - 1) := by rw [sum_const, smul_eq_mul]

/-- The bound `|R| (T - 1)/2` beats `kT` only for at most `2k` deep cells. -/
theorem card_deep_le_of_lt {R T : ℕ} (hT : 2 * k + 1 < T) (h : R * (T - 1) < 2 * k * T) :
    R ≤ 2 * k := by
  by_contra hR
  push Not at hR
  have : (2 * k + 1) * (T - 1) ≤ R * (T - 1) := Nat.mul_le_mul_right _ hR
  have h2 : (2 * k + 1) * (T - 1) = 2 * k * T + (T - 1) - 2 * k := by
    zify [show 1 ≤ T by omega, show 2 * k ≤ 2 * k * T + (T - 1) by nlinarith]
    ring
  omega

end MergeDepth
