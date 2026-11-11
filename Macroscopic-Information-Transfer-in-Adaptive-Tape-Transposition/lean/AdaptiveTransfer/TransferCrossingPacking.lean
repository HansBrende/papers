import NativeRelations.MacroscopicSkeleton
import Mathlib

/-! Exact finite packing of long consecutive revisits at fixed cells. This
is the target-guard budget in crossing transport, with the U-1 horizon and
strict excursion threshold preserved.
-/

namespace AdaptiveTransfer.TransferCrossing
open Finset BoundedNesting NativeRelations MergeDepth
open scoped BigOperators

theorem long_hop_span {y : ℕ → ℤ} (hy : IsWalk y) {U H p u : ℕ}
    (hh : IsHop y U p u) (he : HasHopExcursionGTAt y (2 * H) p u) :
    4 * H + 2 ≤ u - p := by
  obtain ⟨r, hr, hex⟩ := he
  obtain ⟨hpr, hru⟩ := mem_Ioo.mp hr
  have hleft := hy.lip hpr.le
  have hright := hy.lip hru.le
  rw [hh.2.2.1] at hright
  have ha : |y r - y p| ≤ ((r - p : ℕ) : ℤ) := abs_le.mpr (by omega)
  have hb : |y r - y p| ≤ ((u - r : ℕ) : ℤ) := abs_le.mpr (by omega)
  push_cast at hex
  omega

noncomputable def longHopLowersAt (y : ℕ → ℤ) (U H : ℕ) (z : ℤ) : Finset ℕ := by
  classical
  exact (range U).filter fun p => y p = z ∧
    ∃ u, IsHop y U p u ∧ HasHopExcursionGTAt y (2 * H) p u

/-- At one cell, the spans of its long consecutive revisits are disjoint;
each uses at least 4H+2 transitions before the last vertex U-1. -/
theorem longHopLowersAt_card_le {y : ℕ → ℤ} (hy : IsWalk y) (U H : ℕ) (z : ℤ) :
    (longHopLowersAt y U H z).card ≤ (U - 1) / (4 * H + 2) := by
  classical
  let S := longHopLowersAt y U H z
  have spec (p : S) : y p.val = z ∧ ∃ u, IsHop y U p.val u ∧
      HasHopExcursionGTAt y (2 * H) p.val u := (mem_filter.mp p.property).2
  let finish (p : S) : ℕ := (spec p).2.choose
  have hhop (p : S) : IsHop y U p.val (finish p) := (spec p).2.choose_spec.1
  have hlong (p : S) : 4 * H + 2 ≤ finish p - p.val :=
    long_hop_span hy (hhop p) (spec p).2.choose_spec.2
  have hdis : ((univ : Finset S) : Set S).PairwiseDisjoint (fun p => Ioc p.val (finish p)) := by
    intro p _ p' _ hne
    apply disjoint_left.mpr
    intro r hr hr'
    have he := hop_unique (hhop p) (hhop p') ((spec p).1.trans (spec p').1.symm)
      (mem_Ioc.mp hr) (mem_Ioc.mp hr')
    exact hne (Subtype.ext he.1)
  have hsub : (univ.biUnion fun p : S => Ioc p.val (finish p)) ⊆ Ioc 0 (U - 1) := by
    intro r hr
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hr
    have hh : finish p < U := (hhop p).2.1
    have ht := mem_Ioc.mp hp
    exact mem_Ioc.mpr (by omega)
  have hsum : ∑ p : S, (finish p - p.val) ≤ U - 1 := by
    have hc := card_le_card hsub
    rw [card_biUnion hdis] at hc
    simpa only [Nat.card_Ioc, Nat.sub_zero] using hc
  have htotal : S.card * (4 * H + 2) ≤ U - 1 := by
    calc
      _ = ∑ _p : S, (4 * H + 2) := by simp
      _ ≤ ∑ p : S, (finish p - p.val) := sum_le_sum (fun p _ => hlong p)
      _ ≤ _ := hsum
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 4 * H + 2)).mpr htotal

noncomputable def longHopLowersBand (y : ℕ → ℤ) (U H R : ℕ) (z : ℤ) : Finset ℕ :=
  (Icc (z - R) (z + R)).biUnion fun a => longHopLowersAt y U H a

theorem longHopLowersBand_card_le {y : ℕ → ℤ} (hy : IsWalk y) (U H R : ℕ) (z : ℤ) :
    (longHopLowersBand y U H R z).card ≤ (2 * R + 1) * ((U - 1) / (4 * H + 2)) := by
  classical
  unfold longHopLowersBand
  apply (card_biUnion_le).trans
  calc
    _ ≤ ∑ _a ∈ Icc (z - (R : ℤ)) (z + R), (U - 1) / (4 * H + 2) :=
      sum_le_sum (fun a _ => longHopLowersAt_card_le hy U H a)
    _ = _ := by simp [Int.card_Icc]; omega

/-- The literal target guard: a long-hop lower endpoint is charged when its
cell is at distance at most R+1 from some original cut-head position. -/
noncomputable def crossingTargetGuard {k : ℕ} (ys xs : Fin k → ℕ → ℤ)
    (U H R : ℕ) (B : Finset ℕ) : Finset ℕ :=
  univ.biUnion fun h => B.biUnion fun c => longHopLowersBand (ys h) U H (R + 1) (xs h c)

theorem crossingTargetGuard_live {k U H R v : ℕ} {ys xs : Fin k → ℕ → ℤ}
    {B : Finset ℕ} (hv : v ∈ crossingTargetGuard ys xs U H R B) : v < U := by
  classical
  obtain ⟨h, _, hh⟩ := mem_biUnion.mp hv
  obtain ⟨c, _, hc⟩ := mem_biUnion.mp hh
  obtain ⟨a, _, ha⟩ := mem_biUnion.mp hc
  exact mem_range.mp (mem_filter.mp ha).1

theorem crossingTargetGuard_card_le {k : ℕ} {ys xs : Fin k → ℕ → ℤ}
    (hy : ∀ h, IsWalk (ys h)) (U H R : ℕ) (B : Finset ℕ) :
    (crossingTargetGuard ys xs U H R B).card ≤
      k * (2 * R + 3) * ((U - 1) / (4 * H + 2)) * B.card := by
  classical
  unfold crossingTargetGuard
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _h : Fin k, B.card * ((2 * (R + 1) + 1) * ((U - 1) / (4 * H + 2))) := by
      apply sum_le_sum
      intro h _
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _c ∈ B, (2 * (R + 1) + 1) * ((U - 1) / (4 * H + 2)) :=
          sum_le_sum (fun c _ => longHopLowersBand_card_le (hy h) U H (R + 1) (xs h c))
        _ = _ := by simp
    _ = _ := by simp; ring

theorem mem_crossingTargetGuard_of_close {k : ℕ} {ys xs : Fin k → ℕ → ℤ}
    {U H R p u c : ℕ} {B : Finset ℕ} (h : Fin k) (hc : c ∈ B)
    (hh : IsHop (ys h) U p u) (he : HasHopExcursionGTAt (ys h) (2 * H) p u)
    (hclose : |ys h p - xs h c| ≤ (R : ℤ) + 1) :
    p ∈ crossingTargetGuard ys xs U H R B := by
  classical
  apply mem_biUnion.mpr ⟨h, mem_univ _, ?_⟩
  apply mem_biUnion.mpr ⟨c, hc, ?_⟩
  apply mem_biUnion.mpr ⟨ys h p, ?_, ?_⟩
  · have hc' := abs_le.mp hclose
    apply mem_Icc.mpr
    push_cast
    omega
  · apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, rfl, u, hh, he⟩
    have hp := hh.1
    have hu := hh.2.1
    omega

theorem crossingTargetGuard_card_three_scale {k : ℕ} {ys xs : Fin k → ℕ → ℤ}
    (hy : ∀ h, IsWalk (ys h)) (U H s : ℕ) (B : Finset ℕ) :
    (crossingTargetGuard ys xs U H (3 * s) B).card ≤
      k * (6 * s + 3) * ((U - 1) / (4 * H + 2)) * B.card := by
  convert crossingTargetGuard_card_le hy U H (3 * s) B using 1
  ring

end AdaptiveTransfer.TransferCrossing
