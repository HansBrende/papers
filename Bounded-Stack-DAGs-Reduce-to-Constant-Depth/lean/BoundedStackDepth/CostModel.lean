import BoundedStackDepth.Grid

/-!
# The cost model of Theorem A (step 1)

A hop is described by six numbers: the bands `bp`, `bu` at its ends, the scale `σ` of its owner, the band
`lS` of the largest distance `S` from its cell to a home active on it, the largest scale `pm` of a frame
or segment start inside it (`pushmax`), and whether it is *frame-micro* (`fm`: the segment of `u` started
at or before `p`). For a grid offset `r` it is
* *aligned* (`Aligned`) if both ends have the same group `d`, it is home-near (`S < 2^{θ(d+1)+2}`, i.e.
  `lS < θ(d+1) + 2`), and it is eventful (not frame-micro, or `σ ≥ θ(d)`, or `pm ≥ θ(d)`);
* *ground* (`Ground`) if `G(σ) = 0`;
* *lost* if neither.

`card_lost_le`: at most `min(c, σ)` of the `h₀` offsets lose the hop, where `c` (`hopCost`) is the band
change plus the home deficit plus the eventfulness deficit. Each term is one counting lemma of
`Grid.lean`. `hopCost_le_of_bands` is the per-hop estimate used along a ladder.
-/

namespace BoundedStackDepth

open Finset

variable {h₀ : ℕ}

/-- The hop is aligned at offset `r`. -/
def Aligned (h₀ r bp bu σ lS pm : ℕ) (fm : Prop) : Prop :=
  grp h₀ r bp = grp h₀ r bu ∧ lS < flr h₀ r (grp h₀ r bu + 1) + 2 ∧
    (¬ fm ∨ flr h₀ r (grp h₀ r bu) ≤ σ ∨ flr h₀ r (grp h₀ r bu) ≤ pm)

/-- The hop is ground at offset `r`: its owner's scale is in group `0`. -/
def Ground (h₀ r σ : ℕ) : Prop := grp h₀ r σ = 0

instance (h₀ r bp bu σ lS pm : ℕ) (fm : Prop) [Decidable fm] :
    Decidable (Aligned h₀ r bp bu σ lS pm fm) := by
  unfold Aligned; infer_instance

instance (h₀ r σ : ℕ) : Decidable (Ground h₀ r σ) := by unfold Ground; infer_instance

/-- The cost of a hop: band change, home deficit and (if frame-micro) eventfulness deficit. -/
def hopCost (bp bu σ lS pm : ℕ) (fm : Prop) [Decidable fm] : ℕ :=
  (max bp bu - min bp bu) + (lS - 2 - max bp bu) + if fm then bu - max σ pm else 0

/-- **The cost model.** At most `min(c, σ)` offsets lose a hop. -/
theorem card_lost_le (bp bu σ lS pm : ℕ) (fm : Prop) [Decidable fm] :
    ((range h₀).filter (fun r => ¬ Aligned h₀ r bp bu σ lS pm fm ∧ ¬ Ground h₀ r σ)).card ≤
      min (hopCost bp bu σ lS pm fm) σ := by
  refine le_min ?_ ?_
  · -- union bound over the three ways to fail alignment
    have hgrp : ∀ r, grp h₀ r bp = grp h₀ r bu → grp h₀ r bu = grp h₀ r (max bp bu) := fun r h => by
      rcases le_total bp bu with hb | hb
      · rw [max_eq_right hb]
      · rw [max_eq_left hb, h]
    calc ((range h₀).filter (fun r => ¬ Aligned h₀ r bp bu σ lS pm fm ∧ ¬ Ground h₀ r σ)).card
        ≤ ((range h₀).filter (fun r => grp h₀ r (min bp bu) ≠ grp h₀ r (max bp bu)) ∪
            (range h₀).filter (fun r => flr h₀ r (grp h₀ r (max bp bu) + 1) ≤ lS - 2) ∪
            (if fm then (range h₀).filter (fun r => max σ pm < flr h₀ r (grp h₀ r bu)) else ∅)).card := by
          refine card_le_card fun r hr => ?_
          obtain ⟨hr0, hna, -⟩ := mem_filter.mp hr
          simp only [Aligned, not_and_or, not_or, not_le, not_lt] at hna
          simp only [mem_union, mem_filter]
          by_cases hg : grp h₀ r bp = grp h₀ r bu
          · rcases hna with h | h | h
            · exact absurd hg h
            · exact Or.inl (Or.inr ⟨hr0, by rw [← hgrp r hg]; omega⟩)
            · obtain ⟨hfm, h1, h2⟩ := h
              right
              simp only [not_not.mp hfm, ↓reduceIte]
              exact mem_filter.mpr ⟨hr0, max_lt h1 h2⟩
          · left; left
            refine ⟨hr0, fun he => hg ?_⟩
            rcases le_total bp bu with hb | hb
            · rw [min_eq_left hb, max_eq_right hb] at he; exact he
            · rw [min_eq_right hb, max_eq_left hb] at he; exact he.symm
      _ ≤ (max bp bu - min bp bu) + (lS - 2 - max bp bu) + (if fm then bu - max σ pm else 0) := by
          refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
            (Nat.add_le_add (card_grp_ne_le (min_le_max)) (card_flr_grp_succ_le _ _))) ?_)
          split_ifs
          · exact card_lt_flr_grp_le _ _
          · simp
  · exact (card_le_card fun r hr => mem_filter.mpr ⟨(mem_filter.mp hr).1, by
      have := (mem_filter.mp hr).2.2; unfold Ground at this; omega⟩).trans (card_one_le_grp_le σ)

/-- **The per-hop estimate along a ladder.** With both bands and the home band at most `B`, and no
eventfulness deficit, the cost is at most `B − min(bp, bu)`. -/
theorem hopCost_le_of_bands {bp bu σ lS pm B : ℕ} {fm : Prop} [Decidable fm] (hp : bp ≤ B)
    (hu : bu ≤ B) (hS : lS ≤ B) (hev : fm → bu ≤ max σ pm) :
    hopCost bp bu σ lS pm fm ≤ B - min bp bu := by
  unfold hopCost
  have h0 : (if fm then bu - max σ pm else 0) = 0 := by
    split_ifs with h
    · exact Nat.sub_eq_zero_of_le (hev h)
    · rfl
  rw [h0]
  rcases le_total bp bu with hb | hb
  · rw [max_eq_right hb, min_eq_left hb]; omega
  · rw [max_eq_left hb, min_eq_right hb]; omega

end BoundedStackDepth
