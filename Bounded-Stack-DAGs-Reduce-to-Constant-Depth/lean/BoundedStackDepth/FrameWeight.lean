import BoundedStackDepth.FrameDynamics
import BoundedStackDepth.BandSums

/-!
# Frame weight (Lemma W1, generic part)

Every time `t < T` lies in exactly one *segment*: its innermost frame together with that frame's current
segment start (`segOf`). A segment's *maximum* (`segMax`) is the largest distance from its home over its
own times, and its weight is `2 ^ band segMax`.

* `sup_add_one_le_card` (the staircase): if a function vanishes at the first element of a finite set and
  grows by at most one from some earlier element, its maximum is at most the size of the set minus one.
* `sum_segWeight_le`: if every segment's maximum is less than its number of own times, the weights of all
  segments sum to at most `T`. For the frames of Theorem A this holds because own times step by one level
  and every segment starts at its home (the concrete part of Lemma W1).
-/

namespace BoundedStackDepth

open Finset

/-- **The staircase.** If `f` vanishes at the least element of `A` and every other element is at most one
above some earlier element, then `max_A f + 1 ≤ |A|`. -/
theorem sup_add_one_le_card {A : Finset ℕ} (f : ℕ → ℕ) (hA : A.Nonempty) (h0 : f (A.min' hA) = 0)
    (hstep : ∀ t ∈ A, t ≠ A.min' hA → ∃ t' ∈ A, t' < t ∧ f t ≤ f t' + 1) : A.sup f + 1 ≤ A.card := by
  have key : ∀ t ∈ A, f t ≤ (A.filter (· < t)).card := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      by_cases hmin : t = A.min' hA
      · rw [hmin, h0]; exact Nat.zero_le _
      · obtain ⟨t', ht', hlt, hf⟩ := hstep t ht hmin
        have h1 := ih t' hlt ht'
        have h2 : (A.filter (· < t')).card + 1 ≤ (A.filter (· < t)).card := by
          rw [← card_insert_of_notMem (s := A.filter (· < t')) (a := t') (by simp)]
          refine card_le_card fun s hs => ?_
          rcases mem_insert.mp hs with rfl | hs
          · exact mem_filter.mpr ⟨ht', hlt⟩
          · obtain ⟨h3, h4⟩ := mem_filter.mp hs
            exact mem_filter.mpr ⟨h3, h4.trans hlt⟩
        omega
  have : ∀ t ∈ A, f t + 1 ≤ A.card := fun t ht => by
    have h1 := key t ht
    have h2 : (A.filter (· < t)).card < A.card :=
      card_lt_card ⟨filter_subset _ _, fun hs => by simpa using (mem_filter.mp (hs ht)).2⟩
    omega
  obtain ⟨t, ht, he⟩ := exists_mem_eq_sup A hA f
  rw [he]
  exact this t ht

namespace FrameSystem

variable (S : FrameSystem)

/-- The segment of a time: its innermost frame and that frame's current segment start. -/
noncomputable def segOf (t : ℕ) : (ℕ × ℕ) × ℕ := (S.inner t, S.segStart (S.inner t) t)

/-- The segments that have own times. -/
noncomputable def segments : Finset ((ℕ × ℕ) × ℕ) := (range S.T).image S.segOf

/-- The own times of a segment. -/
noncomputable def segTimes (σ : (ℕ × ℕ) × ℕ) : Finset ℕ := (range S.T).filter (S.segOf · = σ)

/-- The maximum of a segment: the largest distance from its home over its own times. -/
noncomputable def segMax (σ : (ℕ × ℕ) × ℕ) : ℕ :=
  (S.segTimes σ).sup fun t => (S.x t - S.x σ.2).natAbs

/-- **Frame weight (Lemma W1, generic part).** If every segment's maximum is less than its number of own times, the
weights `2 ^ band segMax` of all segments sum to at most `T`. -/
theorem sum_segWeight_le (h : ∀ σ ∈ S.segments, S.segMax σ + 1 ≤ (S.segTimes σ).card) :
    ∑ σ ∈ S.segments, 2 ^ band (S.segMax σ) ≤ S.T := by
  calc ∑ σ ∈ S.segments, 2 ^ band (S.segMax σ)
      ≤ ∑ σ ∈ S.segments, (S.segTimes σ).card := sum_le_sum fun σ hσ => by
        have h1 := h σ hσ
        rcases Nat.eq_zero_or_pos (S.segMax σ) with h0 | hpos
        · rw [h0]; simp only [band_zero, pow_zero]; omega
        · have := pow_band_le hpos.ne'
          omega
    _ = (range S.T).card := (card_eq_sum_card_fiberwise (fun t _ => mem_image_of_mem _ ‹_›)).symm
    _ = S.T := card_range _

end FrameSystem

end BoundedStackDepth
