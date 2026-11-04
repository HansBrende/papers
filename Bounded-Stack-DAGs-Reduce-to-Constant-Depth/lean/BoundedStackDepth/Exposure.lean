import BoundedStackDepth.Composition
import BoundedStackDepth.ViewInvariance
import BoundedStackDepth.DisplayTail

/-!
# Exposure: the composed display

The composed display's view above `d` is the union of the heads' views (`mem_aboveVals_iff`,
`mem_visPairs_iff`). So equal head views at two times give equal composed views (`views_eq`), and if
every candidate at `d` is displayed at both times, the shown sets agree above `d`
(`views_eq` with `shown_above_eq`).

`card_exposed_le`: when `d` is a seed at both times and the head views agree, the shown sets above `d`
differ only if a candidate at `d` is broken; there are at most `n` candidates per time (one per head), so
at most `2n Q^{|ι|−1}` bit vectors expose the hop.
-/

namespace BoundedStackDepth

open Finset FrameSystem

variable {n : ℕ} (S : Fin n → FrameSystem) (h₀ r : ℕ)

/-- The composed values above `d` are the union of the heads' views. -/
theorem mem_aboveVals_iff {t d y : ℕ} :
    y ∈ aboveVals (dispBot S h₀ r t) (dispTop S h₀ r) (seeds S h₀ r t) d ↔
      ∃ v, y ∈ (S v).headAbove h₀ r d t := by
  classical
  simp only [aboveVals, mem_union, mem_filter, mem_image, mem_univ, true_and, seeds, mem_headAbove]
  constructor
  · rintro (⟨⟨v, rfl⟩, hy⟩ | ⟨e, ⟨hb, ht⟩, rfl⟩)
    · exact ⟨v, hy, Or.inl rfl⟩
    · obtain ⟨hE, hc⟩ := onStack_of_cand S h₀ r hb ht
      rw [dispBot_of_onStack S h₀ r ⟨hE, hc⟩] at hb
      exact ⟨e.1, ht, Or.inr ⟨e.2.1, hE, hc, hb, ht, rfl⟩⟩
  · rintro ⟨v, hy, h | ⟨F, hE, hc, hb, hlt, rfl⟩⟩
    · exact Or.inl ⟨⟨v, h.symm⟩, hy⟩
    · refine Or.inr ⟨⟨v, F, hE.1⟩, ⟨?_, hlt⟩, rfl⟩
      rw [dispBot_of_onStack S h₀ r ⟨hE, hc⟩]
      exact hb

/-- The composed visible windows are those of the heads' visible entries. -/
theorem mem_visPairs_iff {t d : ℕ} {unb : EntryIdx S → Prop} {b c : ℕ} :
    (b, c) ∈ visPairs (dispBot S h₀ r t) (dispTop S h₀ r) unb d ↔
      ∃ e : EntryIdx S, unb e ∧ (e.2.1, b) ∈ (S e.1).headVisible h₀ r d t ∧
        (S e.1).entryTop h₀ r e.2.1 = c := by
  classical
  simp only [visPairs, mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq, mem_headVisible]
  constructor
  · rintro ⟨e, ⟨hd, hle, hu⟩, rfl, rfl⟩
    have hs : (S e.1).IsEntry e.2.1 ∧ Contains e.2.1 t := by
      by_contra h
      unfold dispBot at hle
      simp only [h, ↓reduceIte] at hle
      unfold dispTop at hle
      omega
    rw [dispBot_of_onStack S h₀ r hs] at hd hle ⊢
    exact ⟨e, hu, ⟨hs.1, hs.2, hd, hle, rfl⟩, rfl⟩
  · rintro ⟨e, hu, ⟨hE, hc, hd, hle, rfl⟩, rfl⟩
    refine ⟨e, ⟨?_, ?_, hu⟩, ?_, rfl⟩ <;> rw [dispBot_of_onStack S h₀ r ⟨hE, hc⟩] <;> first
      | exact hd | exact hle

/-- Equal head views give equal composed views. -/
theorem views_eq {p u d : ℕ} (unb : EntryIdx S → Prop)
    (h : ∀ v, (S v).headAbove h₀ r d p = (S v).headAbove h₀ r d u ∧
      (S v).headVisible h₀ r d p = (S v).headVisible h₀ r d u) :
    aboveVals (dispBot S h₀ r p) (dispTop S h₀ r) (seeds S h₀ r p) d =
        aboveVals (dispBot S h₀ r u) (dispTop S h₀ r) (seeds S h₀ r u) d ∧
      visPairs (dispBot S h₀ r p) (dispTop S h₀ r) unb d =
        visPairs (dispBot S h₀ r u) (dispTop S h₀ r) unb d := by
  constructor
  · ext y
    rw [mem_aboveVals_iff, mem_aboveVals_iff]
    exact exists_congr fun v => by rw [(h v).1]
  · ext ⟨b, c⟩
    rw [mem_visPairs_iff, mem_visPairs_iff]
    exact exists_congr fun e => by rw [(h e.1).2]

/-- **Exposure.** If `d` is a seed at `p` and `u` and the head views above `d` agree, then the shown sets
above `d` differ only if some candidate at `d`, at `p` or at `u`, is broken. -/
theorem exposed_of_ne {Q : ℕ} [NeZero Q] (ξ : EntryIdx S → Fin Q) {p u d : ℕ}
    (hdp : d ∈ seeds S h₀ r p) (hdu : d ∈ seeds S h₀ r u)
    (hv : ∀ v, (S v).headAbove h₀ r d p = (S v).headAbove h₀ r d u ∧
      (S v).headVisible h₀ r d p = (S v).headVisible h₀ r d u)
    (hne : (shownSet (dispBot S h₀ r p) (dispTop S h₀ r) (fun e => ξ e ≠ 0) (seeds S h₀ r p)).filter
        (d < ·) ≠
      (shownSet (dispBot S h₀ r u) (dispTop S h₀ r) (fun e => ξ e ≠ 0) (seeds S h₀ r u)).filter
        (d < ·)) :
    ∃ e ∈ cands (dispBot S h₀ r p) (dispTop S h₀ r) d ∪ cands (dispBot S h₀ r u) (dispTop S h₀ r) d,
      ξ e = 0 := by
  classical
  by_contra hall
  push Not at hall
  have hc : ∀ t, d ∈ seeds S h₀ r t → (∀ e ∈ cands (dispBot S h₀ r t) (dispTop S h₀ r) d, ξ e ≠ 0) →
      ∀ e, dispBot S h₀ r t e ≤ d → d < dispTop S h₀ r e →
        Disp (dispBot S h₀ r t) (dispTop S h₀ r) (fun e => ξ e ≠ 0) (seeds S h₀ r t) e :=
    fun t hd hb e h1 h2 =>
      disp_of_cand h1 h2 (Or.inr ⟨hb e (mem_cands.mpr ⟨h1, h2⟩),
        hd⟩)
  have hcp := hc p hdp fun e he => hall e (mem_union_left _ he)
  have hcu := hc u hdu fun e he => hall e (mem_union_right _ he)
  obtain ⟨hX, hV⟩ := views_eq S h₀ r (fun e => ξ e ≠ 0) hv
  exact hne (shown_above_eq hcp hcu hX hV)

/-- **Exposure, counted.** At most `2n Q^{|ι|−1}` bit vectors make the shown sets above a seed `d` differ
at two times with equal head views. -/
theorem card_exposed_le {Q : ℕ} [NeZero Q] {p u d : ℕ}
    (hdp : d ∈ seeds S h₀ r p) (hdu : d ∈ seeds S h₀ r u)
    (hv : ∀ v, (S v).headAbove h₀ r d p = (S v).headAbove h₀ r d u ∧
      (S v).headVisible h₀ r d p = (S v).headVisible h₀ r d u) :
    (univ.filter fun ξ : EntryIdx S → Fin Q =>
      (shownSet (dispBot S h₀ r p) (dispTop S h₀ r) (fun e => ξ e ≠ 0) (seeds S h₀ r p)).filter
          (d < ·) ≠
        (shownSet (dispBot S h₀ r u) (dispTop S h₀ r) (fun e => ξ e ≠ 0) (seeds S h₀ r u)).filter
          (d < ·)).card ≤ 2 * n * Q ^ (Fintype.card (EntryIdx S) - 1) := by
  classical
  calc _ ≤ (univ.filter fun ξ : EntryIdx S → Fin Q =>
          ∃ e ∈ cands (dispBot S h₀ r p) (dispTop S h₀ r) d ∪
          cands (dispBot S h₀ r u) (dispTop S h₀ r) d, ξ e = 0).card :=
        card_le_card fun ξ hξ => mem_filter.mpr ⟨mem_univ _,
          exposed_of_ne S h₀ r ξ hdp hdu hv (mem_filter.mp hξ).2⟩
    _ ≤ (cands (dispBot S h₀ r p) (dispTop S h₀ r) d ∪
          cands (dispBot S h₀ r u) (dispTop S h₀ r) d).card * Q ^ (Fintype.card (EntryIdx S) - 1) :=
        card_some_broken_le _
    _ ≤ 2 * n * Q ^ (Fintype.card (EntryIdx S) - 1) := by
        refine Nat.mul_le_mul_right _ ((card_union_le _ _).trans ?_)
        have := card_cands_le (oneCandidate_disp S h₀ r p) d
        have := card_cands_le (oneCandidate_disp S h₀ r u) d
        omega

end BoundedStackDepth
