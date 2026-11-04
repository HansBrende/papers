import BoundedStackDepth.Entries
import BoundedStackDepth.DisplayView

/-!
# The composed display of all virtual heads

`n` virtual heads, each with its frame system `S v`, share one grid offset `r`. At each time `t` they
define one display (`Display.lean`):
* the entries are the frames of all heads (`EntryIdx`); an entry on its head's stack at `t` has the window
  `[entryBot, entryTop]`, every other frame the empty window `[top + 1, top]` (`dispBot`, `dispTop`);
* the seeds are the band groups of all heads (`seeds`).

`oneCandidate_disp`: the candidate property holds at every time, so Lemma D (`card_shownSet_tail`)
applies with `n` heads and at most `n` seeds.
-/

namespace BoundedStackDepth

open Finset FrameSystem

variable {n : ℕ} (S : Fin n → FrameSystem) (h₀ r : ℕ)

/-- The entries of all heads: a head and one of its frames. -/
abbrev EntryIdx := Σ v : Fin n, {F // F ∈ (S v).frames}

open Classical in
/-- The window bottom at `t`: the current maximum for an entry on its stack, above the top otherwise. -/
noncomputable def dispBot (t : ℕ) (e : EntryIdx S) : ℕ :=
  if (S e.1).IsEntry e.2.1 ∧ Contains e.2.1 t then (S e.1).entryBot h₀ r e.2.1 t
  else (S e.1).entryTop h₀ r e.2.1 + 1

/-- The window top: the entry's top. -/
noncomputable def dispTop (e : EntryIdx S) : ℕ := (S e.1).entryTop h₀ r e.2.1

/-- The seeds at `t`: the band groups of all heads. -/
noncomputable def seeds (t : ℕ) : Finset ℕ := univ.image fun v => (S v).headGroup h₀ r t

theorem card_seeds_le (t : ℕ) : (seeds S h₀ r t).card ≤ n :=
  card_image_le.trans (by simp)

/-- An entry on its head's stack has its current window. -/
theorem dispBot_of_onStack {t : ℕ} {e : EntryIdx S} (h : (S e.1).IsEntry e.2.1 ∧ Contains e.2.1 t) :
    dispBot S h₀ r t e = (S e.1).entryBot h₀ r e.2.1 t := by
  unfold dispBot
  simp only [h, and_self, ↓reduceIte]

/-- An entry with a candidate window at `t` is an entry on its head's stack. -/
theorem onStack_of_cand {t y : ℕ} {e : EntryIdx S} (h1 : dispBot S h₀ r t e ≤ y)
    (h2 : y < dispTop S h₀ r e) : (S e.1).IsEntry e.2.1 ∧ Contains e.2.1 t := by
  by_contra h
  unfold dispBot at h1
  simp only [h, ↓reduceIte] at h1
  unfold dispTop at h2
  omega

/-- **The candidate property of the composed display.** -/
theorem oneCandidate_disp (t : ℕ) :
    OneCandidate (fun e : EntryIdx S => e.1) (dispBot S h₀ r t) (dispTop S h₀ r) := by
  rintro v y ⟨v₁, F, hF⟩ ⟨v₂, F', hF'⟩ h1 h2 hb ht hb' ht'
  simp only at h1 h2
  obtain rfl : v₁ = v₂ := h1.trans h2.symm
  have hs := onStack_of_cand S h₀ r hb ht
  have hs' := onStack_of_cand S h₀ r hb' ht'
  rw [dispBot_of_onStack S h₀ r hs] at hb
  rw [dispBot_of_onStack S h₀ r hs'] at hb'
  have := entry_candidate_unique hs.1 hs'.1 hs.2 hs'.2 hb ht hb' ht'
  subst this
  rfl

end BoundedStackDepth
