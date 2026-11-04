import BoundedStackDepth.Global
import BoundedStackDepth.DisplayTail

/-!
# Truncated hops (TRUNC, with Lemma D)

A violated hop whose deciding group has rank at least `P` at its start is *truncated*; its start is then a
*bad* time, with more than `P` shown groups (`topRank_lt_card`). Distinct hops of one head have distinct
starts, so a head has at most as many truncated hops as there are bad times (`card_trunc_le_bad`).

`card_bad_le` (Lemma D for the composed display): at each time, if `P ≥ 1 + 2n(jn + 1)` for the `n = 2k`
heads, at most `2n(1 − Q^{−n²})^j` of all bit vectors make the time bad.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} {T : ℕ} (hx : ∀ i, IsWalk (xs i)) {h₀ : ℕ} {Q : ℕ} [NeZero Q]

/-- The bad times: more than `P` shown groups. -/
noncomputable def badTimes (P r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) : Finset ℕ :=
  (range T).filter fun t => P < (shown T hx h₀ r ξ t).card

/-- A head has at most as many truncated hops as there are bad times. -/
theorem card_trunc_le_bad (v : Fin (k * 2)) (P r : ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    ((upperHops (headWalk xs v) T).filter fun e =>
      P ≤ topRank (shown T hx h₀ r ξ e.1) (decGroup (headFrames T hx v) h₀ r e)).card ≤
      (badTimes hx (h₀ := h₀) P r ξ).card := by
  refine card_le_card_of_injOn (fun e => e.1) (fun e he => ?_) fun e he e' he' h => ?_
  · obtain ⟨heU, hP⟩ := mem_filter.mp (Finset.mem_coe.mp he)
    have hh := isHop_of_mem_upperHops heU
    have hlt := topRank_lt_card (decGroup_mem_shown hx (h₀ := h₀) v r ξ e).1
    have h1 := hh.1
    have h2 := hh.2.1
    simp only [Finset.mem_coe, badTimes, mem_filter, mem_range]
    exact ⟨by omega, by omega⟩
  · have hh := isHop_of_mem_upperHops (mem_filter.mp (Finset.mem_coe.mp he)).1
    have hh' := isHop_of_mem_upperHops (mem_filter.mp (Finset.mem_coe.mp he')).1
    simp only at h
    exact Prod.ext h (hop_start_unique hh (h ▸ hh'))

/-- **Lemma D for the composed display.** If `P ≥ 1 + 2n(jn + 1)` (`n = 2k` heads), at most
`2n(1 − Q^{−n²})^j Q^{|ι|}` bit vectors make a given time bad. -/
theorem card_bad_le (P r j t : ℕ) (hP : 1 + (k * 2 + k * 2) * (j * (k * 2) + 1) ≤ P) :
    ((univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
      P < (shown T hx h₀ r ξ t).card).card : ℝ) ≤
      (k * 2 + k * 2 : ℕ) * (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j *
        (Q : ℝ) ^ Fintype.card (EntryIdx (headFrames T hx)) := by
  classical
  have hs := card_seeds_le (headFrames T hx) h₀ r t
  have htail := card_shownSet_tail (Q := Q) (card_cands_le (oneCandidate_disp (headFrames T hx) h₀ r t))
    (seeds (headFrames T hx) h₀ r t) j
  have hsub : (univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
      P < (shown T hx h₀ r ξ t).card) ⊆ univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
      1 + ((seeds (headFrames T hx) h₀ r t).card + k * 2) * (j * (k * 2) + 1) <
        (shownSet (dispBot (headFrames T hx) h₀ r t) (dispTop (headFrames T hx) h₀ r)
          (fun e => ξ e ≠ 0) (seeds (headFrames T hx) h₀ r t)).card := by
    intro ξ hξ
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have h1 := (mem_filter.mp hξ).2
    unfold shown at h1
    have h2 : ((seeds (headFrames T hx) h₀ r t).card + k * 2) * (j * (k * 2) + 1) ≤
        (k * 2 + k * 2) * (j * (k * 2) + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hle : ((seeds (headFrames T hx) h₀ r t).card : ℝ) + ((k * 2 : ℕ) : ℝ) ≤
      ((k * 2 + k * 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (seeds (headFrames T hx) h₀ r t).card + k * 2 ≤ k * 2 + k * 2)
  have hQ : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)
  have hX : (0 : ℝ) ≤ (1 - ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹) ^ j := by
    refine pow_nonneg ?_ _
    have : ((Q : ℝ) ^ (k * 2 * (k * 2)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hQ)
    linarith
  have hY : (0 : ℝ) ≤ (Q : ℝ) ^ Fintype.card (EntryIdx (headFrames T hx)) :=
    pow_nonneg (Nat.cast_nonneg _) _
  calc ((univ.filter fun ξ : EntryIdx (headFrames T hx) → Fin Q =>
        P < (shown T hx h₀ r ξ t).card).card : ℝ)
      ≤ _ := by exact_mod_cast card_le_card hsub
    _ ≤ _ := htail
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hX) hY

end BoundedStackDepth
