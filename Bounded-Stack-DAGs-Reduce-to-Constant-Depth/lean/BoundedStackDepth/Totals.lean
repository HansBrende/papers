import BoundedStackDepth.CutDescents
import BoundedStackDepth.FrameWeightU

/-!
# Totals over the random choices

The random choices are an offset `r < h₀`, digit offsets `ω ∈ [0, K)^P` and bits `ξ`; `Ω` is their
product. This file bounds the per-head event counts and the cut state edges summed over `Ω`.

* `card_upperHops_head_le`: a head has at most `T` upper hops.
* `sum_events_head_le`: summed over the offsets, a head's rises and last-stint ends number at most `8T`
  (the budget, `sum_stdWeight_le`, and frame weight, `sum_segWeight_upperFrames_le`).
* `card_events_head_le`: a head has at most `4T + 1` turning points and segment starts.
* `sum_descents_le`: the descents of the label, summed over `Ω`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} (T : ℕ) (hx : ∀ i, IsWalk (xs i)) {h₀ : ℕ}

include hx in
theorem card_upperHops_head_le (v : Fin (k * 2)) : (upperHops (headWalk xs v) T).card ≤ T := by
  have := card_upperHops_add_card_tops_le (isWalk_headWalk hx v) T
  omega

/-- Summed over the offsets, a head's rises and last-stint ends number at most `8T`. -/
theorem sum_events_head_le (v : Fin (k * 2)) :
    ∑ r ∈ range h₀, ((rises (headFrames T hx v) h₀ r T).card +
      (lastStints (headFrames T hx v) h₀ r T).card) ≤ 8 * T := by
  have hW : ∑ σ ∈ (headFrames T hx v).segments, 2 ^ band ((headFrames T hx v).segMax σ) ≤ T :=
    sum_segWeight_upperFrames_le (isWalk_headWalk hx v)
  have hB := sum_stdWeight_le (S := headFrames T hx v) (h₀ := h₀) T
  have hc : ∀ (A : Finset (ℕ × ℕ)) (r : ℕ), A.card ≤ ∑ tg ∈ A, 2 ^ flr h₀ r tg.2 := fun A r => by
    rw [card_eq_sum_ones]
    exact sum_le_sum fun _ _ => Nat.one_le_two_pow
  calc _ ≤ ∑ r ∈ range h₀, (∑ tg ∈ rises (headFrames T hx v) h₀ r T, 2 ^ flr h₀ r tg.2 +
        ∑ tg ∈ lastStints (headFrames T hx v) h₀ r T, 2 ^ flr h₀ r tg.2) :=
        sum_le_sum fun r _ => Nat.add_le_add (hc _ r) (hc _ r)
    _ ≤ 8 * ∑ σ ∈ (headFrames T hx v).segments, 2 ^ band ((headFrames T hx v).segMax σ) := hB
    _ ≤ 8 * T := Nat.mul_le_mul_left _ hW

/-- A head has at most `2T + 1` frames: the root and at most `2T` suspend frames. -/
theorem card_frames_head_le (v : Fin (k * 2)) : (headFrames T hx v).frames.card ≤ 2 * T + 1 := by
  have := card_suspendFrames_le (isWalk_headWalk hx v) (T := T)
  show (insert (0, T) (suspendFrames (headWalk xs v) T)).card ≤ 2 * T + 1
  exact (card_insert_le _ _).trans (by omega)

/-- A head has at most `4T + 1` turning points and segment starts. -/
theorem card_events_head_le (v : Fin (k * 2)) :
    (turnsOf (headFrames T hx v)).card + (segStarts (headFrames T hx v)).card ≤ 4 * T + 1 := by
  have h1 : (turnsOf (headFrames T hx v)).card ≤ T :=
    (card_filter_le _ _).trans (by rw [card_range]; exact (headFrames_T T hx v).le)
  have h2 := card_segStarts_le (S := headFrames T hx v)
  have h3 := card_frames_head_le T hx v
  rw [headFrames_T] at h2
  omega

/-- A head's events weigh at most `6T + 1`. -/
theorem weight_events_head_le (v : Fin (k * 2)) :
    ∑ s ∈ turnsOf (headFrames T hx v),
        2 ^ band (prom (headFrames T hx v).x (headFrames T hx v).T s) +
      ∑ Fs ∈ segStarts (headFrames T hx v), 2 ^ segScale (headFrames T hx v) Fs.1 Fs.2 ≤ 6 * T + 1 := by
  have h1 := sum_turns_weight_le (isWalk_headFrames T hx v)
  have h2 := sum_segStarts_weight_le (S := headFrames T hx v)
  have hW : ∑ σ ∈ (headFrames T hx v).segments, 2 ^ band ((headFrames T hx v).segMax σ) ≤ T :=
    sum_segWeight_upperFrames_le (isWalk_headWalk hx v)
  have h3 := card_segStarts_le (S := headFrames T hx v)
  have h4 := card_frames_head_le T hx v
  rw [headFrames_T] at h1 h3 ⊢
  omega

variable {Q : ℕ} [NeZero Q]

/-- **The cut state edges, summed over the random choices.** -/
theorem sum_descents_le {K P : ℕ} (hK : 0 < K) :
    ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
        ∑ ξ : EntryIdx (headFrames T hx) → Fin Q,
          (descentsOf (labelOf T hx h₀ K P r ω ξ) T).card ≤
      K ^ P * Q ^ Fintype.card (EntryIdx (headFrames T hx)) * (k * 2 * (8 * T)) +
        Q ^ Fintype.card (EntryIdx (headFrames T hx)) * h₀ * (P * K ^ (P - 1) * (k * 2 * (4 * T + 1))) := by
  classical
  set ι := EntryIdx (headFrames T hx)
  have hω : (Fintype.piFinset fun _ : Fin P => range K).card = K ^ P := by
    rw [Fintype.card_piFinset]; simp
  have hξ : (univ : Finset (ι → Fin Q)).card = Q ^ Fintype.card ι := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  calc _ ≤ ∑ r ∈ range h₀, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), ∑ ξ : ι → Fin Q,
        ((eventTimes T hx (h₀ := h₀) r).card + (wrapTimes T hx (h₀ := h₀) K P r ω ξ).card) := by
        refine sum_le_sum fun r hr => sum_le_sum fun ω _ => sum_le_sum fun ξ _ => ?_
        exact card_descents_le T hx (mem_range.mp hr) ω ξ
    _ = ∑ r ∈ range h₀, (K ^ P * Q ^ Fintype.card ι * (eventTimes T hx (h₀ := h₀) r).card +
        ∑ ξ : ι → Fin Q, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
          (wrapTimes T hx (h₀ := h₀) K P r ω ξ).card) := by
        refine sum_congr rfl fun r _ => ?_
        simp only [sum_add_distrib, sum_const, smul_eq_mul, hω, hξ]
        rw [sum_comm (s := Fintype.piFinset fun _ : Fin P => range K)]
        ring
    _ ≤ ∑ r ∈ range h₀, (K ^ P * Q ^ Fintype.card ι * ∑ w, ((rises (headFrames T hx w) h₀ r T).card +
          (lastStints (headFrames T hx w) h₀ r T).card) +
        Q ^ Fintype.card ι * (P * K ^ (P - 1) * (k * 2 * (4 * T + 1)))) := by
        refine sum_le_sum fun r _ => Nat.add_le_add
          (Nat.mul_le_mul_left _ (card_eventTimes_le T hx r)) ?_
        calc ∑ ξ : ι → Fin Q, ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
              (wrapTimes T hx (h₀ := h₀) K P r ω ξ).card
            ≤ ∑ _ξ : ι → Fin Q, P * K ^ (P - 1) * (k * 2 * (4 * T + 1)) := by
              refine sum_le_sum fun ξ _ => (sum_card_wrapTimes_le T hx hK ξ).trans ?_
              refine Nat.mul_le_mul_left _ ?_
              calc ∑ w, ((turnsOf (headFrames T hx w)).card + (segStarts (headFrames T hx w)).card)
                  ≤ ∑ _w : Fin (k * 2), (4 * T + 1) := sum_le_sum fun w _ => card_events_head_le T hx w
                _ = k * 2 * (4 * T + 1) := by simp
          _ = Q ^ Fintype.card ι * (P * K ^ (P - 1) * (k * 2 * (4 * T + 1))) := by
              rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
    _ = K ^ P * Q ^ Fintype.card ι * ∑ w, ∑ r ∈ range h₀, ((rises (headFrames T hx w) h₀ r T).card +
          (lastStints (headFrames T hx w) h₀ r T).card) +
        Q ^ Fintype.card ι * h₀ * (P * K ^ (P - 1) * (k * 2 * (4 * T + 1))) := by
        rw [sum_add_distrib, ← mul_sum, sum_comm, sum_const, card_range, smul_eq_mul]
        ring
    _ ≤ _ := by
        refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
        calc ∑ w, ∑ r ∈ range h₀, ((rises (headFrames T hx w) h₀ r T).card +
              (lastStints (headFrames T hx w) h₀ r T).card)
            ≤ ∑ _w : Fin (k * 2), 8 * T := sum_le_sum fun w _ => sum_events_head_le T hx w
          _ = k * 2 * (8 * T) := by simp

end BoundedStackDepth
