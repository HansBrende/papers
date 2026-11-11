import AdaptiveTransfer.FeedbackGlobalWindows
import AdaptiveTransfer.FeedbackProduct

/-! The feedback bound for one complete fixed producer/consumer word.
Every width uses windows extracted from that same global execution. Local
instructions have absent query slots and contribute zero to the read count.
-/

namespace AdaptiveTransfer

open TransposeFollowup LeanMachine Finset Classical
open scoped BigOperators

variable {d b : ℕ} {Ω S A C : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype S] [Fintype A] [Fintype C] [Nonempty C]

variable
  (p : BlockProgram (Fin d) (OwnedBits (feedbackRowOwner (b := b) id)) S A) (T : ℕ)
  (X : Ω → FeedbackMatrixBit d b → Bool)
  (queries : List (Option (FeedbackQuery (feedbackRowOwner (b := b) id) T)))
  (steps : List (ReadOnlyStep C (Option ((FeedbackMatrixBit d b → Bool) ⊕ A))
    (Option (FeedbackGlobalWindows.Column d b))))
  (initial : Ω → C) (hslots : steps.length = queries.length)
  (order : Equiv.Perm (Fin d)) (pos : Fin d → Fin steps.length) (hpos : StrictMono pos)
  (hcorrect : ∀ x, (ReadOnlyStep.run steps (initial x)
    (queries.map (fun q => q.map (fun q => FeedbackQuery.value (feedbackRowOwner id) p T q (X x))))).2 =
      OrderedEmissionWindows.record pos (FeedbackGlobalWindows.columnValues order (X x)))

include hslots hpos hcorrect

/-- The exact matrix inequality from one actual global consumer evaluation
and one public ordered write schedule. No local recovery/entry/count data
are hypotheses: all window fields are constructed by slicing this word. -/
theorem feedback_global_matrix_bound (hd : 0 < d)
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (g w : ℕ) (hg : 0 < g) (hw : 0 < w)
    (Sbits M Δ : ℝ) (hS : 0 ≤ Sbits)
    (hs : (Fintype.card S : ℝ) ≤ (2 : ℝ)^Sbits)
    (hm : (Fintype.card C : ℝ) ≤ (2 : ℝ)^M)
    (menu : ℕ → Finset A) (bits : ℕ → ℝ) (hbits0 : ∀ t, 0 ≤ bits t)
    (hmenu : ∀ t s r v, (p.update t s r v).2 ∈ menu t)
    (hbits : ∀ t, ((menu t).card : ℝ) ≤ (2 : ℝ)^bits t)
    (hx : ((d*d*b : ℕ) - Δ) * Real.log 2 ≤ observationEntropy μ X) :
    (d*d*b : ℕ) ≤ (Sbits * p.variation Fin.val T + feedbackSpanCost p T bits) / g +
      (⌈(d : ℝ)/w⌉₊ : ℝ) * (M + Δ) +
        (feedbackReads (feedbackRowOwner id) T queries : ℝ) * g * w * b := by
  let data (x : Ω) := queries.map
    (fun q => q.map (fun q => FeedbackQuery.value (feedbackRowOwner id) p T q (X x)))
  let entries (j : Fin ⌈(d : ℝ)/w⌉₊) (x : Ω) :=
    FeedbackGlobalWindows.entry pos w j.val steps (initial x) (data x)
  let windowQueries (j : Fin ⌈(d : ℝ)/w⌉₊) := FeedbackGlobalWindows.slice pos w j.val queries
  let windowSteps (j : Fin ⌈(d : ℝ)/w⌉₊) := FeedbackGlobalWindows.slice pos w j.val steps
  let outputs (j : Fin ⌈(d : ℝ)/w⌉₊) := FeedbackGlobalWindows.readout (b := b) (C := C) pos hw order j
  have hwin : ∀ j x, outputs j (entries j x)
      (ReadOnlyStep.run (windowSteps j) (entries j x)
        ((windowQueries j).map (fun q => q.map
          (fun q => FeedbackQuery.value (feedbackRowOwner id) p T q (X x))))) =
      bitView (feedbackColumns (feedbackWindowColumns hw order j)) (X x) := by
    intro j x
    dsimp only [outputs, entries, windowSteps, windowQueries]
    rw [← FeedbackGlobalWindows.slice_map]
    exact FeedbackGlobalWindows.window_correct pos hpos hw order steps (initial x) (data x)
      rfl (by simpa only [data, List.length_map] using hslots) (X x) (hcorrect x) j
  have hreads : ∑ j, feedbackReads (feedbackRowOwner id) T (windowQueries j) ≤
      feedbackReads (feedbackRowOwner id) T queries := by
    exact FeedbackGlobalWindows.reads_windows_le pos hpos w queries
  exact feedback_matrix_window_bound hd μ hμ hμ1 p T X g w hg hw order
    entries windowQueries windowSteps outputs hwin _ hreads Sbits M Δ hS hs hm menu bits
    hbits0 hmenu hbits hx

/-- The published product consequence with its exact constant 72, now
quantifying one complete consumer word before any g,w windows are chosen. -/
theorem feedback_global_product_bound (hd : 0 < d) (hb : 0 < b)
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (Sbits M Δ : ℝ) (hS : 0 ≤ Sbits) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ)
    (hs : (Fintype.card S : ℝ) ≤ (2 : ℝ)^Sbits)
    (hm : (Fintype.card C : ℝ) ≤ (2 : ℝ)^M)
    (menu : ℕ → Finset A) (bits : ℕ → ℝ) (hbits0 : ∀ t, 0 ≤ bits t)
    (hmenu : ∀ t s r v, (p.update t s r v).2 ∈ menu t)
    (hbits : ∀ t, ((menu t).card : ℝ) ≤ (2 : ℝ)^bits t)
    (hx : ((d*d*b : ℕ) - Δ) * Real.log 2 ≤ observationEntropy μ X) :
    (d : ℝ) / 72 ≤ max 1 ((feedbackReads (feedbackRowOwner id) T queries : ℝ) / d) *
      (1 + (Sbits * p.variation Fin.val T + feedbackSpanCost p T bits) / (d*d*b : ℕ)) *
      (1 + (M + Δ) / (d*b : ℕ)) := by
  have hcost : 0 ≤ Sbits * p.variation Fin.val T + feedbackSpanCost p T bits := by
    apply add_nonneg (mul_nonneg hS (Nat.cast_nonneg _))
    exact sum_nonneg fun t _ => mul_nonneg (Nat.cast_nonneg _) (hbits0 t)
  apply feedback_product_of_matrix_windows d b _ hd hb _ _ hcost (add_nonneg hM hΔ)
  intro g w hg _ hw _
  exact feedback_global_matrix_bound p T X queries steps initial hslots order pos hpos hcorrect
    hd μ hμ hμ1 g w (by omega) (by omega) Sbits M Δ hS hs hm menu bits hbits0 hmenu hbits hx

end AdaptiveTransfer
