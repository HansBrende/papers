import AdaptiveTransfer.FeedbackFixedWord
import AdaptiveTransfer.FeedbackMatrix
import AdaptiveTransfer.FeedbackCoarsen
import AdaptiveTransfer.FeedbackNumerics
import LeanMachine.BlockSpan

/-! The finite fixed-word feedback inequality. Original row owners, literal
dated queries, and actual read-only evaluations are transported to the one
partition that simultaneously pays both producer charges. -/

namespace AdaptiveTransfer
open TransposeFollowup LeanMachine Finset Classical
open scoped BigOperators

variable {d b : ℕ} {Ω S A C E : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype S] [Fintype A] [Fintype C] [Nonempty C]

/-- The literal total participating capacity times span. Every dated value
is counted once; a date with no readers has zero span. -/
noncomputable def feedbackSpanCost
    (p : BlockProgram (Fin d) (OwnedBits (feedbackRowOwner (b := b) id)) S A)
    (T : ℕ) (bits : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range T, (p.span Fin.val T t : ℝ) * bits t

/-- Finite matrix bound for one complete producer and a subsequent read-only
consumer, split into its actual output windows. Window entries can even be
arbitrary source-dependent states; their complete capacities are paid. -/
theorem feedback_matrix_window_bound (hd : 0 < d)
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (p : BlockProgram (Fin d) (OwnedBits (feedbackRowOwner (b := b) id)) S A) (T : ℕ)
    (X : Ω → FeedbackMatrixBit d b → Bool)
    (g w : ℕ) (hg : 0 < g) (hw : 0 < w) (order : Equiv.Perm (Fin d))
    (entry : Fin ⌈(d : ℝ)/w⌉₊ → Ω → C)
    (queries : Fin ⌈(d : ℝ)/w⌉₊ → List (Option (FeedbackQuery (feedbackRowOwner (b := b) id) T)))
    (steps : Fin ⌈(d : ℝ)/w⌉₊ → List (ReadOnlyStep C (Option ((FeedbackMatrixBit d b → Bool) ⊕ A)) E))
    (readout : Fin ⌈(d : ℝ)/w⌉₊ → C → C × List E → FeedbackMatrixBit d b → Bool)
    (hcorrect : ∀ j x, readout j (entry j x) (ReadOnlyStep.run (steps j) (entry j x)
      ((queries j).map (fun q => q.map (fun q => FeedbackQuery.value (feedbackRowOwner id) p T q (X x))))) =
        bitView (feedbackColumns (feedbackWindowColumns hw order j)) (X x))
    (Q : ℕ) (hQ : ∑ j, feedbackReads (feedbackRowOwner id) T (queries j) ≤ Q)
    (Sbits M Δ : ℝ) (hS : 0 ≤ Sbits)
    (hs : (Fintype.card S : ℝ) ≤ (2 : ℝ)^Sbits)
    (hm : (Fintype.card C : ℝ) ≤ (2 : ℝ)^M)
    (menu : ℕ → Finset A) (bits : ℕ → ℝ) (hbits0 : ∀ t, 0 ≤ bits t)
    (hmenu : ∀ t s r v, (p.update t s r v).2 ∈ menu t)
    (hbits : ∀ t, ((menu t).card : ℝ) ≤ (2 : ℝ)^bits t)
    (hx : ((d*d*b : ℕ) - Δ) * Real.log 2 ≤ observationEntropy μ X) :
    (d*d*b : ℕ) ≤ (Sbits * p.variation Fin.val T + feedbackSpanCost p T bits) / g +
      (⌈(d : ℝ)/w⌉₊ : ℝ) * (M + Δ) + (Q : ℝ) * g * w * b := by
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hceil : 0 < ⌈(d : ℝ)/w⌉₊ := Nat.ceil_pos.mpr (by positivity)
  let : Nonempty (Fin ⌈(d : ℝ)/w⌉₊) := ⟨⟨0,hceil⟩⟩
  let owner := feedbackRowOwner (d := d) (b := b) id
  let groups (θ : Fin g) := ShiftedGrid.finiteLabel d g θ.val hg θ.isLt
  obtain ⟨θ, hpaid⟩ := p.exists_coarsened_cost_le Fin.val T g hg groups
    (fun θ => groupedRaw owner (groups θ)) (by
      intro θ r s
      exact Fin.ext_iff) Sbits hS bits hbits0
  let group := groups θ
  let producer := groupedProducer owner group p
  let columns (j : Fin ⌈(d : ℝ)/w⌉₊) :=
    feedbackColumns (b := b) (feedbackWindowColumns hw order j)
  let reads (j : Fin ⌈(d : ℝ)/w⌉₊) := (queries j).map (Option.map (groupedQuery owner group))
  let output (j : Fin ⌈(d : ℝ)/w⌉₊) (s : C) (result : C × List E) (a : Fin d) :=
    bitView (ownedCoordinates (group ∘ owner) a) (readout j s result)
  have hcorrect' : ∀ j x, output j (entry j x) (ReadOnlyStep.run (steps j) (entry j x)
      ((reads j).map (fun q => q.map (fun q => FeedbackQuery.value (group ∘ owner) producer T q (X x))))) =
        feedbackProjection (group ∘ owner) columns X j x := by
    intro j x
    dsimp only [reads, producer]
    rw [groupedQuery_values]
    funext a i
    dsimp only [output]
    rw [hcorrect]
    simp [feedbackProjection, bitView, columns, Bool.and_assoc]
  have hh := feedback_fixed_partition_bound μ hμ hμ1 (group ∘ owner) producer T X
    columns (fun i => feedback_matrix_window_cover hw order i) entry reads steps output hcorrect'
    Sbits M Δ hs hm menu bits (fun t s r v => hmenu t s (groupedRaw owner group _ r) v) hbits
    (by simpa only [FeedbackMatrixBit, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      mul_assoc] using hx)
  have hc := feedback_query_rectangles_le (group ∘ owner) producer T columns reads
    ((g*w*b : ℕ) : ℝ) (by positivity) (by
      intro j a
      exact_mod_cast feedback_matrix_window_card_le hg θ.isLt hw order a j)
  have hreads : (∑ j, (feedbackReads (group ∘ owner) T (reads j) : ℝ)) ≤ Q := by
    dsimp only [reads]
    simp only [groupedQuery_reads, ← Nat.cast_sum]
    exact_mod_cast hQ
  have hreadbill := mul_le_mul_of_nonneg_right hreads (by positivity : (0 : ℝ) ≤ (g*w*b : ℕ))
  have hn : Fintype.card (FeedbackMatrixBit d b) = d*d*b := by
    simp only [FeedbackMatrixBit, Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hn, Fintype.card_fin] at hh
  change Sbits * (producer.stateExports T).card + ∑ t ∈ producer.versionExports T, bits t ≤
    (Sbits * p.variation Fin.val T + feedbackSpanCost p T bits) / g at hpaid
  simp only [Nat.cast_mul] at hc hreadbill
  nlinarith

end AdaptiveTransfer
