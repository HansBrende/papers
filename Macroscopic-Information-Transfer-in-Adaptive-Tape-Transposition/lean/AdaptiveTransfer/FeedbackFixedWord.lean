import AdaptiveTransfer.FeedbackCoordinates
import AdaptiveTransfer.FeedbackConsumer

/-! Fixed-partition inequality for an actual producer followed by actual
read-only windows. Every local rule is total; only its stated finite state
and raw/dated queries enter its evaluation. Correctness is used on the one
specified source law, not on mixed inputs. -/

namespace AdaptiveTransfer
open TransposeFollowup LeanMachine Finset Classical
open scoped BigOperators

variable {ι κ W Ω S A C E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype W] [DecidableEq W] [Nonempty W]
  [Fintype Ω] [Nonempty Ω] [Fintype S] [Fintype A] [Fintype C] [Nonempty C]

theorem feedback_fixed_partition_bound
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (owner : ι → κ) (p : BlockProgram κ (OwnedBits owner) S A) (T : ℕ)
    (X : Ω → ι → Bool) (columns : W → Finset ι)
    (hcover : ∀ i, ∃ w, i ∈ columns w)
    (entry : W → Ω → C) (queries : W → List (Option (FeedbackQuery owner T)))
    (steps : W → List (ReadOnlyStep C (Option ((ι → Bool) ⊕ A)) E))
    (readout : W → C → C × List E → κ → ι → Bool)
    (hcorrect : ∀ w x, readout w (entry w x) (ReadOnlyStep.run (steps w) (entry w x)
      ((queries w).map (fun q => q.map (fun q => FeedbackQuery.value owner p T q (X x))))) =
        feedbackProjection owner columns X w x)
    (sbits M Δ : ℝ) (hs : (Fintype.card S : ℝ) ≤ (2 : ℝ)^sbits)
    (hm : (Fintype.card C : ℝ) ≤ (2 : ℝ)^M)
    (menu : ℕ → Finset A) (bits : ℕ → ℝ)
    (hmenu : ∀ t s r v, (p.update t s r v).2 ∈ menu t)
    (hbits : ∀ t, ((menu t).card : ℝ) ≤ (2 : ℝ)^bits t)
    (hx : (Fintype.card ι - Δ) * Real.log 2 ≤ observationEntropy μ X) :
    (Fintype.card ι : ℝ) ≤
      sbits * (p.stateExports T).card + ∑ t ∈ p.versionExports T, bits t +
        Fintype.card W * (M + Δ) +
        ∑ w, ∑ a ∈ feedbackQueried owner p T (queries w),
          ((ownedCoordinates owner a ∩ columns w).card : ℝ) := by
  let : Nonempty S := ⟨p.initial⟩
  let : Nonempty A := ⟨p.constant⟩
  refine feedback_coordinate_bound μ hμ hμ1 owner X (blockTranscript owner p T)
    ?_ columns hcover entry (fun w => feedbackQueried owner p T (queries w)) ?_
    (sbits * (p.stateExports T).card + ∑ t ∈ p.versionExports T, bits t) M Δ ?_ hm hx
  · intro z
    convert blockTranscript_rectangle owner p T z using 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
  · intro w x y he
    rw [← hcorrect w x, ← hcorrect w y]
    exact feedback_consumer_factorsThrough owner p T X (entry w) (queries w)
      (steps w) (readout w) he
  · exact block_transcript_entropy_le owner p T μ hμ hμ1 X sbits hs menu bits hmenu hbits

omit [Fintype κ] [Nonempty κ] [DecidableEq W] [Nonempty W] [Fintype S] [Fintype A] in
/-- Any uniform rectangle capacity charges at most that capacity per actual
read. Repeated owners are charged only once in the stronger exact bound. -/
theorem feedback_query_rectangles_le
    (owner : ι → κ) (p : BlockProgram κ (OwnedBits owner) S A) (T : ℕ)
    (columns : W → Finset ι) (queries : W → List (Option (FeedbackQuery owner T)))
    (cap : ℝ) (hcap : 0 ≤ cap)
    (hsize : ∀ w a, ((ownedCoordinates owner a ∩ columns w).card : ℝ) ≤ cap) :
    (∑ w, ∑ a ∈ feedbackQueried owner p T (queries w),
      ((ownedCoordinates owner a ∩ columns w).card : ℝ)) ≤
        (∑ w, (feedbackReads owner T (queries w) : ℝ)) * cap := by
  rw [sum_mul]
  apply sum_le_sum
  intro w _
  calc
    _ ≤ ∑ _a ∈ feedbackQueried owner p T (queries w), cap :=
      sum_le_sum (fun a _ => hsize w a)
    _ = (feedbackQueried owner p T (queries w)).card * cap := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ feedbackReads owner T (queries w) * cap := mul_le_mul_of_nonneg_right
      (by exact_mod_cast feedbackQueried_card owner p T (queries w)) hcap

end AdaptiveTransfer
