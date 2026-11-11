import AdaptiveTransfer.FeedbackConsumer
import LeanMachine.BlockProgramCoarsen

/-! Grouping the raw rows preserves every actual producer value and every
consumer query. These adapters transfer a single fixed computation to each
partition used in the feedback inequality. -/

namespace AdaptiveTransfer
open TransposeFollowup LeanMachine Finset Classical

variable {ι κ S A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
  (owner : ι → κ) (group : κ → κ)

/-- Literal restriction from the grouped raw block to an original owner. -/
def groupedRaw (a : κ) (v : OwnedBits (group ∘ owner) (group a)) : OwnedBits owner a :=
  fun i => v ⟨i.val, mem_filter.mpr ⟨mem_univ _,
    congrArg group ((mem_filter.mp i.property).2)⟩⟩

def groupedProducer (p : BlockProgram κ (OwnedBits owner) S A) :
    BlockProgram κ (OwnedBits (group ∘ owner)) S A :=
  p.coarsen group (groupedRaw owner group)

omit [DecidableEq ι] in
theorem groupedProducer_eval (p : BlockProgram κ (OwnedBits owner) S A) (x : ι → Bool) (t : ℕ) :
    (groupedProducer owner group p).eval (ownedInput (group ∘ owner) x) t =
      p.eval (ownedInput owner x) t := by
  rw [groupedProducer, BlockProgram.coarsen_eval]
  rfl

def groupedQuery {T : ℕ} : FeedbackQuery owner T → FeedbackQuery (group ∘ owner) T
  | .raw a coordinates hlocal => .raw (group a) coordinates (by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _, congrArg group ((mem_filter.mp (hlocal hi)).2)⟩)
  | .version t => .version t

theorem groupedQuery_value (p : BlockProgram κ (OwnedBits owner) S A) (T : ℕ)
    (q : FeedbackQuery owner T) (x : ι → Bool) :
    FeedbackQuery.value (group ∘ owner) (groupedProducer owner group p) T
      (groupedQuery owner group q) x = FeedbackQuery.value owner p T q x := by
  cases q with
  | raw a c h => rfl
  | version t =>
    change Sum.inr ((groupedProducer owner group p).eval (ownedInput (group ∘ owner) x) t.val).2 = _
    rw [groupedProducer_eval]
    rfl

theorem groupedQuery_values (p : BlockProgram κ (OwnedBits owner) S A) (T : ℕ)
    (queries : List (Option (FeedbackQuery owner T))) (x : ι → Bool) :
    (queries.map (Option.map (groupedQuery owner group))).map
      (fun q => q.map (fun q => FeedbackQuery.value (group ∘ owner) (groupedProducer owner group p) T q x)) =
        queries.map (fun q => q.map (fun q => FeedbackQuery.value owner p T q x)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  cases q with
  | none => rfl
  | some q => exact congrArg some (groupedQuery_value owner group p T q x)

omit [DecidableEq ι] in
theorem groupedQuery_reads (T : ℕ) (queries : List (Option (FeedbackQuery owner T))) :
    feedbackReads (group ∘ owner) T (queries.map (Option.map (groupedQuery owner group))) =
      feedbackReads owner T queries := by
  induction queries with
  | nil => rfl
  | cons q qs ih => cases q <;> simpa [feedbackReads] using ih

end AdaptiveTransfer
