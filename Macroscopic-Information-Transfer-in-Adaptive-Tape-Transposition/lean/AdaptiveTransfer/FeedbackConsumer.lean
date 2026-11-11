import AdaptiveTransfer.FeedbackBlockProducer
import LeanMachine.ReadOnlyProgram

/-! Read-only windows over literal raw coordinates and dated block values.
Recovery is derived from evaluating total read transitions. The emitted list
is a proof-side record; transitions cannot inspect it. -/

namespace AdaptiveTransfer
open TransposeFollowup LeanMachine Finset Classical

variable {ι κ S A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
  (owner : ι → κ) (p : BlockProgram κ (OwnedBits owner) S A) (T : ℕ)

/-- A raw query can ask for any subset of one owner's coordinates. A dated
query reads the actual value of one earlier producer operation. -/
inductive FeedbackQuery where
  | raw (a : κ) (coordinates : Finset ι) (locality : coordinates ⊆ ownedCoordinates owner a)
  | version (t : Fin T)

namespace FeedbackQuery

def group : FeedbackQuery owner T → κ
  | .raw a _ _ => a
  | .version t => p.owner t.val

def value : FeedbackQuery owner T → (ι → Bool) → (ι → Bool) ⊕ A
  | .raw _ coordinates _, x => Sum.inl (bitView coordinates x)
  | .version t, x => Sum.inr (p.eval (ownedInput owner x) t.val).2

theorem value_factorsThrough (q : FeedbackQuery owner T) :
    (value owner p T q).FactorsThrough (fun x => (blockTranscript owner p T x,
      bitView (ownedCoordinates owner (group owner p T q)) x)) := by
  cases q with
  | raw a coordinates hlocal =>
    intro x y he
    exact congrArg Sum.inl (bitView_factorsThrough id hlocal (congrArg Prod.snd he))
  | version t =>
    intro x y he
    exact congrArg Sum.inr (block_version_factorsThrough owner p T t.val t.isLt he)

end FeedbackQuery

/-- Local instructions have no external query. Only present query slots count. -/
def feedbackReads (queries : List (Option (FeedbackQuery owner T))) : ℕ :=
  (queries.filterMap id).length

/-- Every queried owner is counted at most once and the bound uses the actual
number of reads, including repeated queries. -/
noncomputable def feedbackQueried (queries : List (Option (FeedbackQuery owner T))) : Finset κ :=
  ((queries.filterMap id).map (fun q => FeedbackQuery.group owner p T q)).toFinset

omit [DecidableEq ι] in
theorem feedbackQueried_card (queries : List (Option (FeedbackQuery owner T))) :
    (feedbackQueried owner p T queries).card ≤ feedbackReads owner T queries := by
  exact (List.toFinset_card_le _).trans_eq (List.length_map _)

/-- The actual consumer result is determined by the common transcript,
queried owners' raw blocks, and the actual entry state. Local steps receive
`none`, and are not charged as reads. Empty windows are included. -/
theorem feedback_consumer_factorsThrough
    {Ω C E Y : Type*} (X : Ω → ι → Bool) (entry : Ω → C)
    (queries : List (Option (FeedbackQuery owner T)))
    (steps : List (ReadOnlyStep C (Option ((ι → Bool) ⊕ A)) E))
    (readout : C → C × List E → Y) :
    (fun x => readout (entry x) (ReadOnlyStep.run steps (entry x)
      (queries.map (fun q => q.map (fun q => FeedbackQuery.value owner p T q (X x)))))).FactorsThrough
      (fun x => (blockTranscript owner p T (X x),
        finiteView (feedbackQueried owner p T queries)
          (fun a => bitView (ownedCoordinates owner a) (X x)), entry x)) := by
  intro x y he
  have hs : entry x = entry y := congrArg (fun v => v.2.2) he
  have hdata : queries.map (fun q => q.map (fun q => FeedbackQuery.value owner p T q (X x))) =
      queries.map (fun q => q.map (fun q => FeedbackQuery.value owner p T q (X y))) := by
    apply List.map_congr_left
    intro q hq
    cases q with
    | none => rfl
    | some q =>
      apply congrArg some
      apply FeedbackQuery.value_factorsThrough owner p T q
      apply Prod.ext
      · have hz := congrArg Prod.fst he
        exact hz
      · have hg : FeedbackQuery.group owner p T q ∈ feedbackQueried owner p T queries := by
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,
            List.mem_filterMap.mpr ⟨some q, hq, rfl⟩, rfl⟩)
        exact (finiteView_eq_iff _ _ _).mp (congrArg (fun v => v.2.1) he) _ hg
  change readout (entry x) _ = readout (entry y) _
  rw [hs, hdata]

end AdaptiveTransfer
