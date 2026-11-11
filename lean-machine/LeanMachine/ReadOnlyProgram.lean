import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Basic

/-! Fixed-word read-only programs. The only mutable readable object is the
resident state. Outputs are accumulated as a mathematical record of emissions
and are never arguments to a transition. This is not a native-tape compiler. -/

namespace LeanMachine

structure ReadOnlyStep (State Data Output : Type*) where
  transition : State → Data → State × Output

namespace ReadOnlyStep

variable {S D O : Type*}

def run : List (ReadOnlyStep S D O) → S → List D → S × List O
  | [], s, _ => (s, [])
  | _ :: _, s, [] => (s, [])
  | step :: rest, s, v :: vs =>
    let next := step.transition s v
    let tail := run rest next.1 vs
    (tail.1, next.2 :: tail.2)

/-- Only the real entry state and read values determine a window's outputs. -/
theorem output_eq (steps : List (ReadOnlyStep S D O))
    {s t : S} {u v : List D} (hs : s = t) (hu : u = v) :
    (run steps s u).2 = (run steps t v).2 := by rw [hs, hu]

/-- A query has one original owner, and all its data are functions of that
owner's raw block plus the common transcript. Query order and repetition
are preserved in the actual read list. The complete run result is covered,
including empty read lists and final state-dependent emissions. -/
theorem queried_result_factorsThrough
    {X I A Z : Type*}
    (steps : List (ReadOnlyStep S D O)) (queries : List I)
    (raw : X → I → A) (z : X → Z) (entry : X → S)
    (datum : (j : Fin queries.length) → X → D)
    (locality : ∀ j, (datum j).FactorsThrough (fun x => (z x, raw x (queries.get j)))) :
    (fun x => run steps (entry x) (List.ofFn (fun j => datum j x))).FactorsThrough
      (fun x => (z x, (fun i : {i // i ∈ queries} => raw x i.val), entry x)) := by
  intro x y he
  have hs : entry x = entry y := congrArg (fun v => v.2.2) he
  change run steps (entry x) _ = run steps (entry y) _
  rw [hs]
  congr 1
  apply congrArg List.ofFn
  funext j
  have hz : z x = z y := congrArg Prod.fst he
  have hr := congrArg (fun v => v.2.1) he
  exact locality j (Prod.ext hz (congrFun hr ⟨queries.get j, List.get_mem queries j⟩))

/-- Output-only specialization of the complete run result. -/
theorem queried_output_factorsThrough
    {X I A Z : Type*}
    (steps : List (ReadOnlyStep S D O)) (queries : List I)
    (raw : X → I → A) (z : X → Z) (entry : X → S)
    (datum : (j : Fin queries.length) → X → D)
    (locality : ∀ j, (datum j).FactorsThrough (fun x => (z x, raw x (queries.get j)))) :
    (fun x => (run steps (entry x) (List.ofFn (fun j => datum j x))).2).FactorsThrough
      (fun x => (z x, (fun i : {i // i ∈ queries} => raw x i.val), entry x)) := by
  intro x y he
  exact congrArg Prod.snd
    (queried_result_factorsThrough steps queries raw z entry datum locality he)

end ReadOnlyStep
end LeanMachine
