import CascadeObstruction.C5Schedule
import CascadeObstruction.C5Compiler
import CascadeObstruction.GapTransfer

/-! Arbitrary finite-controller data completions of the concrete C5 word.
The only semantic premise is correct transposition on a nonempty input set.
Clock and motion certificates are deliberately not fields of this structure. -/

namespace CascadeObstruction.C5

open Set Filter Topology Transpose
open Transpose.Tape Transpose.Tape.Impl

set_option autoImplicit false

theorem canonical_width_pos (d : ℕ) : 0 < entryBits d := by
  unfold entryBits
  omega

theorem canonical_length_eq {d K : ℕ} (hd : d = 2 ^ (K + 1)) :
    inputLength K (entryBits d) = Transpose.inputLength d := by
  subst d
  simp [inputLength, Transpose.inputLength, show 2 * (K + 1) = (K + 1) + (K + 1) by omega,
    pow_add]

/-- A C5 completion at a legal dyadic dimension. `controller + 1` is its
number of source states; a public clock is added only by the proved compiler. -/
structure CorrectCompletion (g d : ℕ) where
  levels : ℕ
  levels_pos : 0 < levels
  dimension : d = 2 ^ (levels + 1)
  controller : ℕ
  rules : Fin (trace levels (entryBits d)).length → Compiler.DataRule 2 g controller
  correctSet : Set (List Bool)
  nonempty : correctSet.Nonempty
  correct : ∀ w ∈ correctSet, ∃ A : Matrix,
    w = encode d (entryBits d) A ∧
      (Compiler.run (completion (trace levels (entryBits d)) rules) w
        (trace levels (entryBits d)).length).outRev.reverse =
          encode d (entryBits d) (transpose A)

def CorrectCompletion.program {g d : ℕ} (x : CorrectCompletion g d) :
    Compiler.Program 2 g x.controller (trace x.levels (entryBits d)).length :=
  completion (trace x.levels (entryBits d)) x.rules

noncomputable def CorrectCompletion.machine {g d : ℕ} (x : CorrectCompletion g d) : TM :=
  Compiler.machine x.program

theorem CorrectCompletion.correct_native {g d : ℕ} (x : CorrectCompletion g d)
    (w : List Bool) (hw : w ∈ x.correctSet) :
    ∃ A : Matrix, w = encode d (entryBits d) A ∧
      (Transpose.Tape.run x.machine w (trace x.levels (entryBits d)).length).outRev.reverse =
        encode d (entryBits d) (transpose A) := by
  obtain ⟨A, hA, hout⟩ := x.correct w hw
  refine ⟨A, hA, ?_⟩
  rw [CorrectCompletion.machine, Compiler.output_word]
  exact hout

theorem CorrectCompletion.card_bounds {g d : ℕ} (x : CorrectCompletion g d) :
    0 < x.correctSet.ncard ∧ x.correctSet.ncard ≤ 2 ^ Transpose.inputLength d := by
  have hsub : x.correctSet ⊆ matrixInputs d (entryBits d) := by
    intro w hw
    obtain ⟨A, hA, _⟩ := x.correct w hw
    exact ⟨A, hA.symm⟩
  have hf : (matrixInputs d (entryBits d)).Finite := by
    rw [matrixInputs_eq]
    exact List.finite_length_eq Bool _
  exact ⟨x.nonempty.ncard_pos (hf.subset hsub),
    by simpa only [ncard_matrixInputs, Transpose.inputLength] using
      Set.ncard_le_ncard hsub hf⟩

theorem CorrectCompletion.work_trajectory {g d : ℕ} (x : CorrectCompletion g d)
    (w : List Bool) (n : ℕ) (h : Fin 2) :
    workTraj x.machine w n h = position (trace x.levels (entryBits d)) (workHead h) n :=
  completion_work_trajectory _ _ w n h

theorem CorrectCompletion.haltsAt_iff {g d : ℕ} (x : CorrectCompletion g d)
    (w : List Bool) (n : ℕ) :
    HaltsAt x.machine w n ↔ n = (trace x.levels (entryBits d)).length :=
  Compiler.haltsAt_iff x.program w n

end CascadeObstruction.C5
