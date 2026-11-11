import AdaptiveTransfer.FeedbackConsumer
import AdaptiveTransfer.FeedbackMatrix
import LeanMachine.OrderedEmissionWindows
import LeanMachine.OptionalReadSlices

/-! Chronological column windows extracted from one complete consumer word.
The only correctness premise concerns its entire literal emission record.
Window entry states, query/step slices and output selectors are definitions.
-/

namespace AdaptiveTransfer.FeedbackGlobalWindows

open TransposeFollowup LeanMachine Finset Classical
open scoped BigOperators

abbrev Column (d b : ℕ) := Fin d × Fin b → Bool

def columnValues {d b : ℕ} (order : Equiv.Perm (Fin d))
    (X : FeedbackMatrixBit d b → Bool) (q : Fin d) : Column d b :=
  fun rb => X (rb.1, order q, rb.2)

noncomputable def start {d N : ℕ} (pos : Fin d → Fin N) (w j : ℕ) : ℕ :=
  OrderedEmissionWindows.cut pos (j * w)

noncomputable def length {d N : ℕ} (pos : Fin d → Fin N) (w j : ℕ) : ℕ :=
  start pos w (j + 1) - start pos w j

noncomputable def slice {d N : ℕ} {V : Type*} (pos : Fin d → Fin N) (w j : ℕ)
    (xs : List V) : List V := (xs.drop (start pos w j)).take (length pos w j)

noncomputable def entry {d N : ℕ} {C D E : Type*} (pos : Fin d → Fin N) (w j : ℕ)
    (steps : List (ReadOnlyStep C D E)) (initial : C) (data : List D) : C :=
  (ReadOnlyStep.run (steps.take (start pos w j)) initial (data.take (start pos w j))).1

noncomputable def readout {d b N w : ℕ} {C : Type*} (pos : Fin d → Fin N)
    (hw : 0 < w) (order : Equiv.Perm (Fin d)) (j : Fin ⌈(d : ℝ) / w⌉₊)
    (_initial : C) (result : C × List (Option (Column d b))) : FeedbackMatrixBit d b → Bool :=
  fun i => if ShiftedGrid.windowLabel d w hw (order.symm i.2.1) = j then
    ((result.2[(pos (order.symm i.2.1)).val - start pos w j.val]?).join.getD
      (fun _ => false)) (i.1, i.2.2)
  else false

theorem column_mem_window {d w : ℕ} (hw : 0 < w) (order : Equiv.Perm (Fin d))
    (j : Fin ⌈(d : ℝ) / w⌉₊) (c : Fin d) :
    c ∈ feedbackWindowColumns hw order j ↔ ShiftedGrid.windowLabel d w hw (order.symm c) = j := by
  constructor
  · intro hc
    obtain ⟨q, hq, he⟩ := mem_image.mp hc
    have hqc : q = order.symm c := by rw [← he, order.symm_apply_apply]
    simpa only [hqc] using (mem_filter.mp hq).2
  · intro hc
    exact mem_image.mpr ⟨order.symm c, mem_filter.mpr ⟨mem_univ _, hc⟩, order.apply_symm_apply c⟩

theorem ordinal_bounds {d w : ℕ} (hw : 0 < w) (j : Fin ⌈(d : ℝ) / w⌉₊)
    (q : Fin d) (hq : ShiftedGrid.windowLabel d w hw q = j) :
    j.val * w ≤ q.val ∧ q.val < (j.val + 1) * w := by
  have he : q.val / w = j.val := congrArg Fin.val hq
  have hlo := Nat.div_mul_le_self q.val w
  have hhi := Nat.lt_mul_div_succ q.val hw
  rw [he] at hlo hhi
  simpa only [Nat.mul_comm w] using And.intro hlo hhi

/-- Actual slice evaluation retrieves the designated columns solely from
the slice's own emissions. No old output record is readable by a step. -/
theorem window_correct {d b N w : ℕ} {C D : Type*}
    (pos : Fin d → Fin N) (hpos : StrictMono pos) (hw : 0 < w)
    (order : Equiv.Perm (Fin d)) (steps : List (ReadOnlyStep C D (Option (Column d b))))
    (initial : C) (data : List D) (hlen : steps.length = N)
    (hdata : steps.length = data.length) (X : FeedbackMatrixBit d b → Bool)
    (hcorrect : (ReadOnlyStep.run steps initial data).2 =
      OrderedEmissionWindows.record pos (columnValues order X))
    (j : Fin ⌈(d : ℝ) / w⌉₊) :
    readout pos hw order j (entry pos w j.val steps initial data)
      (ReadOnlyStep.run (slice pos w j.val steps) (entry pos w j.val steps initial data)
        (slice pos w j.val data)) =
      bitView (feedbackColumns (feedbackWindowColumns hw order j)) X := by
  funext i
  have hmem : i ∈ feedbackColumns (feedbackWindowColumns hw order j) ↔
      ShiftedGrid.windowLabel d w hw (order.symm i.2.1) = j := by
    simp only [feedbackColumns, mem_filter, mem_univ, true_and, column_mem_window]
  by_cases hi : ShiftedGrid.windowLabel d w hw (order.symm i.2.1) = j
  · obtain ⟨hlo, hhi⟩ := ordinal_bounds hw j (order.symm i.2.1) hi
    have he := OrderedEmissionWindows.run_window_get_write pos hpos (columnValues order X)
      steps initial data hlen hdata hcorrect (order.symm i.2.1) hlo hhi
    change ((ReadOnlyStep.run (slice pos w j.val steps) (entry pos w j.val steps initial data)
      (slice pos w j.val data)).2[(pos (order.symm i.2.1)).val - start pos w j.val]?) = _ at he
    simp only [readout, hi, ite_true, he, Option.join_some, Option.getD_some,
      columnValues, order.apply_symm_apply, bitView, hmem.mpr hi, ite_true]
  · simp only [readout, hi, ite_false, bitView, show i ∉ feedbackColumns
      (feedbackWindowColumns hw order j) from fun h => hi (hmem.mp h), ite_false]

theorem slice_map {d N : ℕ} {V W : Type*} (pos : Fin d → Fin N) (w j : ℕ)
    (f : V → W) (xs : List V) : slice pos w j (xs.map f) = (slice pos w j xs).map f := by
  simp [slice, List.map_take, List.map_drop]

theorem reads_windows_le {d N m : ℕ} {Q : Type*} (pos : Fin d → Fin N)
    (hpos : StrictMono pos) (w : ℕ) (queries : List (Option Q)) :
    ∑ j : Fin m, OptionalReadSlices.reads (slice pos w j.val queries) ≤ OptionalReadSlices.reads queries := by
  apply OptionalReadSlices.sum_reads_slices_le queries (start pos w)
  intro i j hij
  exact OrderedEmissionWindows.cut_mono pos hpos (Nat.mul_le_mul_right w hij)

end AdaptiveTransfer.FeedbackGlobalWindows
