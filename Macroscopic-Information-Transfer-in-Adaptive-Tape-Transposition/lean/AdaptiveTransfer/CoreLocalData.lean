import AdaptiveTransfer.CoreReplayClass
import AdaptiveTransfer.LocalClassData

/-! Actual multi-core metadata and ordinary records for
localized cuts. Root coverage is extracted from the original append counters;
full successful completions and paid snapshot agreement are explicit. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset NativeRelations

namespace CoreReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : CoreReplayClass M P π)

theorem omitted_output_cover (X : g.inputs) {p : Fin P} (hp : p ∈ g.omitted) :
    ∃ t ∈ g.times, ∃ j : Fin P, π j = p ∧
      ((g.exec X).config t).outRev.length = j.val ∧ ((g.exec X).emitted t).isSome :=
  geometryOmitted_output_cover (g.exec X) π g.times g.time_lt g.outLo g.outHi g.rawLo g.rawHi
    (g.out_lo X) (g.out_hi X) p hp

noncomputable def localRootTime (X : g.inputs) (p : g.omitted) : ℕ :=
  (g.omitted_output_cover X p.property).choose

theorem localRootTime_spec (X : g.inputs) (p : g.omitted) :
    g.localRootTime X p ∈ g.times ∧ ∃ j : Fin P, π j = p.val ∧
      ((g.exec X).config (g.localRootTime X p)).outRev.length = j.val ∧
        ((g.exec X).emitted (g.localRootTime X p)).isSome :=
  (g.omitted_output_cover X p.property).choose_spec

noncomputable def localRoots (X : g.inputs) : Finset ℕ :=
  univ.image (g.localRootTime X)

theorem localRoots_subset_times (X : g.inputs) : g.localRoots X ⊆ g.times := by
  classical
  intro t ht
  obtain ⟨p, _hp, he⟩ := mem_image.mp ht
  exact he ▸ (g.localRootTime_spec X p).1

/-- The canonically selected roots are actual append steps demanding U.
A full original Out(U)-separator therefore separates these roots as well. -/
theorem localRoots_subset_outputs (X : g.inputs) :
    g.localRoots X ⊆ nativeDemandedOutputSteps M X.val (g.finish X) π g.omitted := by
  classical
  intro t ht
  obtain ⟨p, _hp, he⟩ := mem_image.mp ht
  have hs := g.localRootTime_spec X p
  rw [he] at hs
  obtain ⟨htC, j, hj, hc, ho⟩ := hs
  have htT := g.time_lt t htC
  rw [(g.exec X).config_eq_run htT.le] at hc
  rw [(g.exec X).emitted_eq_outBit htT.le] at ho
  exact mem_filter.mpr ⟨mem_range.mpr (htT.trans_le (g.finish_ge X)), j,
    hj ▸ p.property, hc, ho⟩

/-- The extra native data needed beyond the local chunk: successful execution
up to the actual final output time, a common public time budget, and a real
outer-start configuration. No replay or counting certificate is included. -/
structure Completion where
  active : ∀ X : g.inputs, ∀ t < g.finish X, transAt M (List.ofFn X.val) t ≠ none
  finish_le : ∀ X : g.inputs, g.finish X ≤ g.limit
  outer_start : g.start ≤ g.horizon

namespace Completion
variable {g} (c : g.Completion)

def fullExec (X : g.inputs) : ExecutionPrefix M (List.ofFn X.val) (g.finish X) :=
  ExecutionPrefix.ofRun M _ (g.finish X) (c.active X)

theorem prefix_eq (X : g.inputs) {t : ℕ} (ht : t ≤ g.horizon) :
    (c.fullExec X).config t = (g.exec X).config t :=
  ((g.exec X).config_eq_run ht).symm

theorem ordinary_controls {X Y : g.inputs} (he : g.ordinary X = g.ordinary Y)
    {r : ℕ} (hr : r ∈ runStarts g.times) :
    SameControl ((c.fullExec X).config r) ((c.fullExec Y).config r) := by
  have hrT := (g.time_lt r (mem_filter.mp hr).1).le
  rw [c.prefix_eq X hrT, c.prefix_eq Y hrT]
  exact CoreReplayClass.ordinary_controls he hr

theorem ordinary_snapshots {X Y : g.inputs} (he : g.ordinary X = g.ordinary Y)
    (h : Fin M.k) (t : ℕ) :
    (c.fullExec X).clusterSnapshot g.times g.cluster g.core g.fringe g.start g.radius h t =
      (c.fullExec Y).clusterSnapshot g.times g.cluster g.core g.fringe g.start g.radius h t := by
  funext z
  by_cases hh : h ∈ g.cluster
  · simp only [ExecutionPrefix.clusterSnapshot, hh, ite_true]
    by_cases hc : (g.start ≠ 0 ∧ t = g.start ∧ z ∈ g.core h) ∨
        (t ∈ runStarts g.times ∧ z ∈ g.fringe h)
    · simp only [hc, ite_true, Option.some.injEq]
      rcases hc with ⟨ha, rfl, hz⟩ | ⟨ht, hz⟩
      · rw [c.prefix_eq X c.outer_start, c.prefix_eq Y c.outer_start]
        exact CoreReplayClass.ordinary_cores he h hz
      · have htT := (g.time_lt t (mem_filter.mp ht).1).le
        rw [c.prefix_eq X htT, c.prefix_eq Y htT]
        exact CoreReplayClass.ordinary_entry he ht h (by simpa only [entryCells, hh, ite_true] using hz)
    · simp only [hc, ite_false]
  · simp only [ExecutionPrefix.clusterSnapshot, hh, ite_false]
    by_cases ht : t ∈ runStarts g.times
    · have hp := congrFun (c.ordinary_controls he ht).2.2 h
      simp only [ht, true_and, ← hp]
      by_cases hz : (z - ((c.fullExec X).config t).workPos h).natAbs ≤ g.radius
      · simp only [hz, ite_true, Option.some.injEq]
        have htT := (g.time_lt t (mem_filter.mp ht).1).le
        rw [c.prefix_eq X htT, g.work_entry X t ht] at hz
        rw [c.prefix_eq X htT, c.prefix_eq Y htT]
        apply CoreReplayClass.ordinary_entry he ht h
        have hab : |z - g.workEntry t h| ≤ (g.radius : ℤ) := by
          rw [← Int.natCast_natAbs]; exact_mod_cast hz
        simp only [entryCells, hh, ite_false, mem_Icc]
        obtain ⟨h₁, h₂⟩ := abs_le.mp hab
        constructor <;> omega
      · simp only [hz, ite_false]
    · simp only [ht, false_and, ite_false]

end Completion
end CoreReplayClass
end AdaptiveTransfer
