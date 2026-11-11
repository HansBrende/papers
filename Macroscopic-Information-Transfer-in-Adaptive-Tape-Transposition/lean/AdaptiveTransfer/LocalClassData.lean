import AdaptiveTransfer.NativeImportInformation
import AdaptiveTransfer.LocalSnapshots

/-! Reuse of actual native replay-class metadata and ordinary records for
localized cuts. Root coverage is extracted from the original append counters;
full successful completions and paid snapshot agreement are explicit. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset NativeRelations

noncomputable def nativeDemandedOutputSteps (M : TM) {P : ℕ} (X : Fin P → Bool)
    (finish : ℕ) (π : Fin P → Fin P) (U : Finset (Fin P)) : Finset ℕ := by
  classical
  exact (range finish).filter fun t => ∃ j : Fin P, π j ∈ U ∧
    (run M (List.ofFn X) t).outRev.length = j.val ∧ (outBit M (List.ofFn X) t).isSome

namespace NativeReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : NativeReplayClass M P π)

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
  refine ⟨?_, (g.raw_entry X r hr).trans (g.raw_entry Y r hr).symm,
    (g.work_entry X r hr).trans (g.work_entry Y r hr).symm⟩
  exact congrFun (congrArg Prod.fst he) ⟨r, hr⟩

theorem ordinary_snapshots {X Y : g.inputs} (he : g.ordinary X = g.ordinary Y)
    (h : Fin M.k) (t : ℕ) :
    (c.fullExec X).localSnapshot g.times g.cells g.start g.radius g.free h t =
      (c.fullExec Y).localSnapshot g.times g.cells g.start g.radius g.free h t := by
  apply ExecutionPrefix.localSnapshot_eq_of_paid
  · intro r hr
    exact (c.ordinary_controls he hr).2.2
  · intro ha z hz
    have hz' : z ∈ snapshotCells g.start g.cells := by simp only [snapshotCells, ite_eq_right ha]; exact hz
    have hv := congrFun (congrArg (fun o => o.2.1) he) ⟨z, hz'⟩
    change ((g.exec X).config g.start).work g.free z = ((g.exec Y).config g.start).work g.free z at hv
    rw [c.prefix_eq X c.outer_start, c.prefix_eq Y c.outer_start]
    exact hv
  · intro r hr i hi z hz
    have hrT := (g.time_lt r (mem_filter.mp hr).1).le
    rw [c.prefix_eq X hrT, g.work_entry X r hr] at hz
    obtain ⟨j, hj⟩ := windowAddress_covers hz
    have hv := congrFun (congrFun (congrFun (congrArg (fun o => o.2.2) he) ⟨r, hr⟩) ⟨i, hi⟩) j
    change ((g.exec X).config r).work i (windowAddress (g.workEntry r i) g.radius j) =
      ((g.exec Y).config r).work i (windowAddress (g.workEntry r i) g.radius j) at hv
    rw [hj] at hv
    rw [c.prefix_eq X hrT, c.prefix_eq Y hrT]
    exact hv

end Completion
end NativeReplayClass
end AdaptiveTransfer
