import AdaptiveTransfer.LocalClassData
import AdaptiveTransfer.LocalInjection

/-! Actual localized cut observations inside a native replay class. Ordinary
records are reused without charging or using the class's import fields. The
separator and every parent/root obligation refer to the original full run. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset NativeRelations

namespace NativeReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : NativeReplayClass M P π)

structure LocalCut (X : g.inputs) where
  cut : Finset ℕ
  cut_lt : ∀ t ∈ cut, t < g.finish X
  separates : IsMengerVertexCut (trace M (List.ofFn X.val)).work (g.finish X)
    (nativeDemandedOutputSteps M X.val (g.finish X) π g.omitted)
    (offCarrierLowerEndpoints (trace M (List.ofFn X.val)).work g.free (g.finish X) g.radius) cut

namespace LocalCut
variable {g} {X : g.inputs} (w : g.LocalCut X)

theorem roots_separator : IsMengerVertexCut (trace M (List.ofFn X.val)).work (g.finish X)
    (g.localRoots X) (offCarrierLowerEndpoints (trace M (List.ofFn X.val)).work
      g.free (g.finish X) g.radius) w.cut := by
  intro ρ r hr hpath htarget
  exact w.separates ρ r (g.localRoots_subset_outputs X hr) hpath htarget

noncomputable def observation (c : g.Completion) (N : ℕ) (hN : (runStarts g.times).card ≤ N) :
    LocalFragmentObservation M P g.limit N X.val g.times w.cut where
  finish := g.finish X
  finish_le := c.finish_le X
  active := c.active X
  kept := localAncestors (trace M (List.ofFn X.val)).work (g.finish X) (g.localRoots X) g.times w.cut
  closed := localAncestors_closed _ _ _ _
  chunk_lt := fun t ht => (g.time_lt t ht).trans_le (g.finish_ge X)
  cut_lt := w.cut_lt
  run_cap := hN
  count_le := by
    have hh := congrArg List.length (g.output X)
    simp only [List.length_reverse, List.length_ofFn] at hh
    exact hh.le

theorem snapshot_parents (c : g.Completion) (N : ℕ) (hN : (runStarts g.times).card ≤ N) :
    (w.observation c N hN).SnapshotParents
      ((c.fullExec X).localSnapshot g.times g.cells g.start g.radius g.free) := by
  intro t ht i p hpt hpos hlast
  have hw : (fun h u => ((c.fullExec X).config u).workPos h) = (trace M (List.ofFn X.val)).work := by
    funext h u
    exact workPos_eq_work h u
  have hcarrier : ∀ u, g.start ≤ u → u < g.horizon →
      (u ∈ g.times ↔ ((c.fullExec X).config u).workPos g.free ∈ g.cells) := by
    intro u hau hub
    rw [c.prefix_eq X hub.le]
    exact g.carrier X u hau hub
  have hh := (c.fullExec X).localSnapshot_parent_coverage g.times (g.localRoots X) w.cut g.cells
    g.start g.horizon g.radius g.free (fun u hu => ⟨g.time_start u hu, g.time_lt u hu⟩)
    (g.finish_ge X) hcarrier (by simpa only [hw] using w.roots_separator)
    (by simpa only [hw, observation] using ht) i hpt hpos hlast
  rw [hw] at hh
  simpa only [observation, Completion.fullExec, ExecutionPrefix.ofRun_config] using hh

theorem output_cover (c : g.Completion) (N : ℕ) (hN : (runStarts g.times).card ≤ N)
    {p : Fin P} (hp : p ∈ g.omitted) :
    ∃ t ∈ (w.observation c N hN).kept ∪ w.cut, ∃ j : Fin P,
      π j = p ∧ (((w.observation c N hN).exec).config t).outRev.length = j.val ∧
        (((w.observation c N hN).exec).emitted t).isSome := by
  let p' : g.omitted := ⟨p, hp⟩
  let t := g.localRootTime X p'
  obtain ⟨htC, j, hj, hc, ho⟩ := g.localRootTime_spec X p'
  have htroot : t ∈ g.localRoots X := mem_image.mpr ⟨p', mem_univ _, rfl⟩
  have htT := g.time_lt t htC
  have htkept := root_mem_cut_or_localAncestors (xs := (trace M (List.ofFn X.val)).work)
    (B := w.cut) htroot (htT.trans_le (g.finish_ge X)) htC
  rw [(g.exec X).config_eq_run htT.le] at hc
  rw [(g.exec X).emitted_eq_outBit htT.le] at ho
  exact ⟨t, htkept, j, hj, hc, ho⟩

/-- Derived actual native input injection for two input-dependent cuts with
matching finite local geometry, full cut payload and ordinary records. -/
theorem records_recover (c : g.Completion) (N : ℕ) (hN : (runStarts g.times).card ≤ N)
    {X Y : g.inputs} (wX : g.LocalCut X) (wY : g.LocalCut Y)
    (hB : wX.cut = wY.cut)
    (he : HEq (wX.observation c N hN).encode (wY.observation c N hN).encode)
    (ho : g.ordinary X = g.ordinary Y)
    (hext : ∀ p ∉ g.omitted, X.val p = Y.val p) : X = Y := by
  rcases wX with ⟨B, hBT, hsep⟩
  rcases wY with ⟨B', hB'T, hsep'⟩
  change B = B' at hB
  subst B'
  let wX : g.LocalCut X := ⟨B, hBT, hsep⟩
  let wY : g.LocalCut Y := ⟨B, hB'T, hsep'⟩
  let aX := wX.observation c N hN
  let aY := wY.observation c N hN
  have henc : aX.encode = aY.encode := eq_of_heq he
  apply Subtype.ext
  apply LocalFragmentObservation.record_recovers_input aX aY π g.omitted
    (I := rawExtent g.times g.rawLo g.rawHi)
    ((c.fullExec X).localSnapshot g.times g.cells g.start g.radius g.free)
    ((c.fullExec Y).localSnapshot g.times g.cells g.start g.radius g.free)
  · intro i u _hu z a ha
    exact (c.fullExec X).localSnapshot_sound g.times g.cells g.start g.radius g.free i u z a ha
  · intro i u _hu z a ha
    exact (c.fullExec Y).localSnapshot_sound g.times g.cells g.start g.radius g.free i u z a ha
  · exact fun i u _hu => c.ordinary_snapshots ho i u
  · exact wX.snapshot_parents c N hN
  · exact wY.snapshot_parents c N hN
  · exact fun t ht => c.ordinary_controls ho ht
  · intro t ht
    have htC : t ∈ g.times := aX.closed.1 ht
    have hh := rawExtent_contains_reads (g.exec X) g.times g.time_lt g.rawLo g.rawHi (g.extrema X) t htC
    rwa [(g.exec X).config_eq_run (g.time_lt t htC).le] at hh
  · exact geometryOmitted_raw_disjoint π g.times g.outLo g.outHi g.rawLo g.rawHi
  · exact fun p hp => wX.output_cover c N hN hp
  · exact g.output X
  · exact g.output Y
  · exact henc
  · exact hext

end LocalCut
end NativeReplayClass
end AdaptiveTransfer
