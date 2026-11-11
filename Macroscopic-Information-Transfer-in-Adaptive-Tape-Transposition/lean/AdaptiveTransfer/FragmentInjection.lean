import AdaptiveTransfer.FragmentOutputs
import AdaptiveTransfer.FragmentAncestors

/-! The native fragment input injection. Parent closure below refers to actual
last global visits. The cut-witness application derives it from the literal
ancestor graph; no decoder or input injection is assumed. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape MergeDepth Finset LeanMachine BoundedNesting

namespace FragmentObservation
variable {M : TM} {P T : ℕ} {X Y : Fin P → Bool} {B : Finset ℕ}

/-- Actual latest-visit closure needed by chronological filtered memory. -/
def Parents (g : FragmentObservation M P T X B) : Prop :=
  ∀ t ∈ g.kept, ∀ i : Fin M.k, ∀ p < t,
    (run M (List.ofFn X) t).workPos i = (run M (List.ofFn X) p).workPos i →
    (∀ u, p < u → u < t →
      (run M (List.ofFn X) t).workPos i ≠ (run M (List.ofFn X) u).workPos i) → p ∈ g.kept ∪ B

/-- Equal actual full fragment records and the omitted-set exterior recover
the entire source. The two detailed native traces may be different. -/
theorem record_recovers_input (g : FragmentObservation M P T X B)
    (h : FragmentObservation M P T Y B) (π : Fin P → Fin P)
    (hpg : g.Parents) (hph : h.Parents)
    (hgout : (run M (List.ofFn X) g.finish).outRev.reverse = List.ofFn (fun j => X (π j)))
    (hhout : (run M (List.ofFn Y) h.finish).outRev.reverse = List.ofFn (fun j => Y (π j)))
    (he : g.encode = h.encode) (hext : ∀ p ∉ g.omitted π, X p = Y p) : X = Y := by
  classical
  have hfinish := encode_finish he
  have hK := encode_kept he
  let F : ExecutionPrefix M (List.ofFn Y) g.finish := ExecutionPrefix.ofRun M _ g.finish
    (fun t ht => h.active t (by simpa only [← hfinish] using ht))
  have hraw : ∀ t ∈ g.kept, (g.exec.config t).inPos = (F.config t).inPos →
      readInput (List.ofFn X) (g.exec.config t).inPos = readInput (List.ofFn Y) (F.config t).inPos := by
    intro t ht hpos
    rw [← hpos]
    apply readInput_eq_of_exterior (g.omitted π) (g.rawCells : Set ℤ) hext
      (fun p hp => g.raw_disjoint π p hp)
    change (run M (List.ofFn X) t).inPos ∈ g.rawCells
    rw [inPos_eq_input]
    exact mem_image_of_mem _ ht
  have hret := g.exec.fragment_replay_agreement F g.kept B g.kept_lt g.closed
    (fun _ hp => encode_cut_positions he hp)
    (fun p hp => encode_cut_instruction he ⟨p, hp⟩)
    hpg (fun t ht i p hpt hpos hlast => by
      have hh := hph t (hK ▸ ht) i p hpt hpos hlast
      simpa only [← hK] using hh) hraw
  have hfill : ∀ t ∈ g.kept, ∀ u, cutGapStart B t ≤ u → u ≤ t → u ∈ g.kept := by
    intro t ht u hau hut
    have htgap : t ∈ gapPrefix B g.kept (cutGapStart B t) := mem_filter.mpr ⟨ht, rfl⟩
    rw [gapPrefix_eq_Ico g.closed] at htgap
    have hugap : u ∈ gapPrefix B g.kept (cutGapStart B t) := by
      rw [gapPrefix_eq_Ico g.closed]
      exact mem_Ico.mpr ⟨hau, hut.trans_lt (mem_Ico.mp htgap).2⟩
    exact (mem_filter.mp hugap).1
  have hcountK := g.exec.replay_output_count_agreement F g.kept (cutGapStart B) g.kept_lt
    (fun t _ht => cutGapStart_le B t) hfill
    (fun t _ht => encode_gap_counter he ⟨cutGapStart B t, cutGapStart_mem B t⟩)
    (fun t ht => (hret t ht).2)
  apply g.exec.replay_recovers_input F π (g.kept ∪ B) (g.omitted π)
  · intro t ht
    rcases mem_union.mp ht with htK | htB
    · exact g.kept_lt t htK
    · exact g.cut_lt t htB
  · exact fun p hp => g.omitted_cover π hp
  · intro t ht
    rcases mem_union.mp ht with htK | htB
    · exact hcountK t htK
    · exact encode_cut_counter he ⟨t, htB⟩
  · intro t ht
    rcases mem_union.mp ht with htK | htB
    · exact (hret t htK).2
    · exact encode_cut_instruction he ⟨t, htB⟩
  · intro t ht j bit hc ho
    exact g.exec.output_correct π le_rfl hgout ht j bit hc ho
  · intro t ht j bit hc ho
    apply F.output_correct π le_rfl _ ht j bit hc ho
    rw [hfinish]
    exact hhout
  · exact hext

end FragmentObservation
end AdaptiveTransfer
