import AdaptiveTransfer.LocalGeometry
import AdaptiveTransfer.LocalFragmentReplay

/-! Input recovery from actual localized records and true paid snapshots.
This pairwise lemma is used only after deriving root coverage and latest-parent
coverage from the native selected chunk and its original full-graph cut. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape Finset NativeRelations

namespace LocalFragmentObservation
variable {M : TM} {P T N : ℕ} {X Y : Fin P → Bool} {C B : Finset ℕ}

def SnapshotParents (g : LocalFragmentObservation M P T N X C B)
    (snapshot : Fin M.k → ℕ → ℤ → Option (Fin (M.g + 1))) : Prop :=
  ∀ t ∈ g.kept, ∀ i : Fin M.k, ∀ p < t,
    (run M (List.ofFn X) t).workPos i = (run M (List.ofFn X) p).workPos i →
    (∀ u, p < u → u < t →
      (run M (List.ofFn X) t).workPos i ≠ (run M (List.ofFn X) u).workPos i) →
    p ∈ g.kept ∪ B ∨ ∃ s, p < s ∧ s ≤ t ∧ (snapshot i s ((run M (List.ofFn X) t).workPos i)).isSome

theorem record_recovers_input (g : LocalFragmentObservation M P T N X C B)
    (h : LocalFragmentObservation M P T N Y C B) (π : Fin P → Fin P) (U : Finset (Fin P))
    (snapshotX snapshotY : Fin M.k → ℕ → ℤ → Option (Fin (M.g + 1)))
    (hsoundX : ∀ i u, u ≤ g.finish → ∀ z a, snapshotX i u z = some a →
      a = (run M (List.ofFn X) u).work i z)
    (hsoundY : ∀ i u, u ≤ h.finish → ∀ z a, snapshotY i u z = some a →
      a = (run M (List.ofFn Y) u).work i z)
    (hsame : ∀ i u, u ≤ g.finish → snapshotX i u = snapshotY i u)
    (hpg : g.SnapshotParents snapshotX) (hph : h.SnapshotParents snapshotY)
    (hentry : ∀ t ∈ runStarts C, SameControl (run M (List.ofFn X) t) (run M (List.ofFn Y) t))
    (I : Set ℤ) (hraw : ∀ t ∈ g.kept, (run M (List.ofFn X) t).inPos ∈ I)
    (hdisjoint : ∀ p : Fin P, (p.val : ℤ) ∈ I → p ∉ U)
    (hcover : ∀ p ∈ U, ∃ t ∈ g.kept ∪ B, ∃ j : Fin P,
      π j = p ∧ (g.exec.config t).outRev.length = j.val ∧ (g.exec.emitted t).isSome)
    (hgout : (run M (List.ofFn X) g.finish).outRev.reverse = List.ofFn (fun j => X (π j)))
    (hhout : (run M (List.ofFn Y) h.finish).outRev.reverse = List.ofFn (fun j => Y (π j)))
    (he : g.encode = h.encode) (hext : ∀ p ∉ U, X p = Y p) : X = Y := by
  classical
  have hfinish := encode_finish he
  have hK := encode_kept he
  let F : ExecutionPrefix M (List.ofFn Y) g.finish := ExecutionPrefix.ofRun M _ g.finish
    (fun t ht => h.active t (by simpa only [← hfinish] using ht))
  have hraw' : ∀ t ∈ g.kept, (g.exec.config t).inPos = (F.config t).inPos →
      readInput (List.ofFn X) (g.exec.config t).inPos = readInput (List.ofFn Y) (F.config t).inPos := by
    intro t ht hpos
    rw [← hpos]
    exact readInput_eq_of_exterior U I hext hdisjoint (hraw t ht)
  have hret := g.exec.local_fragment_replay_agreement F C g.kept B g.kept_lt g.closed hentry
    (fun _ hp => encode_cut_positions he hp) (fun p hp => encode_cut_instruction he ⟨p, hp⟩)
    snapshotX snapshotY hsoundX (fun i u hu z a ha => hsoundY i u (by rwa [← hfinish]) z a ha)
    hsame hpg (fun t ht i p hpt hpos hlast => by
      have hh := hph t (hK ▸ ht) i p hpt hpos hlast
      simpa only [← hK, F, ExecutionPrefix.ofRun_config] using hh) hraw'
  let A := localGapStarts C B
  let entry := cutGapStart (startCuts A)
  have hstarts : runStarts g.kept ⊆ A := local_starts_subset g.closed
  have hclosed := stateClosedExcept_startCuts hstarts
  have hfill : ∀ t ∈ g.kept, ∀ u, entry t ≤ u → u ≤ t → u ∈ g.kept := by
    intro t ht u hau hut
    have htgap : t ∈ gapPrefix (startCuts A) g.kept (entry t) := mem_filter.mpr ⟨ht, rfl⟩
    rw [gapPrefix_eq_Ico hclosed] at htgap
    have hugap : u ∈ gapPrefix (startCuts A) g.kept (entry t) := by
      rw [gapPrefix_eq_Ico hclosed]
      exact mem_Ico.mpr ⟨hau, hut.trans_lt (mem_Ico.mp htgap).2⟩
    exact (mem_filter.mp hugap).1
  have hcountK := g.exec.replay_output_count_agreement F g.kept entry g.kept_lt
    (fun t _ht => cutGapStart_le (startCuts A) t) hfill
    (fun t ht => encode_entry_counter he ⟨entry t, cutGapStart_mem_starts hstarts g.kept_lt ht⟩)
    (fun t ht => (hret t ht).2)
  apply g.exec.replay_recovers_input F π (g.kept ∪ B) U
  · intro t ht
    rcases mem_union.mp ht with htK | htB
    · exact g.kept_lt t htK
    · exact g.cut_lt t htB
  · exact hcover
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

end LocalFragmentObservation
end AdaptiveTransfer
