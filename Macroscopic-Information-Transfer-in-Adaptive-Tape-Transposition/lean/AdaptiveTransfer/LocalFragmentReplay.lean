import AdaptiveTransfer.FragmentReplay
import AdaptiveTransfer.SnapshotMemory

/-! Native replay of fragments inside a selected chunk, with original entry
controls and true pre-step overlays. The actual latest-parent obligation is
localized; arbitrary dictionary cells need not remain globally correct. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations

namespace ExecutionPrefix
variable {M : TM} {w v : List Bool} {T : ℕ}

/-- Pairwise native localized replay. Snapshot soundness and last-parent
coverage are separate semantic obligations, proved from actual snapshots and
the full original cut in the native application. -/
theorem local_fragment_replay_agreement (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    (C K B : Finset ℕ) (hKT : ∀ t ∈ K, t < T) (hclosed : LocallyStateClosedExcept C K B)
    (hentry : ∀ t ∈ runStarts C, SameControl (E.config t) (F.config t))
    (hcutpos : ∀ t ∈ B, (E.config t).inPos = (F.config t).inPos ∧
      (E.config t).workPos = (F.config t).workPos)
    (hcutinstr : ∀ t ∈ B,
      nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t))
    (snapshotE snapshotF : Fin M.k → ℕ → ℤ → Option (Fin (M.g + 1)))
    (hsnapE : ∀ h u, u ≤ T → ∀ z a, snapshotE h u z = some a → a = (E.config u).work h z)
    (hsnapF : ∀ h u, u ≤ T → ∀ z a, snapshotF h u z = some a → a = (F.config u).work h z)
    (hsame : ∀ h u, u ≤ T → snapshotE h u = snapshotF h u)
    (hparentE : ∀ t ∈ K, ∀ h, ∀ p < t,
      (E.config t).workPos h = (E.config p).workPos h →
      (∀ u, p < u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) →
      p ∈ K ∪ B ∨ ∃ s, p < s ∧ s ≤ t ∧ (snapshotE h s ((E.config t).workPos h)).isSome)
    (hparentF : ∀ t ∈ K, ∀ h, ∀ p < t,
      (F.config t).workPos h = (F.config p).workPos h →
      (∀ u, p < u → u < t → (F.config t).workPos h ≠ (F.config u).workPos h) →
      p ∈ K ∪ B ∨ ∃ s, p < s ∧ s ≤ t ∧ (snapshotF h s ((F.config t).workPos h)).isSome)
    (hraw : ∀ t ∈ K, (E.config t).inPos = (F.config t).inPos →
      readInput w (E.config t).inPos = readInput v (F.config t).inPos) :
    ∀ t ∈ K, SameControl (E.config t) (F.config t) ∧
      nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t) := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro htK
    have htT := hKT t htK
    have hcontrol : SameControl (E.config t) (F.config t) := by
      cases t with
      | zero => rw [E.initial, F.initial]; exact ⟨rfl, rfl, rfl⟩
      | succ u =>
        by_cases huB : u ∈ B
        · exact (step_positions_instruction_agreement (E.successful u (by omega))
            (F.successful u (by omega)) (hcutpos u huB).1 (hcutpos u huB).2 (hcutinstr u huB)).1
        · by_cases huC : u ∈ C
          · have huK : u ∈ K := by
              simpa only [Nat.add_sub_cancel] using hclosed.2 (u + 1) htK (by omega)
                (by simpa only [Nat.add_sub_cancel] using huC)
                (by simpa only [Nat.add_sub_cancel] using huB)
            have hu := ih u (by omega) huK
            exact (step_record_agreement (E.successful u (by omega)) (F.successful u (by omega))
              hu.1 hu.2).1
          · exact hentry (u + 1) (mem_filter.mpr ⟨hclosed.1 htK, Or.inr
              (by simpa only [Nat.add_sub_cancel] using huC)⟩)
    have hreads : ∀ h, (E.config t).work h ((E.config t).workPos h) =
        (F.config t).work h ((F.config t).workPos h) := by
      intro h
      let keep (u : ℕ) := decide (u ∈ K ∪ B)
      have hmem := snapshotMemory_congr (fun _ : ℤ => (0 : Fin (M.g + 1)))
        (fun u => (E.config u).workPos h) (fun u => (F.config u).workPos h)
        (E.written h) (F.written h) keep (snapshotE h) (snapshotF h) t
        (fun u hu => hsame h u (hu.trans htT.le)) (fun u hut hkeep => ?_)
      · have he := E.snapshot_native_read keep (snapshotE h) h htT.le
          (fun u hu z a ha => hsnapE h u (hu.trans htT.le) z a ha) (fun p hpt hpos hlast => by
            simpa only [keep, decide_eq_true_eq] using hparentE t htK h p hpt hpos hlast)
        have hf := F.snapshot_native_read keep (snapshotF h) h htT.le
          (fun u hu z a ha => hsnapF h u (hu.trans htT.le) z a ha) (fun p hpt hpos hlast => by
            simpa only [keep, decide_eq_true_eq] using hparentF t htK h p hpt hpos hlast)
        rw [← he, ← hf, hmem, congrFun hcontrol.2.2 h]
      · have hu : u ∈ K ∪ B := of_decide_eq_true hkeep
        rcases mem_union.mp hu with huK | huB
        · have hu := ih u hut huK
          exact ⟨congrFun hu.1.2.2 h,
            (step_record_agreement (E.successful u (hut.trans htT))
              (F.successful u (hut.trans htT)) hu.1 hu.2).2 h⟩
        · exact ⟨congrFun (hcutpos u huB).2 h,
            (step_positions_instruction_agreement (E.successful u (hut.trans htT))
              (F.successful u (hut.trans htT)) (hcutpos u huB).1 (hcutpos u huB).2
              (hcutinstr u huB)).2 h⟩
    exact ⟨hcontrol, instruction_eq_of_old_tuple hcontrol.1 (hraw t htK hcontrol.2.1) hreads⟩

end ExecutionPrefix
end AdaptiveTransfer
