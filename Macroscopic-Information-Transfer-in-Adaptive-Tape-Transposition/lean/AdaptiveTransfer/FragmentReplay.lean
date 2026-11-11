import AdaptiveTransfer.AdaptiveReplay
import AdaptiveTransfer.Fragments

/-! Actual-run fragment reconstruction by chronological filtered dictionaries.
Paid cut instructions reset the next control; only actual latest parents are
needed at retained reads. Detailed traces outside the retained fragments may
be different. -/

namespace AdaptiveTransfer
open Transpose Finset

private theorem memoryAfter_eq_of_kept_events {Cell Symbol : Type*} [DecidableEq Cell]
    (initial : Cell → Symbol) (addr addr' : ℕ → Cell) (value value' : ℕ → Symbol)
    (keep : ℕ → Bool) (t : ℕ)
    (hevents : ∀ u < t, keep u = true → addr u = addr' u ∧ value u = value' u) :
    memoryAfter initial addr value keep t = memoryAfter initial addr' value' keep t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (fun u hu hk => hevents u (by omega) hk)
    funext z
    by_cases hk : keep t = true
    · have hh := hevents t (by omega) hk
      simp only [memoryAfter, hk, Bool.true_and, hh.1, hh.2, hp]
    · have hk' : keep t = false := Bool.eq_false_iff.mpr hk
      simp only [memoryAfter, hk', Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]

namespace ExecutionPrefix
variable {M : TM} {w v : List Bool} {T : ℕ}

/-- Pairwise native fragment replay. The parent premises are actual last-visit
closure; the cut premises are equality of actual paid positions/instructions.
No input injectivity or common trace is assumed. -/
theorem fragment_replay_agreement (E : ExecutionPrefix M w T) (F : ExecutionPrefix M v T)
    (K B : Finset ℕ) (hKT : ∀ t ∈ K, t < T) (hclosed : StateClosedExcept K B)
    (hcutpos : ∀ t ∈ B, (E.config t).inPos = (F.config t).inPos ∧
      (E.config t).workPos = (F.config t).workPos)
    (hcutinstr : ∀ t ∈ B,
      nativeInstruction M w (E.config t) = nativeInstruction M v (F.config t))
    (hparentE : ∀ t ∈ K, ∀ h, ∀ p < t,
      (E.config t).workPos h = (E.config p).workPos h →
      (∀ u, p < u → u < t → (E.config t).workPos h ≠ (E.config u).workPos h) → p ∈ K ∪ B)
    (hparentF : ∀ t ∈ K, ∀ h, ∀ p < t,
      (F.config t).workPos h = (F.config p).workPos h →
      (∀ u, p < u → u < t → (F.config t).workPos h ≠ (F.config u).workPos h) → p ∈ K ∪ B)
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
        · have huK : u ∈ K := by
            simpa only [Nat.add_sub_cancel] using hclosed (u + 1) htK (by omega) (by simpa using huB)
          have hu := ih u (by omega) huK
          exact (step_record_agreement (E.successful u (by omega)) (F.successful u (by omega))
            hu.1 hu.2).1
    have hreads : ∀ h, (E.config t).work h ((E.config t).workPos h) =
        (F.config t).work h ((F.config t).workPos h) := by
      intro h
      let keep (u : ℕ) := decide (u ∈ K ∪ B)
      have hmem := memoryAfter_eq_of_kept_events (fun _ : ℤ => (0 : Fin (M.g + 1)))
        (fun u => (E.config u).workPos h) (fun u => (F.config u).workPos h)
        (E.written h) (F.written h) keep t (fun u hut hkeep => ?_)
      · have he := E.filtered_native_read keep h htT.le (fun p hpt hpos hlast => by
          exact decide_eq_true (hparentE t htK h p hpt hpos hlast))
        have hf := F.filtered_native_read keep h htT.le (fun p hpt hpos hlast => by
          exact decide_eq_true (hparentF t htK h p hpt hpos hlast))
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
