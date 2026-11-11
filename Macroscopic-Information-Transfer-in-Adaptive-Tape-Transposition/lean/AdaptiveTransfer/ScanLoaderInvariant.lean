import AdaptiveTransfer.ScanLoaderConsumer

/-! The actual reached configurations of the paid loader. Consumer archive
preservation is a local transition-table condition; correctness of every
archive read, including preparation, is derived from the native execution.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose

variable {r : ℕ} {S A : Fin r → Type*} {Q B : Type*}
variable (F : (j : Fin r) → S j → Bool → S j)
  (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
  (C : Consumer Q A B)

/-- Every archive write preserves the symbol read in that same transition.
The carrier, states, moves and output are otherwise unrestricted. -/
def PreservesArchives : Prop :=
  ∀ q raw old instruction, C q raw old = some instruction →
    ∀ j : Fin r, (instruction.2.2.1 j.succ).1 = old j.succ

def completedPhase : Phase Q (ScanStates S) → Bool
  | some (some none) => true
  | some (some (some (.inl _))) => true
  | _ => false

/-- Exact phase alternatives sufficient for all old archive reads. -/
def ArchiveInvariant (w : List Bool)
    (c : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1)) : Prop :=
  c = initial start blank ∨ c = markConfig ∨
    (∃ i ≤ w.length, c = loadConfig F D s₀ w i) ∨
    (completedPhase c.state = true ∧
      ∀ (j : Fin r) z, c.work j.succ z = archive F D s₀ w j z)

private theorem next_memory {L : Type*} {δ : Table L (Symbol A B) (r + 1)}
    {w : List Bool} {c e : Config L (Symbol A B) (r + 1)}
    (h : next δ w c = some e)
    (hp : ∀ instruction, δ c.state (readInput w c.inPos)
      (fun i => c.work i (c.workPos i)) = some instruction →
      ∀ j : Fin r, (instruction.2.2.1 j.succ).1 = c.work j.succ (c.workPos j.succ)) :
    ∀ (j : Fin r) z, e.work j.succ z = c.work j.succ z := by
  unfold next at h
  cases hi : δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => simp [hi] at h
  | some instruction =>
    rcases instruction with ⟨q, move, acts, out⟩
    simp only [hi, Option.some.injEq] at h
    subst e
    intro j z
    dsimp
    rw [hp _ hi j]
    split <;> rename_i hz
    · rw [hz]
    · rfl

theorem archiveInvariant_next (hC : PreservesArchives C) {w : List Bool}
    {c e : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1)}
    (hc : ArchiveInvariant F D s₀ w c)
    (he : next (table F D s₀ q₀ C) w c = some e) :
    ArchiveInvariant F D s₀ w e := by
  rcases hc with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨hphase, hmem⟩
  · rw [start_step] at he
    exact Or.inr (Or.inl (Option.some.inj he.symm))
  · rw [mark_step] at he
    exact Or.inr (Or.inr (Or.inl ⟨0, Nat.zero_le _, Option.some.inj he.symm⟩))
  · by_cases hlt : i < w.length
    · rw [load_step F D s₀ q₀ C w i hlt] at he
      exact Or.inr (Or.inr (Or.inl ⟨i + 1, by omega, Option.some.inj he.symm⟩))
    · have hiw : i = w.length := by omega
      subst i
      rw [eof_step] at he
      have heq := Option.some.inj he.symm
      subst e
      exact Or.inr (Or.inr (Or.inr ⟨rfl, fun _ _ => rfl⟩))
  · have hp : ∀ instruction, table F D s₀ q₀ C c.state (readInput w c.inPos)
        (fun i => c.work i (c.workPos i)) = some instruction →
        completedPhase instruction.1 = true ∧
        ∀ j : Fin r, (instruction.2.2.1 j.succ).1 = c.work j.succ (c.workPos j.succ) := by
      cases hs : c.state with
      | none => simp [hs, completedPhase] at hphase
      | some a =>
        cases a with
        | none => simp [hs, completedPhase] at hphase
        | some a =>
          cases a with
          | none =>
            intro instruction hinstruction
            cases hr : readInput w c.inPos <;>
              simp only [table, hr, Option.some.injEq] at hinstruction <;>
              subst instruction <;> exact ⟨rfl, fun _ => rfl⟩
          | some a =>
            cases a with
            | inr s => simp [hs, completedPhase] at hphase
            | inl q =>
              intro instruction hinstruction
              simp only [table] at hinstruction
              cases hci : C q (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
              | none => simp [hci] at hinstruction
              | some ci =>
                rcases ci with ⟨q', move, acts, out⟩
                simp only [hci, Option.map_some, Option.some.injEq] at hinstruction
                subst instruction
                exact ⟨rfl, hC _ _ _ _ hci⟩
    have hmemory := next_memory he (fun i hi => (hp i hi).2)
    have hphase' : completedPhase e.state = true := by
      unfold next at he
      cases hi : table F D s₀ q₀ C c.state (readInput w c.inPos)
          (fun i => c.work i (c.workPos i)) with
      | none => simp [hi] at he
      | some instruction =>
        rcases instruction with ⟨q, move, acts, out⟩
        simp only [hi, Option.some.injEq] at he
        subst e
        exact (hp _ hi).1
    exact Or.inr (Or.inr (Or.inr ⟨hphase', fun j z => (hmemory j z).trans (hmem j z)⟩))

theorem archiveInvariant_old {w : List Bool}
    {c : Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1)}
    (hc : ArchiveInvariant F D s₀ w c) (j : Fin r) :
    c.work j.succ (c.workPos j.succ) =
      if completedPhase c.state then archive F D s₀ w j (c.workPos j.succ) else blank := by
  rcases hc with rfl | rfl | ⟨i, _, rfl⟩ | ⟨hphase, hmem⟩
  · rfl
  · rfl
  · exact load_scanned_blank F D s₀ w i j
  · simpa only [hphase, Bool.true_eq, ↓reduceIte] using hmem j (c.workPos j.succ)

section Native
variable [Fintype Q] [∀ j, Fintype (S j)] [∀ j, Fintype (A j)] [Fintype B]

/-- The actual frozen native run has a typed invariant witness at every time,
including after halt. No simulator relation is assumed. -/
theorem native_archiveInvariant (hC : PreservesArchives C) (w : List Bool) (t : ℕ) :
    ∃ c, Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t =
      denote start blank (table F D s₀ q₀ C) c ∧ ArchiveInvariant F D s₀ w c := by
  induction t with
  | zero => exact ⟨initial start blank, (denote_initial _ _ _).symm, Or.inl rfl⟩
  | succ t ih =>
    obtain ⟨c, hc, hi⟩ := ih
    change ∃ e, (Transpose.step _ w (Transpose.Tape.run _ w t)).getD
      (Transpose.Tape.run _ w t) = _ ∧ _
    rw [hc]
    unfold nativeProducer
    rw [step_denote]
    cases hn : next (table F D s₀ q₀ C) w c with
    | none => exact ⟨c, rfl, hi⟩
    | some e => exact ⟨e, rfl, archiveInvariant_next F D s₀ q₀ C hC hi hn⟩

theorem native_old_archive (hC : PreservesArchives C) (w : List Bool) (t : ℕ) (j : Fin r) :
    let c := Transpose.Tape.run (nativeProducer F D s₀ q₀ C) w t
    c.work j.succ (c.workPos j.succ) = pointCode (blank (A := A) (B := B))
      (if completedPhase ((pointCode (start (Q := Q) (S := S))).symm c.state)
      then archive F D s₀ w j (c.workPos j.succ) else blank) := by
  obtain ⟨c, hc, hi⟩ := native_archiveInvariant F D s₀ q₀ C hC w t
  dsimp only
  rw [hc]
  simp only [denote, Equiv.symm_apply_apply]
  exact congrArg (pointCode blank) (archiveInvariant_old F D s₀ hi j)

end Native
end AdaptiveTransfer.ScanLoader
