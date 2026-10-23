import BitWord.NativeLoggedUndoFrame

/-! A literal finite scan of the one-hot history tracks finds the exact record. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

noncomputable def foundBefore (r : Record T L) (n : ℕ) : Option (Record T L) :=
  if ((Fintype.equivFin (Record T L)) r).val < n then some r else none

theorem foundBefore_succ (r : Record T L) (i : Fin (Fintype.card (Record T L))) :
    (if r=historyPort i then some (historyPort i) else foundBefore r i.val) =
      foundBefore r (i.val+1) := by
  have hindex : r=historyPort i ↔ (Fintype.equivFin (Record T L)) r=i := by
    constructor
    · intro he
      rw [he]
      exact (Fintype.equivFin (Record T L)).apply_symm_apply i
    · intro he
      apply (Fintype.equivFin (Record T L)).injective
      rw [he]
      exact ((Fintype.equivFin (Record T L)).apply_symm_apply i).symm
  by_cases he : r=historyPort i
  · have hi := congrArg Fin.val (hindex.mp he)
    rw [ite_eq_left he,foundBefore,ite_eq_left (by omega)]
    exact congrArg some he.symm
  · have hi : ((Fintype.equivFin (Record T L)) r).val ≠ i.val := by
      intro h
      exact he (hindex.mpr (Fin.ext h))
    have hi' : ((Fintype.equivFin (Record T L)) r).val < i.val+1 ↔
        ((Fintype.equivFin (Record T L)) r).val < i.val := by omega
    simp only [ite_eq_right he,foundBefore,hi']

theorem scan_log_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (r : Record T L) (history : List (Record T L))
    (found : Option (Record T L)) (i : Fin (Fintype.card (Record T L))) :
    NativeMicrocode.step (program p keep initial)
      (atRecord (.scanLog found ⟨i.val,by omega⟩) c r history) =
      atRecord (.scanLog (if r=historyPort i then some (historyPort i) else found)
        ⟨i.val+1,by omega⟩) c r history := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,atRecord,
    dite_eq_left i.isLt]
  by_cases he : r=historyPort i <;> simp [Turing.Tape.mk₂,he]

theorem scan_record (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (r : Record T L) (history : List (Record T L))
    (n : ℕ) (hn : n≤Fintype.card (Record T L)) :
    Trace p keep initial n
      (atRecord (.scanLog (foundBefore r (Fintype.card (Record T L)-n))
        ⟨Fintype.card (Record T L)-n,by omega⟩) c r history)
      (atRecord (.scanLog (some r) (Fin.last (Fintype.card (Record T L)))) c r history) := by
  induction n with
  | zero =>
    have he : foundBefore r (Fintype.card (Record T L))=some r := by
      exact ite_eq_left ((Fintype.equivFin (Record T L)) r).isLt
    simpa only [Nat.sub_zero,he,Fin.last] using
      (OperationalTrace.Trace.refl (atRecord (.scanLog (some r)
        (Fin.last (Fintype.card (Record T L)))) c r history))
  | succ n ih =>
    have hi : Fintype.card (Record T L)-(n+1)<Fintype.card (Record T L) := by omega
    have he : Fintype.card (Record T L)-(n+1)+1=Fintype.card (Record T L)-n := by omega
    apply OperationalTrace.Trace.cons
    · simp only [NativeMicrocode.Active,program,atRecord,dite_eq_left hi]
      simp
    · rw [scan_log_step p keep initial c r history _ ⟨_,hi⟩,foundBefore_succ]
      simpa only [he] using ih (by omega)

/-- This includes the final branch from the completed track scan to undo. -/
theorem read_record (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (r : Record T L) (history : List (Record T L)) :
    Trace p keep initial (Fintype.card (Record T L)+1)
      (atRecord (.scanLog none 0) c r history) (atRecord (.unmove r) c r history) := by
  have hs := scan_record p keep initial c r history (Fintype.card (Record T L)) le_rfl
  have hj : Trace p keep initial 1
      (atRecord (.scanLog (some r) (Fin.last (Fintype.card (Record T L)))) c r history)
      (atRecord (.unmove r) c r history) := by
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,atRecord]
    · have he : NativeMicrocode.step (program p keep initial)
          (atRecord (.scanLog (some r) (Fin.last (Fintype.card (Record T L)))) c r history) =
          atRecord (.unmove r) c r history := by
        simp [NativeMicrocode.step,Microcode.actualStep,program,atRecord]
      rw [he]
      exact .refl _
  have hz : (⟨0,Nat.zero_lt_succ (Fintype.card (Record T L))⟩ :
      Fin (Fintype.card (Record T L)+1)) = 0 := by
    apply Fin.ext
    simp
  simpa only [Nat.sub_self,foundBefore,lt_self_iff_false,not_lt_zero,↓reduceIte,hz] using
    NativeCountedLoop.trace_trans hs hj
end BitWord.NativeLogged
