import BitWord.NativeLoggedFrame

/-! Forward refinement and literal history recording for the finite logger. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

theorem scan_source (p : Microcode.Program T L) (keep : T → Bool) (initial pc : L)
    (c : SourceConfig (T := T) (L := L)) (history : List (Record T L))
    (r : ℕ) (hr : r≤Fintype.card T) (seen : T → Sym Bool)
    (hseen : ∀ i : Fin (Fintype.card T), i.val<Fintype.card T-r →
      seen (sourcePort i)=(c.core.tapes (sourcePort i)).head) :
    Trace p keep initial r
      (loaded (.scan pc seen ⟨Fintype.card T-r,by omega⟩) c history)
      (loaded (.scan pc (fun t => (c.core.tapes t).head) (Fin.last (Fintype.card T))) c history) := by
  induction r generalizing seen with
  | zero =>
    have he : seen=fun t => (c.core.tapes t).head := by
      funext t
      simpa [sourcePort] using hseen ((Fintype.equivFin T) t) (by simp)
    subst seen
    simpa only [Nat.sub_zero,Fin.last] using (OperationalTrace.Trace.refl
      (loaded (.scan pc (fun t => (c.core.tapes t).head) (Fin.last (Fintype.card T))) c history))
  | succ r ih =>
    have hn : Fintype.card T-(r+1)<Fintype.card T := by omega
    let i : Fin (Fintype.card T) := ⟨Fintype.card T-(r+1),hn⟩
    let seen' := Function.update seen (sourcePort i) (c.core.tapes (sourcePort i)).head
    have he : Fintype.card T-(r+1)+1=Fintype.card T-r := by omega
    have hs : NativeMicrocode.step (program p keep initial)
      (loaded (.scan pc seen ⟨Fintype.card T-(r+1),by omega⟩) c history)=
      loaded (.scan pc seen' ⟨Fintype.card T-r,by omega⟩) c history := by
      simp [NativeMicrocode.step,Microcode.actualStep,program,loaded,bank,hn,seen',i,he]
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,loaded,hn]
    · rw [hs]
      apply ih (by omega) seen'
      intro j hj
      by_cases hji : j=i
      · subst j; simp [seen']
      · have hne : sourcePort j ≠ sourcePort i := by
          intro h; apply hji; exact (Fintype.equivFin T).symm.injective h
        simp only [seen',Function.update_of_ne hne]
        apply hseen j
        have hjn : j.val ≠ i.val := fun h => hji (Fin.ext h)
        dsimp [i] at hjn
        omega

theorem action_source (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (history : List (Record T L))
    (ha : NativeMicrocode.Active p c) :
    Trace p keep initial 1
      (loaded (.scan c.core.pc (fun t => (c.core.tapes t).head) (Fin.last (Fintype.card T))) c history)
      (forward (NativeMicrocode.step p c) (record c::history)) := by
  have hs : NativeMicrocode.step (program p keep initial)
      (loaded (.scan c.core.pc (fun t => (c.core.tapes t).head) (Fin.last (Fintype.card T))) c history)=
      forward (NativeMicrocode.step p c) (record c::history) := by
    cases hp : p c.core.pc with
    | halt | reject => simp [NativeMicrocode.Active,hp] at ha
    | read t next | act a next | jump next =>
      simp only [NativeMicrocode.step,Microcode.actualStep,loaded,program,Fin.val_last,
        lt_self_iff_false,↓reduceDIte,hp,forward,record,nextPC]
      congr 1
      · congr 1
        funext z; cases z with
        | data t => simp [forwardActions,oldAction,hp,bank,Microcode.Action.actual,idle]
        | log r =>
          simp [forwardActions,bank,logSymbols,Microcode.Action.actual,Turing.Tape.mk₂,
            Turing.Tape.write_mk',Turing.Tape.move_right_mk']
      · funext z; cases z with
        | data t => simp [forwardActions,oldAction,hp,positions,NativeMicrocode.direction,
            Transpose.Dir.shift,idle]
        | log r => simp [forwardActions,positions,NativeMicrocode.direction,Transpose.Dir.shift]
  apply OperationalTrace.Trace.cons
  · cases hp : p c.core.pc <;> simp_all [NativeMicrocode.Active,program,loaded]
  · rw [hs]; exact .refl _

theorem source_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (history : List (Record T L))
    (ha : NativeMicrocode.Active p c) :
    Trace p keep initial (Fintype.card T+1) (forward c history)
      (forward (NativeMicrocode.step p c) (record c::history)) := by
  have hs := scan_source p keep initial c.core.pc c history (Fintype.card T) le_rfl
    (fun _ => .blank) (by intro i hi; omega)
  have h := NativeCountedLoop.trace_trans hs (action_source p keep initial c history ha)
  simpa [forward,start] using h

end BitWord.NativeLogged
