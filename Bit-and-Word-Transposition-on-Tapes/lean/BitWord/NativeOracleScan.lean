import BitWord.NativeOracle
import TransposeFollowup.NativeCountedLoop

/-! The literal oracle controller scans a fixed number of heads. Every read,
transition and halt-discovery jump is charged here. -/
namespace BitWord.NativeOracle
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false

abbrev Tapes (M : Transpose.TM) := Port M → Turing.Tape (Sym Bool)
abbrev Positions (M : Transpose.TM) := Port M → ℤ

def cfg (M : Transpose.TM) (pc : Label M) (tapes : Tapes M) (pos : Positions M) :
    NativeMicrocode.Config (Port M) (Label M) := ⟨⟨pc,tapes⟩,pos⟩

def scanned (M : Transpose.TM) (tapes : Tapes M) : Scanned M :=
  fun i => NativeMicrocode.symbolCode (tapes (.work i)).head

abbrev Trace (M : Transpose.TM) :=
  OperationalTrace.Trace (NativeMicrocode.step (program M)) (NativeMicrocode.Active (program M))

theorem scan_trace (M : Transpose.TM) (state : State M) (input : Option Bool)
    (tapes : Tapes M) (pos : Positions M) (r : ℕ) (hr : r ≤ workCount M)
    (seen : Scanned M)
    (hseen : ∀ i, i.val < workCount M-r → seen i=scanned M tapes i) :
    Trace M r
      (cfg M (.scan state input seen ⟨workCount M-r,by omega⟩) tapes pos)
      (cfg M (.scan state input (scanned M tapes) (Fin.last (workCount M))) tapes pos) := by
  induction r generalizing seen with
  | zero =>
    have he : seen=scanned M tapes := by
      funext i; exact hseen i (by simpa using i.isLt)
    subst seen
    simpa only [Nat.sub_zero, Fin.last] using (OperationalTrace.Trace.refl
      (cfg M (.scan state input (scanned M tapes) (Fin.last (workCount M))) tapes pos))
  | succ r ih =>
    have hn : workCount M-(r+1) < workCount M := by omega
    let i : Fin (workCount M) := ⟨workCount M-(r+1),hn⟩
    let seen' := Function.update seen i (scanned M tapes i)
    have he : (workCount M-(r+1))+1=workCount M-r := by omega
    have hs : NativeMicrocode.step (program M)
        (cfg M (.scan state input seen ⟨workCount M-(r+1),by omega⟩) tapes pos)=
        cfg M (.scan state input seen' ⟨workCount M-r,by omega⟩) tapes pos := by
      simp [NativeMicrocode.step,Microcode.actualStep,program,cfg,hn,seen',i,scanned,he]
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,cfg,hn]
    · rw [hs]
      apply ih (by omega) seen'
      intro j hj
      by_cases hji : j=i
      · subst j; simp [seen']
      · simp only [seen', Function.update_of_ne hji]
        apply hseen j
        have hjn : j.val ≠ i.val := fun h => hji (Fin.ext h)
        dsimp [i] at hjn
        omega

def transitioned (M : Transpose.TM) (tr : Transition M) (tapes : Tapes M)
    (pos : Positions M) : NativeMicrocode.Config (Port M) (Label M) :=
  cfg M (.input tr.1) (fun p => (actions M tr p).actual (tapes p))
    (fun p => (NativeMicrocode.direction (actions M tr p).move).shift (pos p))

def macroResult (M : Transpose.TM) (state : State M) (tapes : Tapes M) (pos : Positions M) :
    NativeMicrocode.Config (Port M) (Label M) :=
  match (plane M).δ state (inputSymbol (tapes .input).head) (scanned M tapes) with
  | none => cfg M .done tapes pos
  | some tr => transitioned M tr tapes pos

theorem macro_trace (M : Transpose.TM) (state : State M) (tapes : Tapes M) (pos : Positions M) :
    Trace M (workCount M+2) (cfg M (.input state) tapes pos) (macroResult M state tapes pos) := by
  have hinput : NativeMicrocode.step (program M) (cfg M (.input state) tapes pos)=
      cfg M (.scan state (inputSymbol (tapes .input).head) (fun _ => 0) 0)
        tapes pos := rfl
  have hscan := scan_trace M state (inputSymbol (tapes .input).head) tapes pos
    (workCount M) le_rfl (fun _ => 0) (by intro i hi; omega)
  have hfinish : Trace M 1
      (cfg M (.scan state (inputSymbol (tapes .input).head) (scanned M tapes)
        (Fin.last (workCount M))) tapes pos)
      (macroResult M state tapes pos) := by
    apply OperationalTrace.Trace.cons
    · simp only [NativeMicrocode.Active,cfg,program,Fin.val_last,lt_self_iff_false,↓reduceDIte]
      split <;> simp
    · have hs : NativeMicrocode.step (program M)
          (cfg M (.scan state (inputSymbol (tapes .input).head) (scanned M tapes)
            (Fin.last (workCount M))) tapes pos)=macroResult M state tapes pos := by
        cases hd : BitPlaneMachine.delta M state
          (inputSymbol (tapes .input).head) (scanned M tapes) <;>
          simp [NativeMicrocode.step,Microcode.actualStep,cfg,program,macroResult,plane,hd,transitioned]
      rw [hs]; exact .refl _
  have htail := NativeCountedLoop.trace_trans hscan hfinish
  have hwhole : Trace M ((workCount M+1)+1)
      (cfg M (.input state) tapes pos) (macroResult M state tapes pos) := by
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,cfg]
    · rw [hinput]
      simpa using htail
  simpa [Nat.add_assoc] using hwhole

end BitWord.NativeOracle
