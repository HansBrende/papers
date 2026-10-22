import TransposeFollowup.NativeIOFusionCalls
import Transpose.Tape.Encode
import TransposeFollowup.NativeCountedLoop

/-! A fixed four-state input rewind. It requires no work tape, counter, or
input-length parameter in the program. All work tapes and their positions,
and the external output, are preserved. Even the empty input is covered. -/
namespace TransposeFollowup.NativeInputRewind
open FixedTapeCompiler Transpose.Tape.Impl
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
inductive Label | left | read | right | done
  deriving DecidableEq

instance : Fintype Label := ⟨{.left,.read,.right,.done},by intro pc;cases pc <;> simp⟩

variable {T : Type*}

def program (T : Type*) : NativeIO.Program T Label
  | .left => .moveInput .left .read
  | .read => .readInput (fun b => match b with | some _ => .left | none => .right)
  | .right => .moveInput .right .done
  | .done => .work .halt

def cfg (pc : Label) (frame : MicrocodeEmbedding.Frame T) (inputPos : ℤ) (outRev : List Bool) :
    NativeIO.Config T Label := ⟨⟨⟨pc,frame.tapes⟩,frame.pos⟩,inputPos,outRev⟩
abbrev Trace (T : Type*) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program T) w) (NativeIO.Active (program T))

theorem left_trace (w : List Bool) (frame : MicrocodeEmbedding.Frame T) (ip : ℤ) (outRev : List Bool) :
    Trace T w 1 (cfg .left frame ip outRev) (cfg .read frame (ip-1) outRev) := by
  apply OperationalTrace.Trace.cons
  · trivial
  · exact .refl _

theorem read_trace (w : List Bool) (frame : MicrocodeEmbedding.Frame T) (ip : ℤ) (outRev : List Bool) :
    Trace T w 1 (cfg .read frame ip outRev)
      (cfg (match Transpose.readInput w ip with | some _ => .left | none => .right) frame ip outRev) := by
  apply OperationalTrace.Trace.cons
  · trivial
  · exact .refl _

theorem right_trace (w : List Bool) (frame : MicrocodeEmbedding.Frame T) (ip : ℤ) (outRev : List Bool) :
    Trace T w 1 (cfg .right frame ip outRev) (cfg .done frame (ip+1) outRev) := by
  apply OperationalTrace.Trace.cons
  · trivial
  · exact .refl _

theorem scan_trace (w : List Bool) (frame : MicrocodeEmbedding.Frame T) (outRev : List Bool)
    (n : ℕ) (hn : n ≤ w.length) :
    Trace T w (2*n+3) (cfg .left frame n outRev) (cfg .done frame 0 outRev) := by
  induction n with
  | zero =>
    have hread:=read_trace w frame (-1) outRev
    rw [readInput_eq_none (Or.inl (by omega))] at hread
    have h:=trace_trans (left_trace w frame 0 outRev) (trace_trans hread (right_trace w frame (-1) outRev))
    simpa using h
  | succ n ih =>
    have hread:=read_trace w frame n outRev
    have hi : Transpose.readInput w (n:ℤ)=some (w[n]'(by omega)) := by
      rw [readInput_natCast,nth_eq_getElem?,List.getElem?_eq_getElem (by omega)]
    rw [hi] at hread
    have hleft:=left_trace w frame (n+1) outRev
    have hnpos : (n:ℤ)+1-1=n := by omega
    rw [hnpos] at hleft
    have h:=trace_trans hleft (trace_trans hread (ih (by omega)))
    have htime : 1+(1+(2*n+3))=2*(n+1)+3 := by omega
    rw [htime] at h
    simpa only [Nat.cast_add,Nat.cast_one] using h

theorem complete_trace (w : List Bool) (frame : MicrocodeEmbedding.Frame T) (outRev : List Bool) :
    Trace T w (2*w.length+3) (cfg .left frame w.length outRev) (cfg .done frame 0 outRev) :=
  scan_trace w frame outRev w.length le_rfl

end TransposeFollowup.NativeInputRewind
