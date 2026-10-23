import BitWord.NativeOracleReset
import BitWord.NativeBankCalls
import TransposeFollowup.NativeSealBack

/-! Explicit finite tape layouts for embedding the checked arbitrary-oracle
call in the block caller. All oracle work heads start at their fixed origin. -/
namespace BitWord.NativeOracleReset
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames
set_option autoImplicit false

abbrev Port (M : Transpose.TM) := NativeLoggedInit.Port (T := SourcePort M) (L := SourceLabel M)
abbrev Label (M : Transpose.TM) := NativeLoggedInit.Label (T := SourcePort M) (L := SourceLabel M)

def inputPort (M : Transpose.TM) : Port M := .data .input
def capturePort (M : Transpose.TM) : Port M := .data .capture

def initialBank (M : Transpose.TM) (w : List Bool) : Port M → Tape Bool
  | .data .input => Counter.marked w
  | .data .capture => NativeSealBack.openWord []
  | _ => ⟨[],[]⟩

def finalBank (M : Transpose.TM) (w out : List Bool) : Port M → Tape Bool
  | .data .input => Counter.marked w
  | .data .capture => NativeSealBack.openWord out
  | _ => ⟨[],[]⟩

def finalPos (M : Transpose.TM) (out : List Bool) : Port M → ℤ
  | .data .capture => out.length | _ => 0

def terminal (M : Transpose.TM) : Label M := NativeLoggedInit.label .done

theorem initial_frame (M : Transpose.TM) (w : List Bool) :
    NativeLoggedInit.initialConfig (sourceInitial M w)=
      workCfg (none : Label M) (initialBank M w) (fun _ => 0) := by
  unfold NativeLoggedInit.initialConfig sourceInitial NativeOracle.cfg workCfg
  congr 1
  · congr 1
    funext p; cases p with
    | data p => cases p <;> rfl
    | log r => rfl
  · funext p; cases p <;> rfl

theorem final_frame (M : Transpose.TM) (w out : List Bool) :
    NativeLoggedInit.mapConfig (NativeLogged.cleared (sourceFinal M w out))=
      workCfg (terminal M) (finalBank M w out) (finalPos M out) := by
  unfold NativeLoggedInit.mapConfig NativeLogged.cleared sourceFinal workCfg
  congr 1
  · congr 1
    funext p; cases p with
    | data p => cases p <;> simp [finalBank,NativeOracle.prepared,NativeSealBack.openWord,Counter.marked,
        symbols,Tape.denote,List.map_reverse,AbsoluteTape.blank]
    | log r => rfl
  · funext p; cases p with
    | data p => cases p <;> rfl
    | log r => rfl

theorem call_trace (M : Transpose.TM) (w out : List Bool) (T : ℕ)
    (h : Transpose.ComputesWithin M w out T) :
    ∃ t≤budget M T,
      OperationalTrace.Trace (NativeMicrocode.step (program M)) (NativeMicrocode.Active (program M)) t
        (workCfg (none : Label M) (initialBank M w) (fun _ => 0))
        (workCfg (terminal M) (finalBank M w out) (finalPos M out)) := by
  obtain ⟨t,ht,htr⟩ := prepared_reset_call M w out T h
  exact ⟨t,ht,by simpa only [initial_frame,final_frame] using htr⟩

end BitWord.NativeOracleReset
