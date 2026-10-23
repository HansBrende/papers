import TransposeFollowup.NativeSealBack

/-! Read a two-bit marked opcode and return its head to the first bit. -/
namespace BitWord.NativeOpcode
open FixedTapeCompiler CopyMachine TransposeFollowup
set_option autoImplicit false
inductive Label
  | first | advance (a : Bool) | second (a : Bool) | back (a b : Bool)
  | done (a b : Bool) | reject
  deriving DecidableEq,Fintype
def start : Label := .first
def program : Microcode.Program (Fin 1) Label
  | .first => .read 0 (fun s => match s with | .data b => .advance b | _ => .reject)
  | .advance a => .act (fun _ => ⟨none,.right⟩) (.second a)
  | .second a => .read 0 (fun s => match s with | .data b => .back a b | _ => .reject)
  | .back a b => .act (fun _ => ⟨none,.left⟩) (.done a b)
  | .done _ _ => .halt | .reject => .reject
def cfg (pc : Label) (xs : List Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => Counter.marked xs⟩,pos⟩
theorem complete_run (a b : Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 4 (cfg start [a,b] pos)=cfg (.done a b) [a,b] pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,start,cfg,
    Counter.marked,symbols,Tape.read,Microcode.Action.apply,Tape.moveRight,Tape.moveLeft,
    NativeMicrocode.direction,Transpose.Dir.shift]
theorem complete_trace (a b : Bool) (pos : Fin 1 → ℤ) :
    ∃ t≤4, OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
      (cfg start [a,b] pos).denote (cfg (.done a b) [a,b] pos).denote :=
  NativeZipper.trace_of_run program (complete_run a b pos)
end BitWord.NativeOpcode
