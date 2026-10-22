import TransposeFollowup.NativeTrimRun

/-! Replace an empty marked word by the one-bit zero word. This makes its
length max(1,length), preserves its value, and restores the absolute head.
The initial read and both possible writes are actual native transitions. -/
namespace TransposeFollowup.NativeNonemptyWord
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | check | zero | seal | done | reject deriving DecidableEq
instance : Fintype Label where
  elems:={.check,.zero,.seal,.done,.reject}
  complete:=by intro p;cases p <;> simp

def program : Microcode.Program (Fin 1) Label
  | .check => .read 0 (fun s => match s with | .data _ => .done | .stop => .zero | _ => .reject)
  | .zero => .act (Microcode.single 0 ⟨some (.data false),.right⟩) .seal
  | .seal => .act (Microcode.single 0 ⟨some .stop,.left⟩) .done
  | .done => .halt | .reject => .reject

def word (xs : List Bool) : List Bool := if xs=[] then [false] else xs

theorem word_length (xs : List Bool) : (word xs).length=max 1 xs.length := by
  cases xs <;> simp [word]

theorem word_value (xs : List Bool) : Counter.value (word xs)=Counter.value xs := by
  cases xs <;> simp [word,Counter.value]

def cfg (pc : Label) (xs : List Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => Counter.marked xs⟩,pos⟩

theorem empty_run (pos : Fin 1 → ℤ) :
    NativeZipper.run program 3 (cfg .check [] pos)=cfg .done [false] pos := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,Counter.marked,
    symbols,List.map_nil,List.map_cons,List.nil_append,List.headD_cons,List.tail_cons,
    Tape.write,Tape.moveRight,Tape.moveLeft,Tape.read]
  congr 2 <;> funext p <;> fin_cases p <;> simp

theorem nonempty_run (b : Bool) (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 1 (cfg .check (b::xs) pos)=cfg .done (b::xs) pos := rfl

theorem complete_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 3,OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
      (cfg .check xs pos).denote (cfg .done (word xs) pos).denote := by
  cases xs with
  | nil => simpa only [word,ite_true] using NativeZipper.trace_of_run program (empty_run pos)
  | cons b xs =>
    obtain ⟨t,ht,htr⟩:=NativeZipper.trace_of_run program (nonempty_run b xs pos)
    exact ⟨t,by omega,by simpa only [word,List.cons_ne_nil,ite_false] using htr⟩

end TransposeFollowup.NativeNonemptyWord
