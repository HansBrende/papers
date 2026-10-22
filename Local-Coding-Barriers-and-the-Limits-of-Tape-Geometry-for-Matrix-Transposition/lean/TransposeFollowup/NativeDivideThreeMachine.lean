import TransposeFollowup.NativeDivideThreeData

/-! A fixed nineteen-state in-place divider. It scans to STOP, processes
bits right-to-left, then returns to the first bit. No unbounded remainder
or word is stored in control. -/
namespace TransposeFollowup.NativeDivideThree
open FixedTapeCompiler CopyMachine
open NativeTrim (cursor shift shift_zero shift_add)
set_option autoImplicit false

inductive Label
  | scan | right | turn
  | read (r : Fin 3)
  | write (r : Fin 3) (b : Bool)
  | finish (r : Fin 3)
  | done (r : Fin 3)
  | reject
  deriving DecidableEq,Fintype

def program : Microcode.Program (Fin 1) Label
  | .scan => .read 0 (fun s => match s with | .data _ => .right | .stop => .turn | _ => .reject)
  | .right => .act (Microcode.single 0 ⟨none,.right⟩) .scan
  | .turn => .act (Microcode.single 0 ⟨none,.left⟩) (.read 0)
  | .read r => .read 0 (fun s => match s with
      | .data b => .write (remainder r b) (quotientBit r b) | .start => .finish r | _ => .reject)
  | .write r b => .act (Microcode.single 0 ⟨some (.data b),.left⟩) (.read r)
  | .finish r => .act (Microcode.single 0 ⟨none,.right⟩) (.done r)
  | .done _ => .halt | .reject => .reject

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label:=
  ⟨⟨pc,fun _ => word⟩,pos⟩

theorem forward_step (pre rest : List Bool) (b : Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg .scan (cursor pre (b::rest)) pos)=
      cfg .scan (cursor (pre++[b]) rest) (shift pos 1) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,
    cursor,Tape.read,symbols,List.map_cons,List.cons_append,List.headD_cons]
  congr 2
  · funext t;fin_cases t;simp [Tape.moveRight,Tape.read,List.reverse_append]
  · funext t;fin_cases t;rfl

theorem forward_run (pre rest : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*rest.length+1) (cfg .scan (cursor pre rest) pos)=
      cfg .turn (cursor (pre++rest) []) (shift pos rest.length) := by
  induction rest generalizing pre pos with
  | nil => simp only [List.append_nil,List.length_nil,Nat.cast_zero,Nat.mul_zero,Nat.zero_add,shift_zero];rfl
  | cons b rest ih =>
    rw [show 2*(b::rest).length+1=2+(2*rest.length+1) by simp;omega,NativeZipper.run_add,
      forward_step,ih,shift_add]
    congr 2
    · simp [List.append_assoc]
    · simp only [List.length_cons,Nat.cast_add,Nat.cast_one];omega

theorem turn_step (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 1 (cfg .turn (cursor xs []) pos)=
      cfg (.read 0) (cursor xs []).moveLeft (shift pos (-1)) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem backward_step (pre tail : List Bool) (b : Bool) (r : Fin 3) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg (.read r) (cursor (pre++[b]) tail).moveLeft pos)=
      cfg (.read (remainder r b)) (cursor pre (quotientBit r b::tail)).moveLeft (shift pos (-1)) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,
    cursor,Tape.moveLeft,Tape.read,symbols,List.map_append,List.map_cons,List.map_nil,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.tail_cons,List.headD_cons]
  congr 2
  · funext p;fin_cases p;simp [Tape.write]
  · funext p;fin_cases p;rfl

theorem backward_empty (tail : List Bool) (r : Fin 3) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg (.read r) (cursor [] tail).moveLeft pos)=
      cfg (.done r) (Counter.marked tail) (shift pos 1) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.single,Microcode.Action.apply,NativeMicrocode.direction,Transpose.Dir.shift,
    cursor,Tape.moveLeft,Tape.read,symbols,List.map_nil,List.reverse_nil,List.nil_append,
    List.tail_cons,List.headD_cons]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem backward_run (xs tail : List Bool) (r : Fin 3) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*xs.length+2) (cfg (.read r) (cursor xs tail).moveLeft pos)=
      cfg (.done (divide xs r).2) (Counter.marked ((divide xs r).1++tail))
        (shift pos (1-(xs.length:ℤ))) := by
  induction xs using List.reverseRecOn generalizing tail r pos with
  | nil => simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,divide,List.nil_append,Nat.cast_zero,sub_zero]
      using backward_empty tail r pos
  | append_singleton xs b ih =>
    rw [show 2*(xs++[b]).length+2=2+(2*xs.length+2) by simp;omega,NativeZipper.run_add,
      backward_step,ih,shift_add,divide_snoc]
    congr 2
    · simp [List.append_assoc]
    · simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one];omega

noncomputable def nativeEncoding:=NativeMicrocode.initialEncoding (T:=Fin 1) Label.scan
noncomputable def nativeMachine:=NativeMicrocode.machine nativeEncoding program

end TransposeFollowup.NativeDivideThree
