import TransposeFollowup.NativeSpanRewind

/-! Expand one row tag using a physically stored unary clock. The fixed
controller writes one tag per clock cell and restores the clock and its
head. The output head advances by the row width. -/
namespace TransposeFollowup.NativeMatchingXorTags
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | clock | write | back | readBack | restore | done | reject
  deriving DecidableEq

instance : Fintype Label where
  elems := {.clock,.write,.back,.readBack,.restore,.done,.reject}
  complete := by intro pc; cases pc <;> simp

def program (bit : Bool) : Microcode.Program (Fin 2) Label
  | .clock => .read 0 (fun s => match s with
      | .data _ => .write | .stop => .back | _ => .reject)
  | .write => .act (fun p => ⟨if p=1 then some (.data bit) else none,.right⟩) .clock
  | .back => .act (fun p => ⟨none,if p=0 then .left else .stay⟩) .readBack
  | .readBack => .read 0 (fun s => match s with
      | .data _ => .back | .start => .restore | _ => .reject)
  | .restore => .act (fun p => ⟨none,if p=0 then .right else .stay⟩) .done
  | .done => .halt
  | .reject => .reject

def cfg (pc : Label) (clock out : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeZipper.Config (Fin 2) Label := ⟨⟨pc,![clock,out]⟩,pos⟩

abbrev symbols := CopyMachine.symbols (α := Bool)

def advance (pos : Fin 2 → ℤ) (a b : ℤ) : Fin 2 → ℤ :=
  fun p => pos p + if p=0 then a else b

@[simp] theorem advance_zero (pos : Fin 2 → ℤ) : advance pos 0 0=pos := by
  funext p; simp [advance]

theorem advance_add (pos : Fin 2 → ℤ) (a b c d : ℤ) :
    advance (advance pos a b) c d=advance pos (a+c) (b+d) := by
  funext p; simp [advance]; split_ifs <;> ring

theorem write_steps (bit a : Bool) (cl cr ol oright : List (Sym Bool))
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) 2
      (cfg .clock ⟨cl,.data a::cr⟩ ⟨ol,oright⟩ pos)=
      cfg .clock ⟨.data a::cl,cr⟩ ⟨.data bit::ol,oright.tail⟩ (advance pos 1 1) := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.write, Tape.moveRight,
    NativeMicrocode.direction, Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> rfl

theorem clock_stop (bit : Bool) (cl cr : List (Sym Bool)) (out : Tape Bool)
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) 1 (cfg .clock ⟨cl,.stop::cr⟩ out pos)=
      cfg .back ⟨cl,.stop::cr⟩ out pos := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Tape.read]

theorem back_steps (bit a : Bool) (cl cr : List (Sym Bool)) (out : Tape Bool)
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) 2 (cfg .back ⟨.data a::cl,cr⟩ out pos)=
      cfg .back ⟨cl,.data a::cr⟩ out (advance pos (-1) 0) := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.moveLeft,
    NativeMicrocode.direction, Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp [advance, sub_eq_add_neg]

theorem back_start (bit : Bool) (cl cr : List (Sym Bool)) (out : Tape Bool)
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) 3 (cfg .back ⟨.start::cl,cr⟩ out pos)=
      cfg .done ⟨.start::cl,cr⟩ out pos := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.moveLeft, Tape.moveRight,
    NativeMicrocode.direction, Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp

theorem back_run (bit : Bool) (xs : List Bool) (cl cr : List (Sym Bool))
    (out : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) (2*xs.length+3)
      (cfg .back ⟨symbols xs++.start::cl,cr⟩ out pos)=
      cfg .done ⟨.start::cl,(symbols xs).reverse++cr⟩ out
        (advance pos (-xs.length) 0) := by
  induction xs generalizing cr pos with
  | nil => simpa [symbols, CopyMachine.symbols] using back_start bit cl cr out pos
  | cons a xs ih =>
    rw [show 2*(a::xs).length+3=2+(2*xs.length+3) by simp; omega,
      NativeZipper.run_add]
    simp only [symbols, CopyMachine.symbols, List.map_cons, List.cons_append]
    rw [back_steps]
    have hi := ih (.data a::cr) (advance pos (-1) 0)
    simpa only [symbols, CopyMachine.symbols, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
      advance_add, Nat.cast_add, Nat.cast_one, neg_add_rev, zero_add] using hi

theorem forward_run (bit : Bool) (xs : List Bool) (cl cr ol oright : List (Sym Bool))
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) (2*xs.length+1)
      (cfg .clock ⟨cl,symbols xs++.stop::cr⟩ ⟨ol,oright⟩ pos)=
      cfg .back ⟨(symbols xs).reverse++cl,.stop::cr⟩
        ⟨List.replicate xs.length (.data bit)++ol,oright.drop xs.length⟩
        (advance pos xs.length xs.length) := by
  induction xs generalizing cl ol oright pos with
  | nil => simpa [symbols, CopyMachine.symbols] using clock_stop bit cl cr ⟨ol,oright⟩ pos
  | cons a xs ih =>
    rw [show 2*(a::xs).length+1=2+(2*xs.length+1) by simp; omega,
      NativeZipper.run_add]
    simp only [symbols, CopyMachine.symbols, List.map_cons, List.cons_append]
    rw [write_steps]
    have hi := ih (.data a::cl) (.data bit::ol) oright.tail (advance pos 1 1)
    have hr : List.replicate xs.length (Sym.data bit) ++ Sym.data bit::ol =
        List.replicate (xs.length+1) (Sym.data bit) ++ ol := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    simpa only [symbols, CopyMachine.symbols, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
      advance_add, Nat.cast_add, Nat.cast_one, add_comm, hr,
      List.drop_tail] using hi

theorem complete_run (bit : Bool) (xs : List Bool) (cl cr ol oright : List (Sym Bool))
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program bit) (4*xs.length+4)
      (cfg .clock ⟨.start::cl,symbols xs++.stop::cr⟩ ⟨ol,oright⟩ pos)=
      cfg .done ⟨.start::cl,symbols xs++.stop::cr⟩
        ⟨List.replicate xs.length (.data bit)++ol,oright.drop xs.length⟩
        (advance pos 0 xs.length) := by
  rw [show 4*xs.length+4=(2*xs.length+1)+(2*xs.length+3) by omega,
    NativeZipper.run_add, forward_run]
  have hb := back_run bit xs.reverse cl (.stop::cr)
    ⟨List.replicate xs.length (.data bit)++ol,oright.drop xs.length⟩
    (advance pos xs.length xs.length)
  simpa [symbols, CopyMachine.symbols, List.map_reverse, advance_add] using hb

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 2) Label.clock
noncomputable def nativeMachine (bit : Bool) := NativeMicrocode.machine nativeEncoding (program bit)

theorem fixed_resources (bit : Bool) : (nativeMachine bit).k=2 ∧
    (nativeMachine bit).g+1=5 ∧ (nativeMachine bit).q+1=7 := by
  refine ⟨rfl,rfl,?_⟩
  change Fintype.card Label-1+1=7
  decide +kernel

theorem native_repeat (bit : Bool) (xs : List Bool) (cl cr ol oright : List (Sym Bool))
    (pos : Fin 2 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+4,
      Transpose.stepN (nativeMachine bit) input t
        ((cfg .clock ⟨.start::cl,symbols xs++.stop::cr⟩ ⟨ol,oright⟩ pos).denote.denote
          nativeEncoding (program bit) inputPos outRev)=
        some ((cfg .done ⟨.start::cl,symbols xs++.stop::cr⟩
          ⟨List.replicate xs.length (.data bit)++ol,oright.drop xs.length⟩
          (advance pos 0 xs.length)).denote.denote nativeEncoding (program bit) inputPos outRev) ∧
      Transpose.step (nativeMachine bit) input
        ((cfg .done ⟨.start::cl,symbols xs++.stop::cr⟩
          ⟨List.replicate xs.length (.data bit)++ol,oright.drop xs.length⟩
          (advance pos 0 xs.length)).denote.denote nativeEncoding (program bit) inputPos outRev)=none := by
  apply NativeZipper.stopped_subroutine nativeEncoding (program bit) input inputPos outRev
    (complete_run bit xs cl cr ol oright pos)
  simp [NativeMicrocode.Active, NativeZipper.Config.denote, Microcode.Config.denote, cfg, program]

end TransposeFollowup.NativeMatchingXorTags
