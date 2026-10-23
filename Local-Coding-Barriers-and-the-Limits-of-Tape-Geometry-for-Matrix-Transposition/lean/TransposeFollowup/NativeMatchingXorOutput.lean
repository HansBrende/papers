import TransposeFollowup.NativeIOZipper
import TransposeFollowup.NativeCounter

/-! A fixed native emitter for a marked bit word. Every source read, output
bit and head movement is an actual transition. The tape cells and input head
are preserved; the work head finishes on STOP for subsequent paid cleanup. -/
namespace TransposeFollowup.NativeMatchingXorOutput
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | read | emit (b : Bool) | advance | done | reject
  deriving DecidableEq, Fintype

def program : NativeIO.Program (Fin 1) Label
  | .read => .work (.read 0 (fun s => match s with
      | .data b => .emit b | .stop => .done | _ => .reject))
  | .emit b => .output b .advance
  | .advance => .work (.act (fun _ => ⟨none,.right⟩) .read)
  | .done => .work .halt
  | .reject => .work .reject

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ)
    (ip : ℤ) (outRev : List Bool) : NativeIOZipper.Config (Fin 1) Label :=
  ⟨⟨⟨pc,fun _ => word⟩,pos⟩,ip,outRev⟩

theorem emit_steps (a : Bool) (left right : List (Sym Bool))
    (pos : Fin 1 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    NativeIOZipper.run program input 3 (cfg .read ⟨left,.data a::right⟩ pos ip outRev)=
      cfg .read ⟨.data a::left,right⟩ (fun p => pos p+1) ip (a::outRev) := by
  simp [NativeIOZipper.run,OperationalTrace.run,NativeIOZipper.step,NativeIOZipper.setLabel,
    NativeZipper.step,Microcode.step,NativeIO.workProgram,program,cfg,
    Microcode.Action.apply,Tape.read,Tape.moveRight,NativeMicrocode.direction,Transpose.Dir.shift]

theorem finish_step (left right : List (Sym Bool)) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    NativeIOZipper.run program input 1 (cfg .read ⟨left,.stop::right⟩ pos ip outRev)=
      cfg .done ⟨left,.stop::right⟩ pos ip outRev := by
  simp [NativeIOZipper.run,OperationalTrace.run,NativeIOZipper.step,
    NativeZipper.step,Microcode.step,NativeIO.workProgram,program,cfg,Tape.read]

theorem run_add (input : List Bool) (n k : ℕ) (c : NativeIOZipper.Config (Fin 1) Label) :
    NativeIOZipper.run program input (n+k) c=
      NativeIOZipper.run program input k (NativeIOZipper.run program input n c) :=
  OperationalTrace.run_add _ n k c

theorem emit_run (xs : List Bool) (left right : List (Sym Bool))
    (pos : Fin 1 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    NativeIOZipper.run program input (3*xs.length+1)
      (cfg .read ⟨left,symbols xs++.stop::right⟩ pos ip outRev)=
      cfg .done ⟨(symbols xs).reverse++left,.stop::right⟩
        (fun p => pos p+xs.length) ip (xs.reverse++outRev) := by
  induction xs generalizing left pos outRev with
  | nil => simpa [symbols] using finish_step left right pos input ip outRev
  | cons a xs ih =>
    rw [show 3*(a::xs).length+1=3+(3*xs.length+1) by simp; omega,run_add]
    simp only [symbols,List.map_cons,List.cons_append]
    rw [emit_steps]
    have h := ih (.data a::left) (fun p => pos p+1) (a::outRev)
    simpa only [symbols,List.map_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,
      add_comm,add_left_comm] using h

abbrev Trace (input : List Bool) :=
  OperationalTrace.Trace (NativeIO.step program input) (NativeIO.Active program)

theorem output_trace (xs : List Bool) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3*xs.length+1, Trace input t
      (cfg .read (Counter.marked xs) pos ip outRev).denote
      (cfg .done ⟨(symbols xs).reverse++[.start],[.stop]⟩
        (fun p => pos p+xs.length) ip (xs.reverse++outRev)).denote := by
  simpa only [Counter.marked] using NativeIOZipper.trace_of_run program input
    (emit_run xs [.start] [] pos input ip outRev)

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 1) Label.read
noncomputable def nativeMachine := NativeIO.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=6 ∧ nativeEncoding.label .read=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=6
  decide +kernel

theorem native_output (xs : List Bool) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3*xs.length+1,
      Transpose.stepN nativeMachine input t
        ((cfg .read (Counter.marked xs) pos ip outRev).denote.denote nativeEncoding program)=
        some ((cfg .done ⟨(symbols xs).reverse++[.start],[.stop]⟩
          (fun p => pos p+xs.length) ip (xs.reverse++outRev)).denote.denote nativeEncoding program) ∧
      Transpose.step nativeMachine input
        ((cfg .done ⟨(symbols xs).reverse++[.start],[.stop]⟩
          (fun p => pos p+xs.length) ip (xs.reverse++outRev)).denote.denote nativeEncoding program)=none := by
  obtain ⟨t,ht,htr⟩ := output_trace xs pos input ip outRev
  refine ⟨t,ht,NativeIO.trace_stepN nativeEncoding program input htr,?_⟩
  apply (NativeIO.step_none_iff nativeEncoding program input _).mpr
  simp [NativeIO.Active,NativeIOZipper.Config.denote,NativeZipper.Config.denote,
    Microcode.Config.denote,cfg,program]

end TransposeFollowup.NativeMatchingXorOutput
