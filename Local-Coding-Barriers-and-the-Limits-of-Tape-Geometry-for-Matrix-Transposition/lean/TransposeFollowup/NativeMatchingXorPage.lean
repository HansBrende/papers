import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.MatchingXorStream

/-! A uniform four-tape controller for one increasing matching page.
The source/target tag tapes select the two streams to zip.  False-tagged
bits are skipped and retained.  No dimension is stored in finite control.
The caller must construct the two tag streams and load the raw banks. -/
namespace TransposeFollowup.NativeMatchingXorPage
open FixedTapeCompiler CopyMachine MatchingXorStream
set_option autoImplicit false

inductive Label
  | findA | skipA | readA | findB (a : Bool) | skipB (a : Bool)
  | readB (a : Bool) | write (a b : Bool) | finishB | skipFinish | done | reject
  deriving DecidableEq, Fintype

def moveA (p : Fin 4) : Microcode.Move := if p=0 ∨ p=2 then .right else .stay
def moveB (p : Fin 4) : Microcode.Move := if p=1 ∨ p=3 then .right else .stay

def program : Microcode.Program (Fin 4) Label
  | .findA => .read 2 (fun s => match s with
      | .data false => .skipA | .data true => .readA | .stop => .finishB | _ => .reject)
  | .skipA => .act (fun p => ⟨none,moveA p⟩) .findA
  | .readA => .read 0 (fun s => match s with | .data a => .findB a | _ => .reject)
  | .findB a => .read 3 (fun s => match s with
      | .data false => .skipB a | .data true => .readB a | _ => .reject)
  | .skipB a => .act (fun p => ⟨none,moveB p⟩) (.findB a)
  | .readB a => .read 1 (fun s => match s with | .data b => .write a b | _ => .reject)
  | .write a b => .act (fun p =>
      ⟨if p=1 then some (.data (a.xor b)) else none,.right⟩) .findA
  | .finishB => .read 3 (fun s => match s with
      | .data false => .skipFinish | .stop => .done | _ => .reject)
  | .skipFinish => .act (fun p => ⟨none,moveB p⟩) .finishB
  | .done => .halt
  | .reject => .reject

def cfg (pc : Label) (a b af bt : Tape Bool) (pos : Fin 4 → ℤ) :
    NativeZipper.Config (Fin 4) Label := ⟨⟨pc, ![a,b,af,bt]⟩,pos⟩

abbrev symbols := CopyMachine.symbols (α := Bool)

def advance (pos : Fin 4 → ℤ) (a b : ℕ) : Fin 4 → ℤ :=
  fun p => pos p + if p=0 ∨ p=2 then a else b

@[simp] theorem advance_zero (pos : Fin 4 → ℤ) : advance pos 0 0=pos := by
  funext p; simp [advance]

theorem advance_add (pos : Fin 4 → ℤ) (a b c d : ℕ) :
    advance (advance pos a b) c d=advance pos (a+c) (b+d) := by
  funext p; simp [advance]; split_ifs <;> push_cast <;> ring

theorem skipA_steps (a : Bool) (al ar bl br atl atr btl btr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 2
      (cfg .findA ⟨al,.data a::ar⟩ ⟨bl,br⟩ ⟨atl,.data false::atr⟩ ⟨btl,btr⟩ pos)=
      cfg .findA ⟨.data a::al,ar⟩ ⟨bl,br⟩ ⟨.data false::atl,atr⟩ ⟨btl,btr⟩
        (advance pos 1 0) := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.moveRight,
    NativeMicrocode.direction, Transpose.Dir.shift, moveA, advance]
  constructor <;> funext p <;> fin_cases p <;> simp [advance]

theorem readA_steps (a : Bool) (al ar bl br atl atr btl btr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 2
      (cfg .findA ⟨al,.data a::ar⟩ ⟨bl,br⟩ ⟨atl,.data true::atr⟩ ⟨btl,btr⟩ pos)=
      cfg (.findB a) ⟨al,.data a::ar⟩ ⟨bl,br⟩ ⟨atl,.data true::atr⟩ ⟨btl,btr⟩ pos := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Tape.read]

theorem skipB_steps (a b : Bool) (al ar bl br atl atr btl btr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 2
      (cfg (.findB a) ⟨al,ar⟩ ⟨bl,.data b::br⟩ ⟨atl,atr⟩ ⟨btl,.data false::btr⟩ pos)=
      cfg (.findB a) ⟨al,ar⟩ ⟨.data b::bl,br⟩ ⟨atl,atr⟩ ⟨.data false::btl,btr⟩
        (advance pos 0 1) := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.moveRight,
    NativeMicrocode.direction, Transpose.Dir.shift, moveB, advance]
  constructor <;> funext p <;> fin_cases p <;> simp [advance]

theorem pair_steps (a b : Bool) (al ar bl br atl atr btl btr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 3
      (cfg (.findB a) ⟨al,.data a::ar⟩ ⟨bl,.data b::br⟩
        ⟨atl,.data true::atr⟩ ⟨btl,.data true::btr⟩ pos)=
      cfg .findA ⟨.data a::al,ar⟩ ⟨.data (a.xor b)::bl,br⟩
        ⟨.data true::atl,atr⟩ ⟨.data true::btl,btr⟩ (advance pos 1 1) := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.write, Tape.moveRight,
    NativeMicrocode.direction, Transpose.Dir.shift, advance]
  constructor <;> funext p <;> fin_cases p <;> simp [advance]

theorem endA_step (a b : Tape Bool) (atl atr : List (Sym Bool)) (bt : Tape Bool)
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 1 (cfg .findA a b ⟨atl,.stop::atr⟩ bt pos)=
      cfg .finishB a b ⟨atl,.stop::atr⟩ bt pos := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Tape.read]

theorem finish_steps (b : Bool) (a af : Tape Bool) (bl br btl btr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 2
      (cfg .finishB a ⟨bl,.data b::br⟩ af ⟨btl,.data false::btr⟩ pos)=
      cfg .finishB a ⟨.data b::bl,br⟩ af ⟨.data false::btl,btr⟩ (advance pos 0 1) := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Microcode.Action.apply, Tape.read, Tape.moveRight,
    NativeMicrocode.direction, Transpose.Dir.shift, moveB, advance]
  constructor <;> funext p <;> fin_cases p <;> simp [advance]

theorem finish_done (a b af : Tape Bool) (btl btr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 1 (cfg .finishB a b af ⟨btl,.stop::btr⟩ pos)=
      cfg .done a b af ⟨btl,.stop::btr⟩ pos := by
  simp [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, Tape.read]

theorem finish_run (ys : List Record) (h : (selected ys).length=0)
    (a af : Tape Bool) (bl br btl btr : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    NativeZipper.run program (2*ys.length+1)
      (cfg .finishB a ⟨bl,symbols (values ys)++br⟩ af
        ⟨btl,symbols (tags ys)++.stop::btr⟩ pos)=
      cfg .done a ⟨(symbols (values ys)).reverse++bl,br⟩ af
        ⟨(symbols (tags ys)).reverse++btl,.stop::btr⟩ (advance pos 0 ys.length) := by
  induction ys generalizing bl btl pos with
  | nil => simpa [values, tags, symbols, CopyMachine.symbols] using finish_done a ⟨bl,br⟩ af btl btr pos
  | cons y ys ih =>
    rcases y with ⟨t,b⟩
    cases t with
    | true => simp at h
    | false =>
      rw [show 2*((false,b)::ys).length+1=2+(2*ys.length+1) by simp; omega,
        NativeZipper.run_add]
      simp only [values, tags, List.map_cons, Prod.snd, Prod.fst,
        symbols, CopyMachine.symbols, List.cons_append]
      rw [finish_steps]
      have hi := ih h (.data b::bl) (.data false::btl) (advance pos 0 1)
      simpa only [values, tags, symbols, CopyMachine.symbols,
        List.map_cons, Prod.fst, Prod.snd, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append,
        List.length_cons, advance_add, zero_add, add_zero, add_comm] using hi

def ticks (xs ys : List Record) : ℕ :=
  2*xs.length+2*ys.length+(selected xs).length+2

def loaded (pc : Label) (xs ys : List Record)
    (al ar bl br atl atr btl btr : List (Sym Bool)) (pos : Fin 4 → ℤ) :=
  cfg pc ⟨al,symbols (values xs)++ar⟩ ⟨bl,symbols (values ys)++br⟩
    ⟨atl,symbols (tags xs)++.stop::atr⟩ ⟨btl,symbols (tags ys)++.stop::btr⟩ pos

def finished (xs ys : List Record)
    (al ar bl br atl atr btl btr : List (Sym Bool)) (pos : Fin 4 → ℤ) :=
  cfg .done ⟨(symbols (values xs)).reverse++al,ar⟩
    ⟨(symbols (MatchingXorStream.apply (selected xs) ys)).reverse++bl,br⟩
    ⟨(symbols (tags xs)).reverse++atl,.stop::atr⟩
    ⟨(symbols (tags ys)).reverse++btl,.stop::btr⟩ (advance pos xs.length ys.length)

theorem scan_run (xs ys : List Record)
    (h : (selected xs).length=(selected ys).length)
    (al ar bl br atl atr btl btr : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    NativeZipper.run program (ticks xs ys) (loaded .findA xs ys al ar bl br atl atr btl btr pos)=
      finished xs ys al ar bl br atl atr btl btr pos := by
  induction xs generalizing ys al bl atl btl pos with
  | nil =>
    have hy : (selected ys).length=0 := h.symm
    rw [show ticks [] ys=1+(2*ys.length+1) by simp [ticks]; omega, NativeZipper.run_add]
    simp only [loaded, values, tags, List.map_nil, symbols, CopyMachine.symbols,
      List.nil_append]
    rw [endA_step]
    have hi := finish_run ys hy ⟨al,ar⟩ ⟨atl,.stop::atr⟩ bl br btl btr pos
    simpa only [finished, values, tags, List.map_nil, symbols, CopyMachine.symbols,
      List.reverse_nil, List.nil_append, List.length_nil, selected_nil,
      nil_apply_of_none ys hy] using hi
  | cons x xs ih =>
    rcases x with ⟨t,a⟩
    cases t with
    | false =>
      have hx : (selected xs).length=(selected ys).length := h
      rw [show ticks ((false,a)::xs) ys=2+ticks xs ys by simp [ticks]; omega,
        NativeZipper.run_add]
      simp only [loaded, values, tags, List.map_cons, Prod.snd, Prod.fst,
        symbols, CopyMachine.symbols, List.cons_append]
      rw [skipA_steps]
      have hi := ih ys hx (.data a::al) bl (.data false::atl) btl (advance pos 1 0)
      simpa only [loaded, finished, values, tags, symbols, CopyMachine.symbols,
        List.map_cons, Prod.snd, Prod.fst, selected_false, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
        advance_add, zero_add, add_zero, add_comm] using hi
    | true =>
      have seek : ∀ (ys : List Record), (a::selected xs).length=(selected ys).length →
          ∀ (bl btl : List (Sym Bool)) (pos : Fin 4 → ℤ),
          NativeZipper.run program (2*xs.length+2*ys.length+(selected xs).length+3)
            (loaded (.findB a) ((true,a)::xs) ys al ar bl br atl atr btl btr pos)=
            finished ((true,a)::xs) ys al ar bl br atl atr btl btr pos := by
        intro zs hz bl btl pos
        induction zs generalizing bl btl pos with
        | nil => simp at hz
        | cons z zs iz =>
          rcases z with ⟨tag,b⟩
          cases tag with
          | false =>
            have hz' : (a::selected xs).length=(selected zs).length := hz
            rw [show 2*xs.length+2*((false,b)::zs).length+(selected xs).length+3=
                2+(2*xs.length+2*zs.length+(selected xs).length+3) by simp; omega,
              NativeZipper.run_add]
            simp only [loaded, values, tags, List.map_cons, Prod.snd, Prod.fst,
              symbols, CopyMachine.symbols, List.cons_append]
            rw [skipB_steps]
            have hi := iz hz' (.data b::bl) (.data false::btl) (advance pos 0 1)
            simpa only [loaded, finished, values, tags, symbols, CopyMachine.symbols,
              List.map_cons, Prod.snd, Prod.fst, selected_true, apply_false, List.reverse_cons,
              List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
              advance_add, zero_add, add_zero, add_comm, List.cons_append] using hi
          | true =>
            have hz' : (selected xs).length=(selected zs).length := by simpa using hz
            rw [show 2*xs.length+2*((true,b)::zs).length+(selected xs).length+3=
                3+ticks xs zs by simp [ticks]; omega, NativeZipper.run_add]
            simp only [loaded, values, tags, List.map_cons, Prod.snd, Prod.fst,
              symbols, CopyMachine.symbols, List.cons_append]
            rw [pair_steps]
            have hi := ih zs hz' (.data a::al) (.data (a.xor b)::bl)
              (.data true::atl) (.data true::btl) (advance pos 1 1)
            simpa only [loaded, finished, values, tags, symbols, CopyMachine.symbols,
              List.map_cons, Prod.snd, Prod.fst, selected_true, apply_true, List.reverse_cons,
              List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
              advance_add, add_comm, List.cons_append] using hi
      rw [show ticks ((true,a)::xs) ys=
          2+(2*xs.length+2*ys.length+(selected xs).length+3) by simp [ticks]; omega,
        NativeZipper.run_add]
      simp only [loaded, values, tags, List.map_cons, Prod.snd, Prod.fst,
        symbols, CopyMachine.symbols, List.cons_append]
      rw [readA_steps]
      exact seek ys h bl btl pos

noncomputable def nativeEncoding :=
  NativeMicrocode.initialEncoding (T:=Fin 4) Label.findA

noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=4 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=17 ∧ nativeEncoding.label .findA=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem ticks_linear (xs ys : List Record) : ticks xs ys≤3*(xs.length+ys.length)+2 := by
  have h := selected_length_le xs
  dsimp [ticks]
  omega

theorem native_scan (xs ys : List Record)
    (h : (selected xs).length=(selected ys).length)
    (al ar bl br atl atr btl btr : List (Sym Bool)) (pos : Fin 4 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ ticks xs ys,
      Transpose.stepN nativeMachine input t
        ((loaded .findA xs ys al ar bl br atl atr btl btr pos).denote.denote
          nativeEncoding program inputPos outRev)=
        some ((finished xs ys al ar bl br atl atr btl btr pos).denote.denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((finished xs ys al ar bl br atl atr btl btr pos).denote.denote
          nativeEncoding program inputPos outRev)=none := by
  apply NativeZipper.stopped_subroutine nativeEncoding program input inputPos outRev
    (scan_run xs ys h al ar bl br atl atr btl btr pos)
  simp [NativeMicrocode.Active, NativeZipper.Config.denote, Microcode.Config.denote,
    finished, cfg, program]

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 4 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs ys : List Record) (h : (selected xs).length=(selected ys).length)
    (al ar bl br atl atr btl btr : List (Sym Bool)) (pos : Fin 4 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ ticks xs ys,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (loaded .findA xs ys al ar bl br atl atr btl btr pos).denote outerFrame).denote
            encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (finished xs ys al ar bl br atl atr btl btr pos).denote outerFrame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run program
    (scan_run xs ys h al ar bl br atl atr btl btr pos)
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeMatchingXorPage
