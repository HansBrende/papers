import TransposeFollowup.NativeMatchingXorPage

/-! Restore all four data/tag heads after a matching-page scan. One marked
source-tag tape is the physical clock. Data heads never cross their original
boundaries, so arbitrary prefixes (including the untouched A half on the
B-target tape) are preserved. -/
namespace TransposeFollowup.NativeMatchingXorReset
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | left | read | follow | restore | done | reject
  deriving DecidableEq

instance : Fintype Label where
  elems := {.left,.read,.follow,.restore,.done,.reject}
  complete := by intro pc; cases pc <;> simp

def program : Microcode.Program (Fin 4) Label
  | .left => .act (fun p => ⟨none,if p=2 then .left else .stay⟩) .read
  | .read => .read 2 (fun s => match s with
      | .data _ => .follow | .start => .restore | _ => .reject)
  | .follow => .act (fun p => ⟨none,if p=2 then .stay else .left⟩) .left
  | .restore => .act (fun p => ⟨none,if p=2 then .right else .stay⟩) .done
  | .done => .halt
  | .reject => .reject

def cfg (pc : Label) (a b af bf : Tape Bool) (pos : Fin 4 → ℤ) : NativeZipper.Config (Fin 4) Label :=
  ⟨⟨pc,![a,b,af,bf]⟩,pos⟩

theorem rewind_steps (a b af bf : Bool) (al ar bl br afl afr bfl bfr : List (Sym Bool))
    (pos : Fin 4 → ℤ) :
    NativeZipper.run program 3
      (cfg .left ⟨.data a::al,ar⟩ ⟨.data b::bl,br⟩ ⟨.data af::afl,afr⟩ ⟨.data bf::bfl,bfr⟩ pos)=
      cfg .left ⟨al,.data a::ar⟩ ⟨bl,.data b::br⟩ ⟨afl,.data af::afr⟩ ⟨bfl,.data bf::bfr⟩
        (fun p => pos p-1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp

theorem empty_run (a b bf : Tape Bool) (afl afr : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    NativeZipper.run program 3 (cfg .left a b ⟨.start::afl,afr⟩ bf pos)=
      cfg .done a b ⟨.start::afl,afr⟩ bf pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp

theorem rewind_run (as bs af bf : List Bool)
    (hb : bs.length=as.length) (hf : af.length=as.length) (hg : bf.length=as.length)
    (al ar bl br afl afr bfl bfr : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    NativeZipper.run program (3*as.length+3)
      (cfg .left ⟨symbols as++al,ar⟩ ⟨symbols bs++bl,br⟩
        ⟨symbols af++.start::afl,afr⟩ ⟨symbols bf++bfl,bfr⟩ pos)=
      cfg .done ⟨al,(symbols as).reverse++ar⟩ ⟨bl,(symbols bs).reverse++br⟩
        ⟨.start::afl,(symbols af).reverse++afr⟩ ⟨bfl,(symbols bf).reverse++bfr⟩
        (fun p => pos p-as.length) := by
  induction as generalizing bs af bf ar br afr bfr pos with
  | nil =>
    have hb' : bs=[] := List.length_eq_zero_iff.mp (by simpa using hb)
    have hf' : af=[] := List.length_eq_zero_iff.mp (by simpa using hf)
    have hg' : bf=[] := List.length_eq_zero_iff.mp (by simpa using hg)
    subst bs; subst af; subst bf
    simpa [symbols] using empty_run ⟨al,ar⟩ ⟨bl,br⟩ ⟨bfl,bfr⟩ afl afr pos
  | cons a as ih =>
    cases bs with
    | nil => simp at hb
    | cons b bs =>
      cases af with
      | nil => simp at hf
      | cons f af =>
        cases bf with
        | nil => simp at hg
        | cons g bf =>
          simp only [List.length_cons,Nat.add_right_cancel_iff] at hb hf hg
          rw [show 3*(a::as).length+3=3+(3*as.length+3) by simp; omega,NativeZipper.run_add]
          simp only [symbols,List.map_cons,List.cons_append]
          rw [rewind_steps]
          have ht := ih bs af bf hb hf hg (.data a::ar) (.data b::br) (.data f::afr) (.data g::bfr) (fun p => pos p-1)
          simpa only [symbols,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,
            List.length_cons,Nat.cast_add,Nat.cast_one,sub_sub,add_comm] using ht

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem reset_trace (as bs af bf : List Bool)
    (hb : bs.length=as.length) (hf : af.length=as.length) (hg : bf.length=as.length)
    (al ar bl br afl afr bfl bfr : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 3*as.length+3, Trace t
      (cfg .left ⟨symbols as++al,ar⟩ ⟨symbols bs++bl,br⟩
        ⟨symbols af++.start::afl,afr⟩ ⟨symbols bf++bfl,bfr⟩ pos).denote
      (cfg .done ⟨al,(symbols as).reverse++ar⟩ ⟨bl,(symbols bs).reverse++br⟩
        ⟨.start::afl,(symbols af).reverse++afr⟩ ⟨bfl,(symbols bf).reverse++bfr⟩
        (fun p => pos p-as.length)).denote :=
  NativeZipper.trace_of_run program (rewind_run as bs af bf hb hf hg al ar bl br afl afr bfl bfr pos)

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 4) Label.left
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=4 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=6 := by
  refine ⟨rfl,rfl,?_⟩
  change Fintype.card Label-1+1=6
  decide +kernel

theorem native_reset (as bs af bf : List Bool)
    (hb : bs.length=as.length) (hf : af.length=as.length) (hg : bf.length=as.length)
    (al ar bl br afl afr bfl bfr : List (Sym Bool)) (pos : Fin 4 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3*as.length+3,
      Transpose.stepN nativeMachine input t
        ((cfg .left ⟨symbols as++al,ar⟩ ⟨symbols bs++bl,br⟩
          ⟨symbols af++.start::afl,afr⟩ ⟨symbols bf++bfl,bfr⟩ pos).denote.denote
          nativeEncoding program inputPos outRev)=
        some ((cfg .done ⟨al,(symbols as).reverse++ar⟩ ⟨bl,(symbols bs).reverse++br⟩
          ⟨.start::afl,(symbols af).reverse++afr⟩ ⟨bfl,(symbols bf).reverse++bfr⟩
          (fun p => pos p-as.length)).denote.denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done ⟨al,(symbols as).reverse++ar⟩ ⟨bl,(symbols bs).reverse++br⟩
          ⟨.start::afl,(symbols af).reverse++afr⟩ ⟨bfl,(symbols bf).reverse++bfr⟩
          (fun p => pos p-as.length)).denote.denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := reset_trace as bs af bf hb hf hg al ar bl br afl afr bfl bfr pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

end TransposeFollowup.NativeMatchingXorReset
