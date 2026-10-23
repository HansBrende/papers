import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.NativeTrimData

/-! A fixed-control, in-place division of a nonempty little-endian binary
word by two. The old left delimiter is erased and the discarded low bit
becomes the new delimiter. Its one-cell origin change is explicit. -/
namespace TransposeFollowup.NativeExpanderShearHalf
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | left | erase | mark | done
  deriving DecidableEq

instance : Fintype Label where
  elems := {.left,.erase,.mark,.done}
  complete := by intro pc; cases pc <;> simp

def program : Microcode.Program (Fin 1) Label
  | .left => .act (fun _ => ⟨none,.left⟩) .erase
  | .erase => .act (fun _ => ⟨some .blank,.right⟩) .mark
  | .mark => .act (fun _ => ⟨some .start,.right⟩) .done
  | .done => .halt

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.Config (Fin 1) Label := ⟨⟨pc,fun _ => word⟩,pos⟩

theorem half_run (a : Bool) (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 3 (cfg .left (Counter.marked (a::xs)) pos)=
      cfg .done ⟨[.start,.blank],symbols xs++[.stop]⟩ (fun p => pos p+1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,cfg,Counter.marked,symbols,Microcode.Action.apply,Tape.write,
    Tape.moveLeft,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem marked_blank_denote (xs : List Bool) :
    (⟨[.start,.blank],symbols xs++[.stop]⟩ : Tape Bool).denote=
      (Counter.marked xs).denote := by
  unfold Tape.denote Counter.marked Turing.Tape.mk₂
  exact congrArg (fun a => Turing.Tape.mk' a (Turing.ListBlank.mk (symbols xs++[.stop])))
    (congrArg (Turing.ListBlank.cons .start) (EraseStream.blanks_eq_nil 1))

theorem half_denote (xs : List Bool) (pos : Fin 1 → ℤ) :
    (cfg .done ⟨[.start,.blank],symbols xs++[.stop]⟩ pos).denote=
      (cfg .done (Counter.marked xs) pos).denote := by
  unfold NativeZipper.Config.denote Microcode.Config.denote cfg
  congr 2
  funext p
  exact marked_blank_denote xs

theorem half_value (a : Bool) (xs : List Bool) :
    Counter.value xs=Counter.value (a::xs)/2 := by
  cases a <;> simp only [Counter.value] <;> omega

theorem normalized_tail (a : Bool) (xs : List Bool)
    (hn : NativeTrim.Normalized (a::xs)) : NativeTrim.Normalized xs := by
  rcases hn with h | ⟨pre,h⟩
  · cases h
  · cases pre with
    | nil =>
      simp only [List.nil_append,List.cons.injEq] at h
      exact Or.inl h.2
    | cons p pre =>
      simp only [List.cons_append,List.cons.injEq] at h
      exact Or.inr ⟨pre,h.2⟩

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program)
  (NativeMicrocode.Active program)

theorem half_trace (a : Bool) (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 3, Trace t (cfg .left (Counter.marked (a::xs)) pos).denote
      (cfg .done (Counter.marked xs) (fun p => pos p+1)).denote := by
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run program (half_run a xs pos)
  exact ⟨t,ht,by simpa only [half_denote] using htr⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 1) Label.left
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=4 ∧ nativeEncoding.label .left=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_half (a : Bool) (xs : List Bool) (pos : Fin 1 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3, Transpose.stepN nativeMachine input t
      ((cfg .left (Counter.marked (a::xs)) pos).denote.denote
        nativeEncoding program inputPos outRev)=
      some ((cfg .done (Counter.marked xs) (fun p => pos p+1)).denote.denote
        nativeEncoding program inputPos outRev) ∧
    Transpose.step nativeMachine input
      ((cfg .done (Counter.marked xs) (fun p => pos p+1)).denote.denote
        nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := half_trace a xs pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

end TransposeFollowup.NativeExpanderShearHalf
