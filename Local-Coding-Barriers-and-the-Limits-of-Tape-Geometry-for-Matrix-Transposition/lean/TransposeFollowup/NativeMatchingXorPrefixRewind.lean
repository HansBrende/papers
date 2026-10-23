import TransposeFollowup.NativeClosedStream

/-! Rewind a marked prefix without changing its arbitrary data suffix.
This reuses the existing fixed rewind controller; the return movement is paid. -/
namespace TransposeFollowup.NativeMatchingXorPrefixRewind
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def splitWord (A B : List Bool) : Tape Bool :=
  ⟨(symbols A).reverse++[.start],symbols B++[.stop]⟩

theorem relative_run (A B : List Bool) :
    Microcode.run NativeSealBack.program (2*A.length+4)
      (NativeSealBack.cfg .back (splitWord A B) (fun _ => 0)).core=
      (NativeSealBack.cfg .done (Counter.marked (A++B)) (fun _ => 0)).core := by
  cases B with
  | nil => simpa [splitWord,NativeClosedStream.word,symbols] using NativeClosedStream.rewind_relative A
  | cons b B =>
    have h := NativeSealBack.rewind.exact A.reverse (.data b) (symbols B++[.stop]) []
        (fun _ : Fin 1 => (⟨[],[]⟩ : Tape Bool)) (Or.inr ⟨b,rfl⟩)
    simpa only [NativeSealBack.cfg,splitWord,Counter.marked,List.length_reverse,
      List.reverse_reverse,symbols,List.map_reverse,List.map_append,List.map_cons,
      List.append_assoc,List.cons_append] using h

theorem rewind_run (A B : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run NativeSealBack.program (2*A.length+4)
      (NativeSealBack.cfg .back (splitWord A B) pos)=
      NativeSealBack.cfg .done (Counter.marked (A++B)) (fun t => pos t-A.length) := by
  let origin : Fin 1 → ℤ := fun t => pos t-(A.length+1)
  have hi : NativeSealBack.Inv (NativeSealBack.cfg .back (splitWord A B) pos).core := by
    simp [NativeSealBack.Inv,NativeSealBack.guard,NativeCounter.Anchored,
      NativeSealBack.cfg,splitWord,Microcode.focus]
  have hl : NativeZipper.Located origin (NativeSealBack.cfg .back (splitWord A B) pos) := by
    intro t
    fin_cases t
    simp [origin,NativeSealBack.cfg,splitWord,Microcode.focus,symbols]
  have h := NativeZipper.lift_run NativeSealBack.program origin NativeSealBack.Inv
    NativeSealBack.invariant_step NativeSealBack.invariant_safe (2*A.length+4)
    (NativeSealBack.cfg .back (splitWord A B) pos)
    (NativeSealBack.cfg .done (Counter.marked (A++B)) (fun t => pos t-A.length)).core
    hi hl (relative_run A B)
  rw [h]
  congr 1
  funext t
  fin_cases t
  simp [origin,NativeSealBack.cfg,Microcode.focus,Counter.marked]
  ring

theorem rewind_trace (A B : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*A.length+4,
      OperationalTrace.Trace (NativeMicrocode.step NativeSealBack.program)
        (NativeMicrocode.Active NativeSealBack.program) t
        (NativeSealBack.cfg .back (splitWord A B) pos).denote
        (NativeSealBack.cfg .done (Counter.marked (A++B)) (fun t => pos t-A.length)).denote :=
  NativeZipper.trace_of_run NativeSealBack.program (rewind_run A B pos)

end TransposeFollowup.NativeMatchingXorPrefixRewind
