import TransposeFollowup.NativeSealBack
import TransposeFollowup.NativeErase
import TransposeFollowup.RowStreamBudget

/-! Native endpoints for consuming an existing closed stream. Reuse the
archived rewind and eraser tail; no new transition table is introduced. -/
namespace TransposeFollowup.NativeClosedStream
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def word (xs : List Bool) : Tape Bool := ⟨(symbols xs).reverse++[.start],[.stop]⟩

theorem word_eq (xs : List Bool) : word xs=RowStream.closedTape xs := by
  simp [word,RowStream.closedTape,symbols]

theorem rewind_relative (xs : List Bool) :
    Microcode.run NativeSealBack.program (2*xs.length+4)
      (NativeSealBack.cfg .back (word xs) (fun _ => 0)).core=
      (NativeSealBack.cfg .done (Counter.marked xs) (fun _ => 0)).core :=
  NativeSealBack.rewind.from_end xs [] (fun _ => ⟨[],[]⟩)

theorem rewind_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run NativeSealBack.program (2*xs.length+4)
      (NativeSealBack.cfg .back (word xs) pos)=
      NativeSealBack.cfg .done (Counter.marked xs) (fun t => pos t-xs.length) := by
  let origin : Fin 1 → ℤ := fun t => pos t-(xs.length+1)
  have hi : NativeSealBack.Inv (NativeSealBack.cfg .back (word xs) pos).core := by
    simp [NativeSealBack.Inv,NativeSealBack.guard,NativeCounter.Anchored,NativeSealBack.cfg,word,Microcode.focus]
  have hl : NativeZipper.Located origin (NativeSealBack.cfg .back (word xs) pos) := by
    intro t
    fin_cases t
    simp [origin,NativeSealBack.cfg,word,Microcode.focus,symbols]
  have h := NativeZipper.lift_run NativeSealBack.program origin NativeSealBack.Inv
    NativeSealBack.invariant_step NativeSealBack.invariant_safe (2*xs.length+4)
    (NativeSealBack.cfg .back (word xs) pos)
    (NativeSealBack.cfg .done (Counter.marked xs) (fun t => pos t-xs.length)).core hi hl (rewind_relative xs)
  rw [h]
  congr 1
  funext t
  fin_cases t
  simp [origin,NativeSealBack.cfg,Microcode.focus,Counter.marked]
  ring

theorem rewind_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*xs.length+4,
      OperationalTrace.Trace (NativeMicrocode.step NativeSealBack.program) (NativeMicrocode.Active NativeSealBack.program) t
        (NativeSealBack.cfg .back (RowStream.closedTape xs) pos).denote
        (NativeSealBack.cfg .done (Counter.marked xs) (fun p => pos p-xs.length)).denote := by
  simpa only [word_eq] using NativeZipper.trace_of_run NativeSealBack.program (rewind_run xs pos)

theorem erase_relative (xs : List Bool) :
    Microcode.run NativeErase.program (2*xs.length+3)
      (NativeErase.cfg 4 (word xs) (fun _ => 0)).core=
      (NativeErase.cfg 0 (NativeBuffer.erased xs.length) (fun _ => 0)).core :=
  Microcode.EraseFamily.fragment.tailCode.exact xs [] (fun _ => ⟨[],[]⟩)

theorem erase_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run NativeErase.program (2*xs.length+3)
      (NativeErase.cfg 4 (word xs) pos)=
      NativeErase.cfg 0 (NativeBuffer.erased xs.length) (fun t => pos t-xs.length) := by
  let origin : Fin 1 → ℤ := fun t => pos t-(xs.length+1)
  have hi : NativeErase.Inv (NativeErase.cfg 4 (word xs) pos).core := by
    simp [NativeErase.Inv,NativeBuffer.guard,NativeCounter.Anchored,NativeErase.cfg,word,Microcode.focus]
  have hl : NativeZipper.Located origin (NativeErase.cfg 4 (word xs) pos) := by
    intro t
    fin_cases t
    simp [origin,NativeErase.cfg,word,Microcode.focus,symbols]
  have h := NativeZipper.lift_run NativeErase.program origin NativeErase.Inv
    NativeErase.invariant_step NativeErase.invariant_safe (2*xs.length+3)
    (NativeErase.cfg 4 (word xs) pos)
    (NativeErase.cfg 0 (NativeBuffer.erased xs.length) (fun t => pos t-xs.length)).core hi hl (erase_relative xs)
  rw [h]
  congr 1
  funext t
  fin_cases t
  simp [origin,NativeErase.cfg,Microcode.focus,NativeBuffer.erased]
  ring

theorem erase_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*xs.length+3,
      OperationalTrace.Trace (NativeMicrocode.step NativeErase.program) (NativeMicrocode.Active NativeErase.program) t
        (NativeErase.cfg 4 (RowStream.closedTape xs) pos).denote
        (NativeErase.cfg 0 ⟨[],[]⟩ (fun p => pos p-xs.length)).denote := by
  simpa only [word_eq,NativeErase.cfg_erased_denote] using
    NativeZipper.trace_of_run NativeErase.program (erase_run xs pos)

end TransposeFollowup.NativeClosedStream
