import TransposeFollowup.NativeCounter
import FixedTapeCompiler.MicroMappedAppend

/-! Reuse the archived eight-label mapped append. Its source head returns
to its original absolute position; its target head advances by the source
length, regardless of the existing target prefix. No rewind is hidden. -/

namespace TransposeFollowup.NativeMappedAppend

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open Microcode.MappedAppendFamily (Label program fragment)
open NativeCounter (Anchored anchor_left anchor_right)
set_option autoImplicit false

def guard (pc : Label) (w : Tape Bool) : Prop :=
  if pc = 1 ∨ pc = 2 ∨ pc = 4 then Sym.start ∈ w.left else True

def Inv (c : Microcode.Config (Fin 2) Label) : Prop :=
  Anchored (c.tapes 0) ∧ guard c.pc (c.tapes 0)

theorem invariant_step (f : Bool → Bool) (c : Microcode.Config (Fin 2) Label)
    (hc : Inv c) : Inv (Microcode.step (program f) c) := by
  rcases c with ⟨pc, bank⟩
  fin_cases pc
  all_goals simp only [Inv, guard] at hc
  all_goals simp only [Microcode.step, program, Microcode.MappedAppendFamily.instruction,
    id_eq, Microcode.twins, Microcode.single, Microcode.emitBit, Microcode.Action.apply]
  · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored]
  · simpa [Inv, guard] using anchor_right (bank 0) hc.1
  · simpa [Inv, guard] using anchor_right (bank 0) hc.1
  · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored]
  · simpa [Inv, guard] using anchor_left (bank 0) hc.2
  · simpa [Inv, guard] using anchor_right (bank 0) hc.1
  · exact hc
  · exact hc

theorem invariant_safe (f : Bool → Bool) (c : Microcode.Config (Fin 2) Label)
    (hc : Inv c) : NativeZipper.SafeLeft (program f) c := by
  intro acts next hp t hm
  rcases c with ⟨pc, bank⟩
  fin_cases pc
  all_goals simp only [program, Microcode.MappedAppendFamily.instruction, id_eq] at hp
  all_goals try contradiction
  all_goals cases hp
  all_goals fin_cases t <;> simp_all [Microcode.twins, Microcode.single, Microcode.emitBit]
  exact List.ne_nil_of_mem hc.2

def cfg (pc : Label) (source target : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeZipper.Config (Fin 2) Label :=
  ⟨Microcode.focus2 pc 0 1 source target (fun _ => ⟨[], []⟩), pos⟩

def finalPositions (pos : Fin 2 → ℤ) (n : ℕ) : Fin 2 → ℤ :=
  fun t => pos t + if t = 1 then (n : ℤ) else 0

theorem append_run (f : Bool → Bool) (xs : List Bool) (pre : List (Sym Bool))
    (pos : Fin 2 → ℤ) :
    NativeZipper.run (program f) (4*xs.length+5)
      (cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos) =
      cfg 7 (Counter.marked xs) ⟨(symbols (xs.map f)).reverse ++ pre, []⟩
        (finalPositions pos xs.length) := by
  let origin : Fin 2 → ℤ := fun t => pos t - if t = 0 then 1 else pre.length
  have hi : Inv (cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos).core := by
    simp [Inv, guard, Anchored, cfg, Microcode.focus2, Microcode.focus, Counter.marked]
  have hl : NativeZipper.Located origin (cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos) := by
    intro t
    fin_cases t <;> simp [origin, cfg, Microcode.focus2, Microcode.focus, Counter.marked]
  have hr := (fragment f).exact (by decide : (0 : Fin 2) ≠ 1) xs pre (fun _ => ⟨[], []⟩)
  have h := NativeZipper.lift_run (program f) origin Inv (invariant_step f) (invariant_safe f)
    (4*xs.length+5) (cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos)
    (cfg 7 (Counter.marked xs) ⟨(symbols (xs.map f)).reverse ++ pre, []⟩
      (finalPositions pos xs.length)).core hi hl hr
  rw [h]
  congr 1
  funext t
  fin_cases t <;> simp [origin, cfg, finalPositions, Microcode.focus2, Microcode.focus,
    Counter.marked, symbols]

theorem append_trace (f : Bool → Bool) (xs : List Bool) (pre : List (Sym Bool))
    (pos : Fin 2 → ℤ) :
    ∃ t ≤ 4*xs.length+5,
      OperationalTrace.Trace (NativeMicrocode.step (program f)) (NativeMicrocode.Active (program f)) t
        (cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos).denote
        (cfg 7 (Counter.marked xs) ⟨(symbols (xs.map f)).reverse ++ pre, []⟩
          (finalPositions pos xs.length)).denote :=
  NativeZipper.trace_of_run (program f) (append_run f xs pre pos)

noncomputable def nativeEncoding : NativeMicrocode.Encoding (Fin 2) Label 2 7 where
  port := Equiv.refl _
  label := Equiv.refl _

noncomputable def nativeMachine (f : Bool → Bool) : Transpose.TM :=
  NativeMicrocode.machine nativeEncoding (program f)

theorem fixed_resources (f : Bool → Bool) : (nativeMachine f).k = 2 ∧
    (nativeMachine f).g+1 = 5 ∧ (nativeMachine f).q+1 = 8 ∧ nativeEncoding.label 0 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem native_append (f : Bool → Bool) (xs : List Bool) (pre : List (Sym Bool))
    (pos : Fin 2 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+5,
      Transpose.stepN (nativeMachine f) input t
        ((cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos).denote.denote
          nativeEncoding (program f) inputPos outRev) =
        some ((cfg 7 (Counter.marked xs) ⟨(symbols (xs.map f)).reverse ++ pre, []⟩
          (finalPositions pos xs.length)).denote.denote nativeEncoding (program f) inputPos outRev) ∧
      Transpose.step (nativeMachine f) input
        ((cfg 7 (Counter.marked xs) ⟨(symbols (xs.map f)).reverse ++ pre, []⟩
          (finalPositions pos xs.length)).denote.denote nativeEncoding (program f) inputPos outRev) = none := by
  apply NativeZipper.stopped_subroutine nativeEncoding (program f) input inputPos outRev
    (append_run f xs pre pos)
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Fin 2 ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (f : Bool → Bool)
    (hc : ∀ pc, program f pc ≠ .halt → program f pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program f pc))
    (xs : List Bool) (pre : List (Sym Bool)) (pos : Fin 2 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+5,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg 0 (Counter.marked xs) ⟨pre, []⟩ pos).denote
          frame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg 7 (Counter.marked xs) ⟨(symbols (xs.map f)).reverse ++ pre, []⟩
            (finalPositions pos xs.length)).denote frame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := append_trace f xs pre pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program f) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeMappedAppend
