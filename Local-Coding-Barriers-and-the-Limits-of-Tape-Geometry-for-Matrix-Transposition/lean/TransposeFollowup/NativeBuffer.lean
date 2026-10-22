import TransposeFollowup.NativeCounter
import TransposeFollowup.BinaryCarryRun
import FixedTapeCompiler.MicroEraseFamily

/-! Erase a marked result word, restore the absolute head and prepare its
START marker again. Every erased cell and both preparation steps are paid. -/

namespace TransposeFollowup.NativeBuffer

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeCounter (Anchored anchor_left anchor_right anchor_write_left)
set_option autoImplicit false

inductive Label
  | erase (pc : Microcode.EraseFamily.Label)
  | mark
  | done
  deriving DecidableEq, Fintype

def program : Microcode.Program (Fin 1) Label
  | .erase pc => if pc = 0 then .act (Microcode.single 0 ⟨none, .left⟩) .mark
      else Microcode.EraseFamily.instruction 0 Label.erase pc
  | .mark => .act (Microcode.single 0 ⟨some .start, .right⟩) .done
  | .done => .halt

def fragment : Microcode.Erase program 0 (.erase 2) (.erase 0) :=
  Microcode.EraseFamily.assemble program 0 Label.erase (by
    intro pc hp
    simp [program, hp])

def guard (pc : Microcode.EraseFamily.Label) (w : Tape Bool) : Prop :=
  if pc = 4 ∨ pc = 6 then Sym.start ∈ w.left else True

def Inv (c : Microcode.Config (Fin 1) Label) : Prop :=
  match c.pc with
  | .erase pc => if pc = 0 then (c.tapes 0).left ≠ []
      else Anchored (c.tapes 0) ∧ guard pc (c.tapes 0)
  | .mark | .done => True

theorem invariant_step (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    Inv (Microcode.step program c) := by
  rcases c with ⟨pc, bank⟩
  cases pc with
  | mark => simp [Microcode.step, program, Inv]
  | done => exact hc
  | erase pc =>
    fin_cases pc
    all_goals simp only [Inv, guard] at hc
    all_goals simp only [Microcode.step, program, Microcode.EraseFamily.instruction,
      Microcode.Action.apply]
    · simp [Inv]
    · exact hc
    · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored]
    · simpa [Inv, guard, Microcode.single] using anchor_right (bank 0) (by simpa using hc)
    · simpa [Inv, guard, Microcode.single] using anchor_write_left (bank 0) .blank (by simpa using hc.2)
    · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored]
    · simpa [Inv, guard, Microcode.single] using anchor_write_left (bank 0) .blank (by simpa using hc.2)
    · simp [Inv, Tape.moveRight, Microcode.single]

theorem invariant_safe (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    NativeZipper.SafeLeft program c := by
  intro acts next hp t hm
  have ht : t = 0 := Subsingleton.elim _ _
  subst t
  rcases c with ⟨pc, bank⟩
  cases pc with
  | done => simp [program] at hp
  | mark =>
    simp only [program] at hp
    cases hp
    simp [Microcode.single] at hm
  | erase pc =>
    fin_cases pc
    all_goals simp only [program, Microcode.EraseFamily.instruction] at hp
    all_goals simp at hp
    all_goals obtain ⟨rfl, rfl⟩ := hp
    all_goals simp only [Microcode.single, ite_true] at hm
    all_goals try contradiction
    · simpa [Inv] using hc
    · have hmem : Sym.start ∈ (bank 0).left := by simpa [Inv, guard] using hc.2
      exact List.ne_nil_of_mem hmem
    · have hmem : Sym.start ∈ (bank 0).left := by simpa [Inv, guard] using hc.2
      exact List.ne_nil_of_mem hmem

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.Config (Fin 1) Label :=
  ⟨Microcode.focus pc 0 word (fun _ => ⟨[], []⟩), pos⟩

def erased (m : ℕ) : Tape Bool := ⟨[.blank], List.replicate (m + 1) .blank⟩
def prepared (m : ℕ) : Tape Bool := ⟨[.start], List.replicate (m + 1) .blank⟩

theorem erase_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (4 * xs.length + 4)
      (cfg (.erase 2) (Counter.marked xs) pos) =
      cfg (.erase 0) (erased xs.length) pos := by
  have hi : Inv (cfg (.erase 2) (Counter.marked xs) pos).core := by
    simp [Inv, guard, Anchored, cfg, Microcode.focus, Counter.marked]
  have hl : NativeZipper.Located (fun t => pos t - 1)
      (cfg (.erase 2) (Counter.marked xs) pos) := by
    intro t; fin_cases t
    simp [cfg, Microcode.focus, Counter.marked]
  have h := NativeZipper.lift_run program (fun t => pos t - 1) Inv
    invariant_step invariant_safe (4 * xs.length + 4)
    (cfg (.erase 2) (Counter.marked xs) pos) (cfg (.erase 0) (erased xs.length) pos).core
    hi hl (fragment.exact xs [] (fun _ => ⟨[], []⟩))
  rw [h]
  congr 1
  funext t; fin_cases t
  simp [cfg, Microcode.focus, erased]

theorem prepare_run (m : ℕ) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg (.erase 0) (erased m) pos) =
      cfg .done (prepared m) pos := by
  simp only [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, erased, prepared, Microcode.focus, Microcode.single,
    Microcode.Action.apply, NativeMicrocode.direction, Transpose.Dir.shift, ite_true]
  congr 2
  · funext t; fin_cases t; rfl
  · funext t; fin_cases t; simp

theorem recycle_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (4 * xs.length + 6)
      (cfg (.erase 2) (Counter.marked xs) pos) = cfg .done (prepared xs.length) pos := by
  rw [show 4 * xs.length + 6 = (4 * xs.length + 4) + 2 by omega,
    NativeZipper.run_add, erase_run, prepare_run]

theorem prepared_denote (m : ℕ) : (prepared m).denote = BinaryCarry.preparedOutput.denote := by
  simp [prepared, BinaryCarry.preparedOutput, Tape.denote, Turing.Tape.mk₂,
    EraseStream.blanks_eq_nil]

theorem cfg_prepared_denote (m : ℕ) (pos : Fin 1 → ℤ) :
    (cfg .done (prepared m) pos).denote = (cfg .done BinaryCarry.preparedOutput pos).denote := by
  unfold NativeZipper.Config.denote Microcode.Config.denote cfg Microcode.focus
  congr 2
  funext t; fin_cases t
  simpa using prepared_denote m

theorem recycle_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 4 * xs.length + 6,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (.erase 2) (Counter.marked xs) pos).denote
        (cfg .done BinaryCarry.preparedOutput pos).denote := by
  obtain ⟨t, ht, htr⟩ := NativeZipper.trace_of_run program (recycle_run xs pos)
  exact ⟨t, ht, by simpa only [cfg_prepared_denote] using htr⟩

theorem fixed_resources : Fintype.card (Fin 1) = 1 ∧ Fintype.card (Sym Bool) = 5 ∧
    Fintype.card Label = 10 := by decide +kernel

theorem initialize_run (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg (.erase 0) ⟨[], []⟩ pos) =
      cfg .done BinaryCarry.preparedOutput pos := by
  simp only [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, cfg, BinaryCarry.preparedOutput, Microcode.focus, Microcode.single,
    Microcode.Action.apply, NativeMicrocode.direction, Transpose.Dir.shift, ite_true]
  congr 2
  · funext t; fin_cases t; rfl
  · funext t; fin_cases t; simp

theorem initialize_trace (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (.erase 0) ⟨[], []⟩ pos).denote
        (cfg .done BinaryCarry.preparedOutput pos).denote :=
  NativeZipper.trace_of_run program (initialize_run pos)

theorem native_recycle {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (frame : MicrocodeEmbedding.Frame U) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 4 * xs.length + 6,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((MicrocodeEmbedding.embed ports labels (cfg (.erase 2) (Counter.marked xs) pos).denote
          frame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done BinaryCarry.preparedOutput pos).denote frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := recycle_trace xs pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    frame w inputPos outRev hc htr⟩

end TransposeFollowup.NativeBuffer
