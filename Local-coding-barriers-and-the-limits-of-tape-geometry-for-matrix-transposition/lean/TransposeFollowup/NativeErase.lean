import TransposeFollowup.NativeBuffer

/-! Reuse the archived eight-state eraser and lift its exact run to the
original tape model with absolute head restoration. The final tape is
blank, including both markers; no new START marker is inserted. -/

namespace TransposeFollowup.NativeErase

open FixedTapeCompiler
open CopyMachine (Sym Tape)
open NativeCounter (Anchored anchor_left anchor_right anchor_write_left)
set_option autoImplicit false

abbrev Label := Microcode.EraseFamily.Label
abbrev program := Microcode.EraseFamily.program

def Inv (c : Microcode.Config (Fin 1) Label) : Prop :=
  if c.pc=0 then True else Anchored (c.tapes 0) ∧ NativeBuffer.guard c.pc (c.tapes 0)

theorem invariant_step (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    Inv (Microcode.step program c) := by
  rcases c with ⟨pc, bank⟩
  fin_cases pc
  all_goals simp only [Inv, NativeBuffer.guard] at hc
  all_goals simp only [Microcode.step, program, Microcode.EraseFamily.program,
    Microcode.EraseFamily.instruction, Microcode.Action.apply]
  · simp [Inv]
  · exact hc
  · cases hr : (bank 0).read <;> simp_all [Inv, NativeBuffer.guard, Anchored]
  · simpa [Inv, NativeBuffer.guard, Microcode.single] using anchor_right (bank 0) hc.1
  · simpa [Inv, NativeBuffer.guard, Microcode.single] using anchor_write_left (bank 0) .blank hc.2
  · cases hr : (bank 0).read <;> simp_all [Inv, NativeBuffer.guard, Anchored]
  · simpa [Inv, NativeBuffer.guard, Microcode.single] using anchor_write_left (bank 0) .blank hc.2
  · simp [Inv]

theorem invariant_safe (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    NativeZipper.SafeLeft program c := by
  intro acts next hp t hm
  have ht : t=0 := Subsingleton.elim _ _
  subst t
  rcases c with ⟨pc, bank⟩
  fin_cases pc
  all_goals simp only [program, Microcode.EraseFamily.program, Microcode.EraseFamily.instruction] at hp
  all_goals simp at hp
  all_goals obtain ⟨rfl, rfl⟩ := hp
  all_goals simp only [Microcode.single, ite_true] at hm
  all_goals try contradiction
  all_goals
    have hmem : Sym.start ∈ (bank 0).left := by simpa [Inv, NativeBuffer.guard] using hc.2
    exact List.ne_nil_of_mem hmem

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨Microcode.focus pc 0 word (fun _ => ⟨[], []⟩), pos⟩

theorem erase_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (4*xs.length+4) (cfg 2 (Counter.marked xs) pos) =
      cfg 0 (NativeBuffer.erased xs.length) pos := by
  have hi : Inv (cfg 2 (Counter.marked xs) pos).core := by
    simp [Inv, NativeBuffer.guard, Anchored, cfg, Microcode.focus, Counter.marked]
  have hl : NativeZipper.Located (fun t => pos t-1) (cfg 2 (Counter.marked xs) pos) := by
    intro t; fin_cases t
    simp [cfg, Microcode.focus, Counter.marked]
  have h := NativeZipper.lift_run program (fun t => pos t-1) Inv invariant_step invariant_safe
    (4*xs.length+4) (cfg 2 (Counter.marked xs) pos) (cfg 0 (NativeBuffer.erased xs.length) pos).core
    hi hl (Microcode.EraseFamily.fragment.exact xs [] (fun _ => ⟨[], []⟩))
  rw [h]
  congr 1
  funext t; fin_cases t
  simp [cfg, Microcode.focus, NativeBuffer.erased]

theorem erased_denote (m : ℕ) : (NativeBuffer.erased m).denote = (⟨[], []⟩ : Tape Bool).denote := by
  simp [NativeBuffer.erased, Tape.denote, Turing.Tape.mk₂, EraseStream.blanks_eq_nil]
  exact congrArg (fun a => Turing.Tape.mk' a (Turing.ListBlank.mk [])) (EraseStream.blanks_eq_nil 1)

theorem cfg_erased_denote (m : ℕ) (pos : Fin 1 → ℤ) :
    (cfg 0 (NativeBuffer.erased m) pos).denote = (cfg 0 ⟨[], []⟩ pos).denote := by
  unfold NativeZipper.Config.denote Microcode.Config.denote cfg Microcode.focus
  congr 2
  funext t; fin_cases t
  exact erased_denote m

theorem erase_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 4*xs.length+4,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg 2 (Counter.marked xs) pos).denote (cfg 0 ⟨[], []⟩ pos).denote := by
  obtain ⟨t, ht, htr⟩ := NativeZipper.trace_of_run program (erase_run xs pos)
  exact ⟨t, ht, by simpa only [cfg_erased_denote] using htr⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Fin 1) (2 : Label)
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=8 ∧ nativeEncoding.label 2=0 := by
  refine ⟨rfl, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_erase (xs : List Bool) (pos : Fin 1 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+4,
      Transpose.stepN nativeMachine input t
        ((cfg 2 (Counter.marked xs) pos).denote.denote nativeEncoding program inputPos outRev) =
        some ((cfg 0 ⟨[], []⟩ pos).denote.denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg 0 ⟨[], []⟩ pos).denote.denote nativeEncoding program inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := erase_trace xs pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Fin 1 ↪ U) (labels : Label → J)
    (targetProgram : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc≠.halt → program pc≠.reject →
      targetProgram (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Fin 1 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+4,
      Transpose.stepN (NativeMicrocode.machine encoding targetProgram) input t
        ((MicrocodeEmbedding.embed ports labels (cfg 2 (Counter.marked xs) pos).denote frame).denote
          encoding targetProgram inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels (cfg 0 ⟨[], []⟩ pos).denote frame).denote
          encoding targetProgram inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := erase_trace xs pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program targetProgram
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeErase
