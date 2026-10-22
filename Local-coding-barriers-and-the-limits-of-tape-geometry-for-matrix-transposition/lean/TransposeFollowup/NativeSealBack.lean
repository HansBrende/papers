import TransposeFollowup.NativeCounter

/-! One STOP write followed by the archived rewind fragment. The theorem
accounts for the actual absolute displacement from the end to the first bit. -/

namespace TransposeFollowup.NativeSealBack

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeCounter (Anchored anchor_left anchor_right)
set_option autoImplicit false

inductive Label | seal | back | left | right | done | reject
  deriving DecidableEq

instance : Fintype Label where
  elems := {.seal, .back, .left, .right, .done, .reject}
  complete := by intro x; cases x <;> simp

def program : Microcode.Program (Fin 1) Label
  | .seal => .act (Microcode.single 0 ⟨some .stop, .stay⟩) .back
  | .back => .read 0 (fun s => match s with
      | .start => .right | .stop | .data _ => .left | .blank => .reject)
  | .left => .act (Microcode.single 0 ⟨none, .left⟩) .back
  | .right => .act (Microcode.single 0 ⟨none, .right⟩) .done
  | .done => .halt
  | .reject => .reject

def rewind : Microcode.Rewind program 0 .back .done :=
  ⟨.left, .right, .reject, rfl, rfl, rfl⟩

def guard (pc : Label) (w : Tape Bool) : Prop :=
  match pc with | .seal | .left => Sym.start ∈ w.left | _ => True

def Inv (c : Microcode.Config (Fin 1) Label) : Prop :=
  Anchored (c.tapes 0) ∧ guard c.pc (c.tapes 0)

theorem invariant_step (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    Inv (Microcode.step program c) := by
  rcases c with ⟨pc, bank⟩
  cases pc
  all_goals simp only [Inv, guard] at hc
  all_goals simp only [Microcode.step, program, Microcode.single, Microcode.Action.apply]
  · exact ⟨Or.inl hc.2, trivial⟩
  · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored]
  · simpa [Inv, guard] using anchor_left (bank 0) hc.2
  · simpa [Inv, guard] using anchor_right (bank 0) hc.1
  · exact hc
  · exact hc

theorem invariant_safe (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    NativeZipper.SafeLeft program c := by
  intro acts next hp t hm
  have ht : t = 0 := Subsingleton.elim _ _
  subst t
  rcases c with ⟨pc, bank⟩
  cases pc
  all_goals simp only [program] at hp
  all_goals try contradiction
  all_goals cases hp
  all_goals simp only [Microcode.single, ite_true] at hm
  all_goals try contradiction
  exact List.ne_nil_of_mem hc.2

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨Microcode.focus pc 0 word (fun _ => ⟨[], []⟩), pos⟩

def openWord (xs : List Bool) : Tape Bool := ⟨(symbols xs).reverse ++ [.start], []⟩

theorem relative_run (xs : List Bool) :
    Microcode.run program (2*xs.length+5)
      (cfg .seal (openWord xs) (fun _ => 0)).core =
      (cfg .done (Counter.marked xs) (fun _ => 0)).core := by
  rw [show 2*xs.length+5 = 1+(2*xs.length+4) by omega, Microcode.run_add]
  have he : Microcode.run program 1 (cfg .seal (openWord xs) (fun _ => 0)).core =
      Microcode.focus .back 0 ⟨(symbols xs).reverse ++ [.start], [.stop]⟩ (fun _ => ⟨[], []⟩) := by
    change Microcode.step program (Microcode.focus Label.seal (0 : Fin 1)
      (openWord xs) (fun _ => ⟨[], []⟩)) = _
    rw [Microcode.at_act program .seal .back 0 _ rfl]
    rfl
  rw [he]
  exact rewind.from_end xs [] (fun _ => ⟨[], []⟩)

theorem seal_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*xs.length+5) (cfg .seal (openWord xs) pos) =
      cfg .done (Counter.marked xs) (fun t => pos t-xs.length) := by
  let origin : Fin 1 → ℤ := fun t => pos t-(xs.length+1)
  have hi : Inv (cfg .seal (openWord xs) pos).core := by
    simp [Inv, guard, Anchored, cfg, openWord, Microcode.focus]
  have hl : NativeZipper.Located origin (cfg .seal (openWord xs) pos) := by
    intro t; fin_cases t
    simp [origin, cfg, openWord, Microcode.focus, symbols]
  have h := NativeZipper.lift_run program origin Inv invariant_step invariant_safe
    (2*xs.length+5) (cfg .seal (openWord xs) pos)
    (cfg .done (Counter.marked xs) (fun t => pos t-xs.length)).core hi hl (relative_run xs)
  rw [h]
  congr 1
  funext t; fin_cases t
  simp [origin, cfg, Microcode.focus, Counter.marked]
  ring

theorem seal_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*xs.length+5,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .seal (openWord xs) pos).denote
        (cfg .done (Counter.marked xs) (fun t => pos t-xs.length)).denote :=
  NativeZipper.trace_of_run program (seal_run xs pos)

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Fin 1) Label.seal
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k = 1 ∧ nativeMachine.g+1 = 5 ∧
    nativeMachine.q+1 = 6 ∧ nativeEncoding.label .seal = 0 := by
  refine ⟨rfl, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_seal (xs : List Bool) (pos : Fin 1 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*xs.length+5,
      Transpose.stepN nativeMachine input t
        ((cfg .seal (openWord xs) pos).denote.denote nativeEncoding program inputPos outRev) =
        some ((cfg .done (Counter.marked xs) (fun t => pos t-xs.length)).denote.denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (Counter.marked xs) (fun t => pos t-xs.length)).denote.denote
          nativeEncoding program inputPos outRev) = none := by
  apply NativeZipper.stopped_subroutine nativeEncoding program input inputPos outRev (seal_run xs pos)
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Fin 1 ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Fin 1 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*xs.length+5,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .seal (openWord xs) pos).denote frame).denote
          encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (Counter.marked xs) (fun t => pos t-xs.length)).denote frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := seal_trace xs pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeSealBack
