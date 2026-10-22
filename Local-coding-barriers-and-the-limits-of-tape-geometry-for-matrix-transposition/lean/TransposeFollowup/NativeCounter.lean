import TransposeFollowup.ZipperLocation
import TransposeFollowup.BinaryCompareData
import TransposeFollowup.MicrocodeEmbedding
import FixedTapeCompiler.MicroDecrementFamily

/-! The archived finite decrement controller, now with an absolute-position
proof. Arithmetic and execution cost are reused from the archive. -/

namespace TransposeFollowup.NativeCounter

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open Microcode.DecrementFamily (Label program fragment)
set_option autoImplicit false

def Anchored (w : Tape Bool) : Prop := Sym.start ∈ w.left ∨ w.read = .start

def guard (pc : Label) (w : Tape Bool) : Prop :=
  match pc with
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨5, _⟩ | ⟨8, _⟩ => Sym.start ∈ w.left
  | ⟨6, _⟩ | ⟨9, _⟩ => w.read = .start
  | _ => True

def Inv (c : Microcode.Config (Fin 1) Label) : Prop :=
  Anchored (c.tapes 0) ∧ guard c.pc (c.tapes 0)

theorem anchor_left (w : Tape Bool) (h : Sym.start ∈ w.left) :
    Anchored w.moveLeft := by
  rcases w with ⟨left, right⟩
  cases left with
  | nil => simp at h
  | cons a left => simpa [Anchored, Tape.moveLeft, Tape.read, or_comm, eq_comm] using h

theorem anchor_write_left (w : Tape Bool) (a : Sym Bool) (h : Sym.start ∈ w.left) :
    Anchored (w.write a).moveLeft := anchor_left _ h

theorem anchor_right (w : Tape Bool) (h : Anchored w) : Anchored w.moveRight := by
  unfold Anchored at *
  exact Or.inl (by simpa [Tape.moveRight, or_comm, eq_comm] using h)

theorem anchor_write_right (w : Tape Bool) (a : Sym Bool) (h : Sym.start ∈ w.left) :
    Anchored (w.write a).moveRight := anchor_right _ (Or.inl h)

theorem invariant_step (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    Inv (Microcode.step program c) := by
  rcases c with ⟨pc, bank⟩
  fin_cases pc
  all_goals simp only [Inv, guard] at hc
  all_goals simp only [Microcode.step, Microcode.DecrementFamily.program,
    Microcode.DecrementFamily.instruction, id_eq, Microcode.single,
    Microcode.Action.apply]
  · cases hr : (bank 0).read with
    | blank => simpa [Inv, guard] using hc
    | start => simpa [Inv, guard] using hc
    | stop => simp_all [Inv, guard, Anchored]; trivial
    | data b => cases b <;> simp_all [Inv, guard, Anchored] <;> trivial
  · simpa [Inv, guard] using anchor_write_right (bank 0) (.data true) hc.2
  · simpa [Inv, guard] using anchor_write_left (bank 0) (.data false) hc.2
  · simpa [Inv, guard] using anchor_left (bank 0) hc.2
  · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored] <;> trivial
  · simpa [Inv, guard] using anchor_left (bank 0) hc.2
  · simpa [Inv, guard] using anchor_right (bank 0) hc.1
  · cases hr : (bank 0).read <;> simp_all [Inv, guard, Anchored] <;> trivial
  · simpa [Inv, guard] using anchor_left (bank 0) hc.2
  · simpa [Inv, guard] using anchor_right (bank 0) hc.1
  · exact hc
  · exact hc
  · exact hc

theorem invariant_safe (c : Microcode.Config (Fin 1) Label) (hc : Inv c) :
    NativeZipper.SafeLeft program c := by
  intro acts next hp t hm
  have ht : t = 0 := Subsingleton.elim _ _
  subst t
  rcases c with ⟨pc, bank⟩
  fin_cases pc
  all_goals simp only [Microcode.DecrementFamily.program,
    Microcode.DecrementFamily.instruction, id_eq] at hp
  all_goals try contradiction
  all_goals cases hp
  all_goals simp only [Microcode.single, ite_true] at hm
  all_goals try contradiction
  all_goals
    have hmem : Sym.start ∈ (bank 0).left := hc.2
    exact List.ne_nil_of_mem hmem

def cfg (pc : Label) (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.Config (Fin 1) Label :=
  ⟨Microcode.focus pc 0 (Counter.marked xs) (fun _ => ⟨[], []⟩), pos⟩

def returnLabel (xs : List Bool) : Label := if Counter.isZero xs then 12 else 11

theorem decrement_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2 * Counter.stepCost xs) (cfg 0 xs pos) =
      cfg (returnLabel xs) (Counter.decrement xs) pos := by
  have hi : Inv (cfg 0 xs pos).core := by
    simp [Inv, guard, Anchored, cfg, Microcode.focus, Counter.marked]
  have hl : NativeZipper.Located (fun t => pos t - 1) (cfg 0 xs pos) := by
    intro t
    fin_cases t
    simp [cfg, Microcode.focus, Counter.marked]
  have hr := fragment.exact xs (fun _ => (⟨[], []⟩ : Tape Bool))
  have h := NativeZipper.lift_run program (fun t => pos t - 1) Inv
    invariant_step invariant_safe (2 * Counter.stepCost xs) (cfg 0 xs pos)
    (cfg (returnLabel xs) (Counter.decrement xs) pos).core hi hl hr
  rw [h]
  congr 1
  funext t
  fin_cases t
  simp [cfg, Microcode.focus, Counter.marked]

theorem decrement_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2 * Counter.stepCost xs,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg 0 xs pos).denote (cfg (returnLabel xs) (Counter.decrement xs) pos).denote :=
  NativeZipper.trace_of_run program (decrement_run xs pos)

theorem word_value (xs : List Bool) : Counter.value xs = BinaryCompare.value xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [Counter.value, BinaryCompare.value, Nat.ofDigits, ih, add_comm]

theorem decrement_value (xs : List Bool) (h : Counter.isZero xs = false) :
    BinaryCompare.value (Counter.decrement xs) + 1 = BinaryCompare.value xs := by
  simpa only [word_value] using Counter.decrement_value xs h

theorem zero_iff (xs : List Bool) : Counter.isZero xs = true ↔ BinaryCompare.value xs = 0 := by
  rw [← word_value]
  exact (Counter.value_zero_iff xs).symm

/-- Cost of the physical read/action-split decrement calls. Any caller
body and its loop-branch instructions are additional costs. -/
theorem native_sequence_budget (n : ℕ) (xs : List Bool) :
    2 * Counter.totalCost n xs ≤ 8 * n + 4 * xs.length := by
  have h := Counter.sequence_cost n xs
  omega

noncomputable def nativeEncoding : NativeMicrocode.Encoding (Fin 1) Label 1 12 where
  port := Equiv.refl _
  label := Equiv.refl _

noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem native_resources : nativeMachine.k = 1 ∧ nativeMachine.g + 1 = 5 ∧
    nativeMachine.q + 1 = 13 ∧ nativeEncoding.label 0 = 0 := by decide +kernel

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (frame : MicrocodeEmbedding.Frame U) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2 * Counter.stepCost xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((MicrocodeEmbedding.embed ports labels (cfg 0 xs pos).denote frame).denote
          encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (returnLabel xs) (Counter.decrement xs) pos).denote frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := decrement_trace xs pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    frame w inputPos outRev hc htr⟩

end TransposeFollowup.NativeCounter
