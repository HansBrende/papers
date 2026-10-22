import TransposeFollowup.FiniteProgramEncodingCore

/-! Zipper proofs with explicit absolute head positions. The position field
is updated only by the finite microinstruction, and the whole configuration
refines the checked native compiler. -/

namespace TransposeFollowup.NativeZipper

open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

def shiftPositions (pos : T → ℤ) (d : ℤ) : T → ℤ := fun t => pos t + d

@[simp] theorem shiftPositions_zero (pos : T → ℤ) : shiftPositions pos 0 = pos := by
  funext t; simp [shiftPositions]

theorem shiftPositions_add (pos : T → ℤ) (a b : ℤ) :
    shiftPositions (shiftPositions pos a) b = shiftPositions pos (a + b) := by
  funext t; simp [shiftPositions, add_assoc]

structure Config (T L : Type*) where
  core : Microcode.Config T L
  pos : T → ℤ

def step (p : Microcode.Program T L) (c : Config T L) : Config T L where
  core := Microcode.step p c.core
  pos := match p c.core.pc with
    | .act actions _ => fun t => (NativeMicrocode.direction (actions t).move).shift (c.pos t)
    | _ => c.pos

def Config.denote (c : Config T L) : NativeMicrocode.Config T L where
  core := c.core.denote
  pos := c.pos

theorem step_denote (p : Microcode.Program T L) (c : Config T L) :
    (step p c).denote = NativeMicrocode.step p c.denote := by
  exact congrArg₂ NativeMicrocode.Config.mk (Microcode.step_refines p c.core) rfl

abbrev run (p : Microcode.Program T L) := OperationalTrace.run (step p)

theorem run_denote (p : Microcode.Program T L) (n : ℕ) (c : Config T L) :
    (run p n c).denote = NativeMicrocode.run p n c.denote := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simpa only [OperationalTrace.run, step_denote] using ih (step p c)

theorem run_add (p : Microcode.Program T L) (n m : ℕ) (c : Config T L) :
    run p (n + m) c = run p m (run p n c) := OperationalTrace.run_add _ _ _ _

theorem trace_of_run (p : Microcode.Program T L) {n : ℕ} {c d : Config T L}
    (h : run p n c = d) :
    ∃ t ≤ n, OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p)
      t c.denote d.denote := by
  have hr : NativeMicrocode.run p n c.denote = d.denote := by
    rw [← run_denote, h]
  obtain ⟨t, ht, htr⟩ := OperationalTrace.prune (NativeMicrocode.step p)
    (NativeMicrocode.Active p) (NativeMicrocode.inactive_fixed p) n c.denote
  change OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p)
    t c.denote (NativeMicrocode.run p n c.denote) at htr
  rw [hr] at htr
  exact ⟨t, ht, htr⟩

/-- A stopped zipper computation supplies a paid native subroutine run
from the specified prepared configuration. This does not load its inputs. -/
theorem stopped_subroutine {k q : ℕ} (e : NativeMicrocode.Encoding T L k q)
    (p : Microcode.Program T L) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    {n : ℕ} {c d : Config T L} (h : run p n c = d)
    (hh : ¬ NativeMicrocode.Active p d.denote) :
    ∃ t ≤ n, Transpose.stepN (NativeMicrocode.machine e p) w t
        (c.denote.denote e p inputPos outRev) =
        some (d.denote.denote e p inputPos outRev) ∧
      Transpose.step (NativeMicrocode.machine e p) w
        (d.denote.denote e p inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := trace_of_run p h
  exact ⟨t, ht, NativeMicrocode.trace_stepN e p w inputPos outRev htr,
    (NativeMicrocode.step_none_iff e p w inputPos outRev d.denote).mpr hh⟩

end TransposeFollowup.NativeZipper
