import TransposeFollowup.NativeZipper

/-! Lift existing zipper execution proofs to absolute head positions.
The left-list length measures displacement only while a left move never
passes the represented left boundary. That condition is explicit here. -/

namespace TransposeFollowup.NativeZipper

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false
variable {T L : Type*}

def SafeLeft (p : Microcode.Program T L) (c : Microcode.Config T L) : Prop :=
  ∀ acts next, p c.pc = .act acts next →
    ∀ t, (acts t).move = .left → (c.tapes t).left ≠ []

def Located (origin : T → ℤ) (c : Config T L) : Prop :=
  ∀ t, c.pos t = origin t + ((c.core.tapes t).left.length : ℤ)

theorem action_left_length (a : Microcode.Action) (w : Tape Bool)
    (h : a.move = .left → w.left ≠ []) :
    ((a.apply w).left.length : ℤ) =
      (NativeMicrocode.direction a.move).shift (w.left.length : ℤ) := by
  rcases a with ⟨write, move⟩
  cases w with | mk left right =>
    cases move <;> cases write <;>
      simp_all [Microcode.Action.apply, Tape.write, Tape.moveLeft, Tape.moveRight,
        NativeMicrocode.direction, Transpose.Dir.shift]
    all_goals cases left <;> simp_all

theorem step_located (p : Microcode.Program T L) (origin : T → ℤ)
    (c : Config T L) (hc : Located origin c) (hs : SafeLeft p c.core) :
    Located origin (step p c) := by
  intro t
  cases hp : p c.core.pc with
  | act acts next =>
    have ha := action_left_length (acts t) (c.core.tapes t) (hs acts next hp t)
    simp only [step, Microcode.step, hp]
    rw [hc t, ha]
    cases hm : (acts t).move <;>
      simp [NativeMicrocode.direction, Transpose.Dir.shift, sub_eq_add_neg, add_assoc]
  | read port next => simpa [step, Microcode.step, hp] using hc t
  | jump next => simpa [step, Microcode.step, hp] using hc t
  | halt => simpa [step, Microcode.step, hp] using hc t
  | reject => simpa [step, Microcode.step, hp] using hc t

theorem run_core (p : Microcode.Program T L) (n : ℕ) (c : Config T L) :
    (run p n c).core = Microcode.run p n c.core := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simpa only [run, Microcode.run, OperationalTrace.run, step] using (ih (step p c))

theorem run_located (p : Microcode.Program T L) (origin : T → ℤ)
    (Inv : Microcode.Config T L → Prop)
    (preserve : ∀ c, Inv c → Inv (Microcode.step p c))
    (safe : ∀ c, Inv c → SafeLeft p c)
    (n : ℕ) (c : Config T L) (hi : Inv c.core) (hl : Located origin c) :
    Located origin (run p n c) := by
  induction n generalizing c with
  | zero => exact hl
  | succ n ih =>
    exact ih (step p c) (preserve c.core hi) (step_located p origin c hl (safe c.core hi))

/-- An old relative execution theorem plus a preserved safe-boundary
invariant supplies the exact absolute final position. -/
theorem lift_run (p : Microcode.Program T L) (origin : T → ℤ)
    (Inv : Microcode.Config T L → Prop)
    (preserve : ∀ c, Inv c → Inv (Microcode.step p c))
    (safe : ∀ c, Inv c → SafeLeft p c)
    (n : ℕ) (c : Config T L) (d : Microcode.Config T L)
    (hi : Inv c.core) (hl : Located origin c) (hr : Microcode.run p n c.core = d) :
    run p n c = ⟨d, fun t => origin t + ((d.tapes t).left.length : ℤ)⟩ := by
  have hcore : (run p n c).core = d := (run_core p n c).trans hr
  have hpos := run_located p origin Inv preserve safe n c hi hl
  cases he : run p n c with
  | mk core pos =>
    simp only [he] at hcore hpos
    subst core
    congr 1
    exact funext hpos

end TransposeFollowup.NativeZipper
