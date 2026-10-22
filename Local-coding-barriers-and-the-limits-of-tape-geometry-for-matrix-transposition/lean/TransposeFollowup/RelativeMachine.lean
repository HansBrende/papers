import TransposeFollowup.AbsoluteTape
import Transpose.Tape.Run

/-! Relative tapes implement the original finite TM transition table exactly.
States, input/output conventions and absolute head positions are retained.
This is a semantic representation theorem, not an arithmetic time estimate. -/

namespace TransposeFollowup
namespace RelativeMachine

set_option autoImplicit false

structure Config (M : Transpose.TM) where
  state : Fin (M.q + 1)
  inPos : ℤ
  tapes : Fin M.k → Turing.Tape (Fin (M.g + 1))
  workPos : Fin M.k → ℤ
  outRev : List Bool

variable {M : Transpose.TM}

def Config.denote (c : Config M) : Transpose.Config M where
  state := c.state
  inPos := c.inPos
  work := fun i => AbsoluteTape.cells (c.tapes i) (c.workPos i)
  workPos := c.workPos
  outRev := c.outRev

def init (M : Transpose.TM) : Config M where
  state := 0
  inPos := 0
  tapes := fun _ => AbsoluteTape.blank
  workPos := fun _ => 0
  outRev := []

def step (w : List Bool) (c : Config M) : Option (Config M) :=
  match M.δ c.state (Transpose.readInput w c.inPos) (fun i => (c.tapes i).head) with
  | none => none
  | some (s, d, acts, o) => some
      { state := s
        inPos := d.shift c.inPos
        tapes := fun i => AbsoluteTape.move (acts i).2 ((c.tapes i).write (acts i).1)
        workPos := fun i => (acts i).2.shift (c.workPos i)
        outRev := match o with | none => c.outRev | some b => b :: c.outRev }

theorem init_denote (M : Transpose.TM) : (init M).denote = Transpose.init M := by
  unfold init Config.denote Transpose.init
  congr 1
  funext i z
  exact AbsoluteTape.blank_cells 0 z

theorem step_denote (w : List Bool) (c : Config M) :
    (step w c).map Config.denote = Transpose.step M w c.denote := by
  simp only [step, Transpose.step, Config.denote, AbsoluteTape.scanned]
  cases h : M.δ c.state (Transpose.readInput w c.inPos) (fun i => (c.tapes i).head) with
  | none => rfl
  | some a =>
    rcases a with ⟨s, d, acts, o⟩
    simp only [Option.map_some, Config.denote]
    congr 2
    funext i z
    exact AbsoluteTape.write_move_cells (acts i).1 (acts i).2 (c.tapes i) (c.workPos i) z

def stepN (w : List Bool) : ℕ → Config M → Option (Config M)
  | 0, c => some c
  | t + 1, c => match step w c with
    | none => none
    | some c' => stepN w t c'

theorem stepN_denote (w : List Bool) (t : ℕ) (c : Config M) :
    (stepN w t c).map Config.denote = Transpose.stepN M w t c.denote := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [stepN, Transpose.stepN, ← step_denote]
    cases h : step w c with
    | none => rfl
    | some c' => exact ih c'

theorem step_none_iff (w : List Bool) (c : Config M) :
    step w c = none ↔ Transpose.step M w c.denote = none := by
  rw [← step_denote, Option.map_eq_none_iff]

def ComputesWithin (M : Transpose.TM) (w out : List Bool) (T : ℕ) : Prop :=
  ∃ t, t ≤ T ∧ ∃ c, stepN w t (init M) = some c ∧
    step w c = none ∧ c.outRev.reverse = out

theorem computesWithin_iff (M : Transpose.TM) (w out : List Bool) (T : ℕ) :
    ComputesWithin M w out T ↔ Transpose.ComputesWithin M w out T := by
  constructor
  · rintro ⟨t, ht, c, hc, hh, ho⟩
    refine ⟨t, ht, c.denote, ?_, (step_none_iff w c).mp hh, ho⟩
    rw [← init_denote M, ← stepN_denote, hc]
    rfl
  · rintro ⟨t, ht, c, hc, hh, ho⟩
    rw [← init_denote M, ← stepN_denote] at hc
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hc
    subst c
    exact ⟨t, ht, d, hd, (step_none_iff w d).mpr hh, ho⟩

def next (w : List Bool) (c : Config M) : Config M := (step w c).getD c

theorem next_denote (w : List Bool) (c : Config M) :
    (next w c).denote = Transpose.Tape.Impl.next M w c.denote := by
  unfold next Transpose.Tape.Impl.next
  rw [← step_denote]
  cases h : step w c <;> rfl

def run (M : Transpose.TM) (w : List Bool) : ℕ → Config M
  | 0 => init M
  | t + 1 => next w (run M w t)

theorem run_denote (M : Transpose.TM) (w : List Bool) (t : ℕ) :
    (run M w t).denote = Transpose.Tape.run M w t := by
  induction t with
  | zero => exact init_denote M
  | succ t ih => rw [run, next_denote, Transpose.Tape.Impl.run_succ, ih]

theorem run_workPos (M : Transpose.TM) (w : List Bool) (t : ℕ) (i : Fin M.k) :
    (run M w t).workPos i = Transpose.Tape.workTraj M w t i := by
  exact congrArg (fun c : Transpose.Config M => c.workPos i) (run_denote M w t)

end RelativeMachine
end TransposeFollowup
