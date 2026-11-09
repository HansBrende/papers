import TransposeFollowup.FiniteProgramEncodingCore
import Transpose.Tape.Run
import Transpose.Tape.DefsM

/-! A finite, time-indexed local program compiled to the original native TM.
The source semantics reads the whole old tuple and performs simultaneous writes
at the old head positions. The work alphabet is arbitrary `Fin (g + 1)`.
-/

namespace CascadeObstruction.Compiler

open Transpose

set_option autoImplicit false

abbrev Rule (k g q : ℕ) :=
  Fin (q + 1) → Option Bool → (Fin k → Fin (g + 1)) →
    Fin (q + 1) × Dir × (Fin k → Fin (g + 1) × Dir) × Option Bool

abbrev Program (k g q T : ℕ) := Fin T → Rule k g q

abbrev Label (q T : ℕ) := Fin (T + 1) × Fin (q + 1)

abbrev nativeQ (q T : ℕ) := Fintype.card (Label q T) - 1

noncomputable def encoding (q T : ℕ) : Label q T ≃ Fin (nativeQ q T + 1) :=
  (TransposeFollowup.NativeMicrocode.initialEncoding (T := Fin 0)
    ((0 : Fin (T + 1)), (0 : Fin (q + 1)))).label

@[simp] theorem encoding_zero (q T : ℕ) : encoding q T (0, 0) = 0 :=
  TransposeFollowup.NativeMicrocode.initialEncoding_start _

variable {k g q T : ℕ}

noncomputable def delta (p : Program k g q T)
    (s : Fin (nativeQ q T + 1)) (input : Option Bool)
    (scanned : Fin k → Fin (g + 1)) :
    Option (Fin (nativeQ q T + 1) × Dir ×
      (Fin k → Fin (g + 1) × Dir) × Option Bool) :=
  let l := (encoding q T).symm s
  if h : l.1.val < T then
    let r := p ⟨l.1.val, h⟩ l.2 input scanned
    some (encoding q T (⟨l.1.val + 1, by omega⟩, r.1), r.2)
  else none

noncomputable def machine (p : Program k g q T) : TM where
  k := k
  g := g
  q := nativeQ q T
  δ := delta p

/-- Source configuration, without the public clock in its controller. -/
structure Config (k g q : ℕ) where
  control : Fin (q + 1)
  inputPos : ℤ
  work : Fin k → ℤ → Fin (g + 1)
  workPos : Fin k → ℤ
  outRev : List Bool

def initial : Config k g q := ⟨0, 0, fun _ _ => 0, fun _ => 0, []⟩

def advance (r : Rule k g q) (w : List Bool) (c : Config k g q) : Config k g q :=
  let a := r c.control (readInput w c.inputPos) (fun h => c.work h (c.workPos h))
  { control := a.1
    inputPos := a.2.1.shift c.inputPos
    work := fun h z => if z = c.workPos h then (a.2.2.1 h).1 else c.work h z
    workPos := fun h => (a.2.2.1 h).2.shift (c.workPos h)
    outRev := match a.2.2.2 with | none => c.outRev | some b => b :: c.outRev }

/-- The source run freezes after its prescribed duration. -/
def run (p : Program k g q T) (w : List Bool) : ℕ → Config k g q
  | 0 => initial
  | n + 1 => if h : n < T then advance (p ⟨n, h⟩) w (run p w n) else run p w n

noncomputable def Config.denote (p : Program k g q T) (n : ℕ)
    (c : Config k g q) : Transpose.Config (machine p) where
  state := encoding q T (⟨min n T, by omega⟩, c.control)
  inPos := c.inputPos
  work := c.work
  workPos := c.workPos
  outRev := c.outRev

theorem denote_initial (p : Program k g q T) :
    (initial : Config k g q).denote p 0 = Transpose.init (machine p) := by
  simp [Config.denote, initial, Transpose.init, machine]
  rfl

theorem step_denote_of_lt (p : Program k g q T) (w : List Bool)
    (n : ℕ) (c : Config k g q) (hn : n < T) :
    Transpose.step (machine p) w (c.denote p n) =
      some ((advance (p ⟨n, hn⟩) w c).denote p (n + 1)) := by
  simp [Transpose.step, Config.denote, machine, delta, advance,
    Nat.min_eq_left hn.le, hn]
  rfl

theorem step_denote_of_ge (p : Program k g q T) (w : List Bool)
    (n : ℕ) (c : Config k g q) (hn : T ≤ n) :
    Transpose.step (machine p) w (c.denote p n) = none := by
  simp [Transpose.step, Config.denote, machine, delta, Nat.min_eq_right hn]

theorem denote_succ_of_ge (p : Program k g q T)
    (n : ℕ) (c : Config k g q) (hn : T ≤ n) :
    c.denote p (n + 1) = c.denote p n := by
  simp [Config.denote, Nat.min_eq_right hn,
    Nat.min_eq_right (hn.trans (Nat.le_succ n))]

/-- Exact equality of complete configurations: all symbols, positions and
output bits agree; only the controller is encoded with its public time. -/
theorem run_denote (p : Program k g q T) (w : List Bool) (n : ℕ) :
    Transpose.Tape.run (machine p) w n = (run p w n).denote p n := by
  induction n with
  | zero => exact (denote_initial p).symm
  | succ n ih =>
    rw [Transpose.Tape.run, ih]
    by_cases hn : n < T
    · rw [step_denote_of_lt p w n _ hn]
      simp [run, hn]
    · rw [step_denote_of_ge p w n _ (Nat.le_of_not_gt hn)]
      simpa [run, hn] using
        (denote_succ_of_ge p n (run p w n) (Nat.le_of_not_gt hn)).symm

theorem haltsAt (p : Program k g q T) (w : List Bool) :
    Transpose.Tape.HaltsAt (machine p) w T := by
  constructor
  · intro n hn he
    have hs := (Transpose.Tape.Impl.step_run_eq_none_iff n).2 he
    rw [run_denote, step_denote_of_lt p w n _ hn] at hs
    contradiction
  · apply (Transpose.Tape.Impl.step_run_eq_none_iff T).1
    rw [run_denote, step_denote_of_ge p w T _ le_rfl]

theorem haltsAt_iff (p : Program k g q T) (w : List Bool) (n : ℕ) :
    Transpose.Tape.HaltsAt (machine p) w n ↔ n = T := by
  constructor
  · intro h
    exact Transpose.Tape.Impl.haltsAt_unique h (haltsAt p w)
  · rintro rfl
    exact haltsAt p w

/-- The exact active prefix also agrees in the frozen statement's partial
`stepN` semantics; post-halt freezing is not counted as an executed step. -/
theorem stepN_eq (p : Program k g q T) (w : List Bool) (n : ℕ) (hn : n ≤ T) :
    Transpose.stepN (machine p) w n (Transpose.init (machine p)) =
      some ((run p w n).denote p n) := by
  apply (Transpose.Tape.Impl.stepN_init_eq_some_iff n _).2
  exact ⟨fun u hu => (haltsAt p w).1 u (hu.trans_le hn), run_denote p w n⟩

theorem input_trajectory (p : Program k g q T) (w : List Bool) (n : ℕ) :
    Transpose.Tape.inTraj (machine p) w n = (run p w n).inputPos := by
  simp only [Transpose.Tape.inTraj, run_denote, Config.denote]

theorem work_trajectory (p : Program k g q T) (w : List Bool) (n : ℕ) (h : Fin k) :
    Transpose.Tape.workTraj (machine p) w n h = (run p w n).workPos h := by
  simp only [Transpose.Tape.workTraj, run_denote, Config.denote]

theorem work_contents (p : Program k g q T) (w : List Bool) (n : ℕ)
    (h : Fin k) (z : ℤ) :
    (Transpose.Tape.run (machine p) w n).work h z = (run p w n).work h z := by
  rw [run_denote]
  rfl

theorem output_word (p : Program k g q T) (w : List Bool) (n : ℕ) :
    (Transpose.Tape.run (machine p) w n).outRev = (run p w n).outRev := by
  rw [run_denote]
  rfl

theorem outBit_eq (p : Program k g q T) (w : List Bool) (n : ℕ) :
    Transpose.Tape.outBit (machine p) w n =
      if hn : n < T then
        (p ⟨n, hn⟩ (run p w n).control
          (readInput w (run p w n).inputPos)
          (fun h => (run p w n).work h ((run p w n).workPos h))).2.2.2
      else none := by
  unfold Transpose.Tape.outBit Transpose.Tape.transAt
    Transpose.Tape.inSym Transpose.Tape.headSym
  rw [run_denote]
  by_cases hn : n < T
  · simp [Config.denote, machine, delta, hn, Nat.min_eq_left hn.le]
  · simp [Config.denote, machine, delta, hn, Nat.min_eq_right (Nat.le_of_not_gt hn)]

theorem computesWithin (p : Program k g q T) (w : List Bool) :
    Transpose.ComputesWithin (machine p) w (run p w T).outRev.reverse T := by
  apply (Transpose.Tape.Impl.computesWithin_iff _ _).2
  exact ⟨T, le_rfl, haltsAt p w, congrArg List.reverse (output_word p w T)⟩

@[simp] theorem tape_count (p : Program k g q T) : (machine p).k = k := rfl

@[simp] theorem alphabet_size (p : Program k g q T) : (machine p).g + 1 = g + 1 := rfl

@[simp] theorem cell_bits (p : Program k g q T) :
    Transpose.Tape.cellBits (machine p) = max 1 (Nat.clog 2 (g + 1)) := rfl

theorem state_count (p : Program k g q T) :
    (machine p).q + 1 = (T + 1) * (q + 1) := by
  simp only [machine, nativeQ, Label, Fintype.card_prod, Fintype.card_fin]
  have hp : 0 < (T + 1) * (q + 1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem state_bits_le (p : Program k g q T) :
    Nat.clog 2 ((machine p).q + 1) ≤ Nat.clog 2 (T + 1) + Nat.clog 2 (q + 1) := by
  rw [state_count]
  apply Nat.clog_le_of_le_pow
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _)
    (Nat.le_pow_clog (by norm_num) _)

end CascadeObstruction.Compiler
