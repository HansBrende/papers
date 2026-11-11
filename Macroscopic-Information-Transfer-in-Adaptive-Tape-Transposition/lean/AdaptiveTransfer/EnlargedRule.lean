import AdaptiveTransfer.PrefixOutput
import AdaptiveTransfer.ReplayCounting

/-! The whole enlarged analysis rule. Its only raw observations are declared
windows at continuous ports, and output access is exactly the strict prefix.
All other evolving storage is in the finite state; no reconstruction premise is
part of the model. Native old-position writes and at most one append are literal.
-/

namespace AdaptiveTransfer.Enlarged

open Transpose

variable {Q Γ Λ : Type*} {k p R : ℕ}

structure Context (Q Γ Λ : Type*) (k p R : ℕ) where
  state : Q
  label : Λ
  time : ℕ
  workPos : Fin k → ℤ
  ports : Fin p → ℤ
  ordinal : ℕ
  old : Fin k → Γ
  raw : Fin p → Fin (2 * R + 1) → Option Bool
  prior : List Bool

structure Instruction (Q Γ : Type*) (k p : ℕ) where
  state : Q
  work : Fin k → Γ × Dir
  ports : Fin p → Dir
  append : Option Bool

structure Config (Q Γ : Type*) (k p : ℕ) where
  state : Q
  work : Fin k → ℤ → Γ
  workPos : Fin k → ℤ
  ports : Fin p → ℤ
  outRev : List Bool

/-- All rules are fixed before selecting the input, label or replay region.
The rule is total; `none` is the halting instruction. -/
structure System (Q Γ Λ : Type*) (k p R : ℕ) where
  initialState : Q
  blank : Γ
  origins : Fin p → ℤ
  rule : Context Q Γ Λ k p R → Option (Instruction Q Γ k p)

namespace System

variable (M : System Q Γ Λ k p R)

def initial : Config Q Γ k p :=
  ⟨M.initialState, fun _ _ => M.blank, fun _ => 0, M.origins, []⟩

def context (_M : System Q Γ Λ k p R) (label : Λ) (w : List Bool) (t : ℕ) (c : Config Q Γ k p) :
    Context Q Γ Λ k p R :=
  ⟨c.state, label, t, c.workPos, c.ports, c.outRev.length,
    (fun h => c.work h (c.workPos h)),
    (fun j i => readInput w (windowAddress (c.ports j) R i)), c.outRev.reverse⟩

def applyInstruction (c : Config Q Γ k p) (v : Instruction Q Γ k p) : Config Q Γ k p :=
  ⟨v.state, (fun h z => if z = c.workPos h then (v.work h).1 else c.work h z),
    (fun h => (v.work h).2.shift (c.workPos h)),
    (fun j => (v.ports j).shift (c.ports j)),
    (match v.append with | none => c.outRev | some b => b :: c.outRev)⟩

def step (label : Λ) (w : List Bool) (t : ℕ) (c : Config Q Γ k p) :
    Option (Config Q Γ k p) := (M.rule (M.context label w t c)).map (applyInstruction c)

/-- The Boolean records whether execution has already halted; it is an
administrative run status, not a register available to the transition rule.
Once halted, even a time-dependent rule is never called again. -/
def execution (M : System Q Γ Λ k p R) (label : Λ) (w : List Bool) :
    ℕ → Config Q Γ k p × Bool
  | 0 => (M.initial, true)
  | t + 1 =>
      let prev := execution M label w t
      if prev.2 then
        match M.step label w t prev.1 with
        | none => (prev.1, false)
        | some c => (c, true)
      else prev

def run (label : Λ) (w : List Bool) (t : ℕ) : Config Q Γ k p :=
  (M.execution label w t).1

def live (label : Λ) (w : List Bool) (t : ℕ) : Bool := (M.execution label w t).2

def instruction (label : Λ) (w : List Bool) (t : ℕ) : Option (Instruction Q Γ k p) :=
  if M.live label w t then M.rule (M.context label w t (M.run label w t)) else none

def emitted (label : Λ) (w : List Bool) (t : ℕ) : Option Bool :=
  (M.instruction label w t).bind Instruction.append

def written (label : Λ) (w : List Bool) (h : Fin k) (t : ℕ) : Γ :=
  (M.run label w (t + 1)).work h ((M.run label w t).workPos h)

@[simp] theorem run_zero (label : Λ) (w : List Bool) : M.run label w 0 = M.initial := rfl

theorem run_succ (label : Λ) (w : List Bool) (t : ℕ) :
    M.run label w (t + 1) =
      match M.instruction label w t with
      | none => M.run label w t
      | some v => applyInstruction (M.run label w t) v := by
  simp only [run, execution, instruction, live, step]
  by_cases h : (M.execution label w t).2 = true
  · simp only [h, ite_true]
    cases M.rule (M.context label w t (M.execution label w t).1) <;> rfl
  · simp [h]

/-- Frozen halt ticks cause no output access to future bits and no extra append. -/
theorem output_succ (label : Λ) (w : List Bool) (t : ℕ) :
    (M.run label w (t + 1)).outRev =
      match M.emitted label w t with
      | none => (M.run label w t).outRev
      | some b => b :: (M.run label w t).outRev := by
  rw [run_succ]
  unfold emitted
  cases M.instruction label w t with
  | none => rfl
  | some v => rfl

theorem output_eq_word (label : Λ) (w : List Bool) (t : ℕ) :
    (M.run label w t).outRev.reverse = PrefixOutput.word (M.emitted label w) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [output_succ, PrefixOutput.word_succ]
    cases M.emitted label w t <;> simp [ih]

theorem count_eq_word (label : Λ) (w : List Bool) (t : ℕ) :
    (M.run label w t).outRev.length = (PrefixOutput.word (M.emitted label w) t).length := by
  rw [← List.length_reverse, output_eq_word]

/-- The exact old-position update, valid also after halt. -/
theorem work_update (label : Λ) (w : List Bool) (t : ℕ) (h : Fin k) (z : ℤ) :
    (M.run label w (t + 1)).work h z =
      if z = (M.run label w t).workPos h then M.written label w h t
      else (M.run label w t).work h z := by
  unfold written
  rw [run_succ]
  cases M.instruction label w t with
  | none =>
    by_cases hz : z = (M.run label w t).workPos h
    · subst z; simp
    · simp [hz]
  | some v => simp [applyInstruction]

theorem work_eq_memoryAfter (label : Λ) (w : List Bool) (h : Fin k) (t : ℕ) (z : ℤ) :
    (M.run label w t).work h z = memoryAfter (fun _ => M.blank)
      (fun u => (M.run label w u).workPos h) (M.written label w h) (fun _ => true) t z := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [work_update]
    simp only [memoryAfter, Bool.true_and, decide_eq_true_eq]
    split_ifs <;> simp_all

theorem work_constant (label : Λ) (w : List Bool) (h : Fin k)
    {a b : ℕ} (hab : a ≤ b) (z : ℤ)
    (hmiss : ∀ u, a ≤ u → u < b → z ≠ (M.run label w u).workPos h) :
    (M.run label w b).work h z = (M.run label w a).work h z := by
  rw [M.work_eq_memoryAfter, M.work_eq_memoryAfter]
  exact memoryAfter_no_write _ _ _ _ hab (fun u hau hub _ => hmiss u hau hub)

theorem work_virgin (label : Λ) (w : List Bool) (h : Fin k) (t : ℕ) (z : ℤ)
    (hmiss : ∀ u < t, z ≠ (M.run label w u).workPos h) :
    (M.run label w t).work h z = M.blank := by
  rw [M.work_constant label w h (Nat.zero_le _) z (fun u _ hu => hmiss u hu)]
  rfl

private theorem dir_abs_shift_sub (d : Dir) (z : ℤ) : |d.shift z - z| ≤ 1 := by
  cases d <;> simp [Dir.shift]

theorem work_unit (label : Λ) (w : List Bool) (h : Fin k) (t : ℕ) :
    |(M.run label w (t + 1)).workPos h - (M.run label w t).workPos h| ≤ 1 := by
  rw [run_succ]
  cases M.instruction label w t with
  | none => simp
  | some v => exact dir_abs_shift_sub _ _

theorem port_unit (label : Λ) (w : List Bool) (j : Fin p) (t : ℕ) :
    |(M.run label w (t + 1)).ports j - (M.run label w t).ports j| ≤ 1 := by
  rw [run_succ]
  cases M.instruction label w t with
  | none => simp
  | some v => exact dir_abs_shift_sub _ _

end System
end AdaptiveTransfer.Enlarged
