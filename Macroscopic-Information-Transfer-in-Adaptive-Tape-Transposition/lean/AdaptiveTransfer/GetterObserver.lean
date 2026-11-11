import AdaptiveTransfer.PrefixOutput
import AdaptiveTransfer.ReplayCounting

/-! Native sources with paid finite observers and continuous virtual raw ports.
Observer updates receive exactly the declared old native context/windows and
resulting instruction. They do not receive prior output or the getter label.
-/

namespace AdaptiveTransfer.Getter

open Transpose Transpose.Tape Transpose.Tape.Impl

abbrev NativeInstruction (M : TM) :=
  Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) × Option Bool

structure ObserverContext (M : TM) (U : Type*) (v R : ℕ) where
  sourceState : Fin (M.q + 1)
  observerState : U
  time : ℕ
  workPos : Fin M.k → ℤ
  ports : Fin (v + 1) → ℤ
  ordinal : ℕ
  old : Fin M.k → Fin (M.g + 1)
  raw : Fin (v + 1) → Fin (2 * R + 1) → Option Bool

structure Observer (M : TM) (U : Type*) (v R : ℕ) where
  initial : U
  origins : Fin v → ℤ
  update : ObserverContext M U v R → NativeInstruction M → U × (Fin v → Dir)

variable {M : TM} {U Λ : Type*} {v R : ℕ}

namespace Observer
variable (A : Observer M U v R)

/-- Port zero is literally the native input head; the other ports are virtual. -/
def ports (c : Transpose.Config M) (virtual : Fin v → ℤ) : Fin (v + 1) → ℤ :=
  Fin.cases c.inPos virtual

def context (w : List Bool) (t : ℕ) (aux : U × (Fin v → ℤ)) : ObserverContext M U v R :=
  let c := Transpose.Tape.run M w t
  let ps := ports c aux.2
  ⟨c.state, aux.1, t, c.workPos, ps, c.outRev.length,
    (fun h => c.work h (c.workPos h)),
    (fun j i => readInput w (windowAddress (ps j) R i))⟩

/-- A real deterministic observer attached to the actual native execution.
Native halting freezes both its state and its virtual ports. -/
def run (A : Observer M U v R) (w : List Bool) : ℕ → U × (Fin v → ℤ)
  | 0 => (A.initial, A.origins)
  | t + 1 => match transAt M w t with
      | none => run A w t
      | some instruction =>
          let prev := run A w t
          let next := A.update (context w t prev) instruction
          (next.1, fun j => (next.2 j).shift (prev.2 j))

def allPorts (w : List Bool) (t : ℕ) : Fin (v + 1) → ℤ :=
  ports (Transpose.Tape.run M w t) (A.run w t).2

def rawWindows (w : List Bool) (t : ℕ) : Fin (v + 1) → Fin (2 * R + 1) → Option Bool :=
  fun j i => readInput w (windowAddress (A.allPorts w t j) R i)

@[simp] theorem allPorts_zero (w : List Bool) (t : ℕ) :
    A.allPorts w t 0 = (Transpose.Tape.run M w t).inPos := rfl

@[simp] theorem allPorts_succ (w : List Bool) (t : ℕ) (j : Fin v) :
    A.allPorts w t j.succ = (A.run w t).2 j := rfl

theorem virtual_unit (w : List Bool) (t : ℕ) (j : Fin v) :
    |(A.run w (t + 1)).2 j - (A.run w t).2 j| ≤ 1 := by
  rw [run]
  cases h : transAt M w t with
  | none => simp
  | some instruction =>
    dsimp
    cases (A.update (context w t (A.run w t)) instruction).2 j <;> simp [Dir.shift]

/-- The observer's actual update is determined by the declared old fields.
There is no output-prefix equality premise and no observer-history oracle. -/
theorem update_agreement (w x : List Bool) (t : ℕ)
    (hstate : (Transpose.Tape.run M w t).state = (Transpose.Tape.run M x t).state)
    (haux : (A.run w t).1 = (A.run x t).1)
    (hwork : (Transpose.Tape.run M w t).workPos = (Transpose.Tape.run M x t).workPos)
    (hports : A.allPorts w t = A.allPorts x t)
    (hcount : (Transpose.Tape.run M w t).outRev.length = (Transpose.Tape.run M x t).outRev.length)
    (hold : ∀ h, (Transpose.Tape.run M w t).work h ((Transpose.Tape.run M w t).workPos h) =
      (Transpose.Tape.run M x t).work h ((Transpose.Tape.run M x t).workPos h))
    (hraw : A.rawWindows w t = A.rawWindows x t)
    (hinstr : transAt M w t = transAt M x t) : A.run w (t + 1) = A.run x (t + 1) := by
  have hctx : context (M := M) (R := R) w t (A.run w t) = context x t (A.run x t) := by
    unfold context
    change ObserverContext.mk _ _ _ _ (A.allPorts w t) _ _ (A.rawWindows w t) =
      ObserverContext.mk _ _ _ _ (A.allPorts x t) _ _ (A.rawWindows x t)
    rw [funext hold, hstate, haux, hwork, hports, hcount, hraw]
  have hv : (A.run w t).2 = (A.run x t).2 := by
    funext j
    exact congrFun hports j.succ
  rw [run, run, hinstr]
  cases transAt M x t with
  | none => exact Prod.ext haux hv
  | some instruction =>
    dsimp
    rw [hctx, hv]

end Observer

/-- Public getters do not receive unknown sibling old work symbols. Their
entire output argument is the strict prior string, not its future extension. -/
structure GetterContext (M : TM) (U Λ : Type*) (v R : ℕ) where
  label : Λ
  sourceState : Fin (M.q + 1)
  observerState : U
  time : ℕ
  workPos : Fin M.k → ℤ
  ports : Fin (v + 1) → ℤ
  ordinal : ℕ
  carrier : Fin (M.g + 1)
  raw : Fin (v + 1) → Fin (2 * R + 1) → Option Bool
  prior : List Bool

abbrev Getters (M : TM) (U Λ : Type*) (v R : ℕ) :=
  Fin M.k → GetterContext M U Λ v R → Fin (M.g + 1)

def getterContext (A : Observer M U v R) (f : Fin M.k) (label : Λ) (w : List Bool) (t : ℕ) :
    GetterContext M U Λ v R :=
  let c := Transpose.Tape.run M w t
  ⟨label, c.state, (A.run w t).1, t, c.workPos, A.allPorts w t, c.outRev.length,
    c.work f (c.workPos f), A.rawWindows w t, c.outRev.reverse⟩

def prediction (A : Observer M U v R) (G : Getters M U Λ v R)
    (f : Fin M.k) (label : Λ) (w : List Bool) (t : ℕ) (h : Fin M.k) : Fin (M.g + 1) :=
  G h (getterContext A f label w t)

/-- Only a wrong prediction on a genuine ordinary import carries a tag/value. -/
noncomputable def errorRecord {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)
    (A : Observer M U v R) (G : Getters M U Λ v R) (f : Fin M.k)
    (label : Λ) (H a t : ℕ) (h : Fin M.k) : Option (Fin (M.g + 1)) :=
  (E.incomingRecord H a t h).bind (fun value =>
    if value = prediction A G f label w t h then none else some value)

/-- Equal presence, prediction, and actual correction payload recover the
ordinary import value. Tagged blank and absence remain distinct. -/
theorem correction_recovers {Γ : Type*} [DecidableEq Γ] (e f : Option Γ) (prediction : Γ)
    (hp : e.isSome = f.isSome)
    (hc : e.bind (fun value => if value = prediction then none else some value) =
      f.bind (fun value => if value = prediction then none else some value)) : e = f := by
  cases e with
  | none => cases f <;> simp_all
  | some e =>
    cases f with
    | none => simp at hp
    | some f =>
      simp only [Option.bind_some] at hc
      by_cases he : e = prediction <;> by_cases hf : f = prediction <;>
        simp_all

end AdaptiveTransfer.Getter
