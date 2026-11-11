import AdaptiveTransfer.NativeWrites
import Transpose.Tape.Encode
import Mathlib.Data.Fintype.EquivFin

/-! A finite typed transition table is compiled directly to the frozen native
machine. The correspondence is proved from its simultaneous old-position rule.
This interface is used by the exact scan loader, not by a time-expanded microcode.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose

variable {Q Γ : Type*} {k : ℕ}

abbrev Instruction (Q Γ : Type*) (k : ℕ) :=
  Q × Dir × (Fin k → Γ × Dir) × Option Bool
abbrev Table (Q Γ : Type*) (k : ℕ) :=
  Q → Option Bool → (Fin k → Γ) → Option (Instruction Q Γ k)

structure Config (Q Γ : Type*) (k : ℕ) where
  state : Q
  inPos : ℤ
  work : Fin k → ℤ → Γ
  workPos : Fin k → ℤ
  outRev : List Bool

@[ext] theorem Config.ext {c e : Config Q Γ k} (hs : c.state = e.state)
    (hi : c.inPos = e.inPos) (hw : c.work = e.work) (hp : c.workPos = e.workPos)
    (ho : c.outRev = e.outRev) : c = e := by cases c; cases e; simp_all

def initial (q₀ : Q) (blank : Γ) : Config Q Γ k := ⟨q₀, 0, fun _ _ => blank, fun _ => 0, []⟩

def next (δ : Table Q Γ k) (w : List Bool) (c : Config Q Γ k) : Option (Config Q Γ k) :=
  match δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => none
  | some (q, move, acts, out) => some {
      state := q
      inPos := move.shift c.inPos
      work := fun i z => if z = c.workPos i then (acts i).1 else c.work i z
      workPos := fun i => (acts i).2.shift (c.workPos i)
      outRev := match out with | none => c.outRev | some b => b :: c.outRev }

def run (δ : Table Q Γ k) (w : List Bool) : ℕ → Config Q Γ k → Option (Config Q Γ k)
  | 0, c => some c
  | n + 1, c => (next δ w c).bind (run δ w n)

theorem run_add (δ : Table Q Γ k) (w : List Bool) (m n : ℕ) (c : Config Q Γ k) :
    run δ w (m + n) c = (run δ w m c).bind (run δ w n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add, run, run, Option.bind_assoc]
    congr 1
    funext e
    exact ih e

theorem run_trans (δ : Table Q Γ k) (w : List Bool) {m n : ℕ} {a b c : Config Q Γ k}
    (h₁ : run δ w m a = some b) (h₂ : run δ w n b = some c) :
    run δ w (m + n) a = some c := by rw [run_add, h₁]; exact h₂

section Encoding
variable [Fintype Q] [Fintype Γ]

/-- A fixed finite enumeration with a distinguished element sent to native zero. -/
noncomputable def pointCode {α : Type*} [Fintype α] (a₀ : α) :
    α ≃ Fin (Fintype.card α - 1 + 1) := by
  letI : Nonempty α := ⟨a₀⟩
  let e : α ≃ Fin (Fintype.card α - 1 + 1) :=
    Fintype.equivFinOfCardEq (Nat.sub_add_cancel (Fintype.card_pos (α := α))).symm
  exact e.trans (Equiv.swap (e a₀) 0)

@[simp] theorem pointCode_initial {α : Type*} [Fintype α] (a₀ : α) : pointCode a₀ a₀ = 0 := by
  classical
  simp [pointCode]

noncomputable def machine (q₀ : Q) (blank : Γ) (δ : Table Q Γ k) : TM where
  k := k
  q := Fintype.card Q - 1
  g := Fintype.card Γ - 1
  δ q raw scanned := (δ ((pointCode q₀).symm q) raw
    (fun i => (pointCode blank).symm (scanned i))).map
      (fun (s, move, acts, out) => (pointCode q₀ s, move,
        fun i => (pointCode blank (acts i).1, (acts i).2), out))

noncomputable def denote (q₀ : Q) (blank : Γ) (δ : Table Q Γ k) (c : Config Q Γ k) :
    Transpose.Config (machine q₀ blank δ) where
  state := pointCode q₀ c.state
  inPos := c.inPos
  work := fun i z => pointCode blank (c.work i z)
  workPos := c.workPos
  outRev := c.outRev

@[simp] theorem denote_initial (q₀ : Q) (blank : Γ) (δ : Table Q Γ k) :
    denote q₀ blank δ (initial q₀ blank) = init (machine q₀ blank δ) := by
  simp [denote, initial, init]
  rfl

/-- Literal one-step correspondence with the frozen native machine. -/
theorem step_denote (q₀ : Q) (blank : Γ) (δ : Table Q Γ k) (w : List Bool)
    (c : Config Q Γ k) :
    step (machine q₀ blank δ) w (denote q₀ blank δ c) =
      (next δ w c).map (denote q₀ blank δ) := by
  classical
  simp only [step, machine, denote, Equiv.symm_apply_apply, next]
  cases h : δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => rfl
  | some instruction =>
    rcases instruction with ⟨q, move, acts, out⟩
    simp only [Option.map_some]
    congr 2
    funext i z
    change (if z = c.workPos i then pointCode blank (acts i).1 else pointCode blank (c.work i z)) =
      pointCode blank (if z = c.workPos i then (acts i).1 else c.work i z)
    by_cases hz : z = c.workPos i <;> simp only [hz, ite_true, ite_false]

/-- Exact iteration: no overhead and no assumed simulator relation. -/
theorem stepN_denote (q₀ : Q) (blank : Γ) (δ : Table Q Γ k) (w : List Bool)
    (n : ℕ) (c : Config Q Γ k) :
    stepN (machine q₀ blank δ) w n (denote q₀ blank δ c) =
      (run δ w n c).map (denote q₀ blank δ) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [stepN, step_denote, run]
    cases h : next δ w c with
    | none => rfl
    | some e => exact ih e

theorem machine_resources (q₀ : Q) (blank : Γ) (δ : Table Q Γ k) :
    (machine q₀ blank δ).k = k ∧
    (machine q₀ blank δ).q + 1 = Fintype.card Q ∧
    (machine q₀ blank δ).g + 1 = Fintype.card Γ := by
  let : Nonempty Q := ⟨q₀⟩
  let : Nonempty Γ := ⟨blank⟩
  exact ⟨rfl, Nat.sub_add_cancel (Fintype.card_pos (α := Q)),
    Nat.sub_add_cancel (Fintype.card_pos (α := Γ))⟩

end Encoding
end AdaptiveTransfer.ScanLoader
