import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Actual synchronous finite-state scans. The nested address order is the
ordinary forward or backward order on a bank split into equal aligned bins.
Every output reads the old tuple at that address; state is the only carried channel. -/
namespace BitWord
open Classical
set_option autoImplicit false

abbrev Grid (n B : ℕ) := Fin n × Fin B
abbrev Banks (n B q : ℕ) := Grid n B → Fin q → Bool

def scanOrder (reverse : Bool) {n : ℕ} (i : Fin n) : Fin n :=
  if reverse then i.rev else i

@[simp] theorem scanOrder_involutive (reverse : Bool) {n : ℕ} (i : Fin n) :
    scanOrder reverse (scanOrder reverse i) = i := by
  cases reverse <;> simp [scanOrder]

/-- A public, possibly address-dependent nonlinear scan rule. -/
structure Scan (n B q : ℕ) (State : Type*) where
  reverse : Bool
  step : Grid n B → State → (Fin q → Bool) → State × (Fin q → Bool)

namespace Scan
variable {n B q : ℕ} {State : Type*}

/-- State after t visits within one bin. -/
def localState (C : Scan n B q State) (x : Banks n B q) (j : Fin n) (initial : State) : ℕ → State
  | 0 => initial
  | t+1 => if ht : t < B then
      (C.step (j,scanOrder C.reverse ⟨t,ht⟩) (C.localState x j initial t)
        (x (j,scanOrder C.reverse ⟨t,ht⟩))).1
    else C.localState x j initial t

/-- Actual carried state after processing t bins. -/
def boundaryState (C : Scan n B q State) (x : Banks n B q) (initial : State) : ℕ → State
  | 0 => initial
  | t+1 => if ht : t < n then
      C.localState x (scanOrder C.reverse ⟨t,ht⟩) (C.boundaryState x initial t) B
    else C.boundaryState x initial t

/-- The n actual entering states, one per bin. The terminal state is not needed
for local replay and is not charged as an extra helper field. -/
def boundaryRecord (C : Scan n B q State) (x : Banks n B q) (initial : State) :
    Fin n → State := fun j => C.boundaryState x initial j.val

def output (C : Scan n B q State) (x : Banks n B q) (initial : State) : Banks n B q :=
  fun p => (C.step p (C.localState x p.1
    (C.boundaryState x initial (scanOrder C.reverse p.1).val)
    (scanOrder C.reverse p.2).val) (x p)).2

def terminal (C : Scan n B q State) (x : Banks n B q) (initial : State) : State :=
  C.boundaryState x initial n

/-- Local replay is proved from the step recurrence; it is not a locality hypothesis. -/
theorem localState_congr (C : Scan n B q State) (x y : Banks n B q) (j : Fin n)
    (a b : State) (hab : a=b) (hxy : ∀ i, x (j,i)=y (j,i)) (t : ℕ) :
    C.localState x j a t = C.localState y j b t := by
  subst b
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [localState]
    split_ifs with ht
    · rw [ih,hxy]
    · exact ih

/-- The old tuples on a bin and its actual entering state determine every
new output tuple in that bin, in either direction. -/
theorem output_congr_on_bin (C : Scan n B q State) (x y : Banks n B q)
    (a b : State) (j : Fin n)
    (hentry : C.boundaryState x a (scanOrder C.reverse j).val =
      C.boundaryState y b (scanOrder C.reverse j).val)
    (hxy : ∀ i, x (j,i)=y (j,i)) :
    ∀ i, C.output x a (j,i)=C.output y b (j,i) := by
  intro i
  unfold output
  rw [C.localState_congr x y j _ _ hentry hxy, hxy]

/-- Equal actual records supply the entering state even when it is inherited. -/
theorem output_congr_of_record (C : Scan n B q State) (x y : Banks n B q)
    (a b : State) (j : Fin n)
    (hrecord : C.boundaryRecord x a = C.boundaryRecord y b)
    (hxy : ∀ i, x (j,i)=y (j,i)) :
    ∀ i, C.output x a (j,i)=C.output y b (j,i) := by
  apply C.output_congr_on_bin x y a b j
  · exact congrFun hrecord (scanOrder C.reverse j)
  · exact hxy

/-- Omitting a scan is represented by the identity scan. -/
def identity : Scan n B q State := ⟨false,fun _ s x => (s,x)⟩

@[simp] theorem identity_output (x : Banks n B q) (initial : State) :
    (identity : Scan n B q State).output x initial = x := rfl

@[simp] theorem identity_localState (x : Banks n B q) (j : Fin n) (initial : State) (t : ℕ) :
    (identity : Scan n B q State).localState x j initial t = initial := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [localState]
    split_ifs <;> exact ih

@[simp] theorem identity_boundaryState (x : Banks n B q) (initial : State) (t : ℕ) :
    (identity : Scan n B q State).boundaryState x initial t = initial := by
  induction t with
  | zero => rfl
  | succ t ih => simp [boundaryState,ih]

/-- Flattening a backward traversal reverses the ordinary raw address. -/
theorem reverse_flatten (j : Fin n) (i : Fin B) :
    finProdFinEquiv (j.rev,i.rev) = (finProdFinEquiv (j,i)).rev := by
  apply Fin.ext
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Fin.rev,Fin.val_mk]
  have hj := Nat.sub_add_cancel (Nat.succ_le_of_lt j.isLt)
  have hi := Nat.sub_add_cancel (Nat.succ_le_of_lt i.isLt)
  have he : (B-(i.val+1)+B*(n-(j.val+1)))+(i.val+B*j.val+1)=n*B := by
    nlinarith
  omega

end Scan
end BitWord
