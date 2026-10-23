import BitWord.ScanTrace

/-! A scale-independent raw scan and its exact regrouping into aligned bins. -/
namespace BitWord
open Classical
set_option autoImplicit false

structure RawScan (P q : ℕ) (State : Type*) where
  reverse : Bool
  step : Fin P → State → (Fin q → Bool) → State × (Fin q → Bool)

namespace RawScan
variable {P n B q : ℕ} {State : Type*}

def state (C : RawScan P q State) (x : Fin P → Fin q → Bool) (initial : State) : ℕ → State
  | 0 => initial
  | t+1 => if ht : t<P then
      (C.step (scanOrder C.reverse ⟨t,ht⟩) (C.state x initial t)
        (x (scanOrder C.reverse ⟨t,ht⟩))).1
    else C.state x initial t

def output (C : RawScan P q State) (x : Fin P → Fin q → Bool) (initial : State) :
    Fin P → Fin q → Bool :=
  fun p => (C.step p (C.state x initial (scanOrder C.reverse p).val) (x p)).2

def onGrid (C : RawScan (n*B) q State) : Scan n B q State :=
  ⟨C.reverse,fun p s x => C.step (finProdFinEquiv p) s x⟩

theorem order_flatten (reverse : Bool) (j : Fin n) (i : Fin B) :
    finProdFinEquiv (scanOrder reverse j,scanOrder reverse i) =
      scanOrder reverse (finProdFinEquiv (j,i)) := by
  cases reverse
  · rfl
  · exact Scan.reverse_flatten j i

/-- The scan state reached after a partial bin equals the corresponding raw state. -/
theorem localState_eq_raw (C : RawScan (n*B) q State) (x : Fin (n*B) → Fin q → Bool)
    (initial : State) (j : Fin n) (t : ℕ) (ht : t ≤ B) :
    C.onGrid.localState (fun p => x (finProdFinEquiv p)) (scanOrder C.reverse j)
      (C.state x initial (j.val*B)) t = C.state x initial (j.val*B+t) := by
  induction t with
  | zero => simp [Scan.localState]
  | succ t ih =>
    have ht' : t < B := by omega
    have hi : j.val*B+t < n*B := by
      have hj := j.isLt
      nlinarith
    rw [Scan.localState, dite_eq_left ht', ih (by omega)]
    rw [show j.val*B+(t+1)=j.val*B+t+1 by omega,state,dite_eq_left hi]
    have hp : (⟨j.val*B+t,hi⟩ : Fin (n*B)) = finProdFinEquiv (j,⟨t,ht'⟩) := by
      apply Fin.ext
      change j.val*B+t = t+B*j.val
      ring
    simp only [onGrid]
    rw [hp,← order_flatten]

/-- Every recorded bin boundary is the actual raw scan state at that address. -/
theorem boundaryState_eq_raw (C : RawScan (n*B) q State)
    (x : Fin (n*B) → Fin q → Bool) (initial : State) (t : ℕ) (ht : t ≤ n) :
    C.onGrid.boundaryState (fun p => x (finProdFinEquiv p)) initial t =
      C.state x initial (t*B) := by
  induction t with
  | zero => simp [Scan.boundaryState,state]
  | succ t ih =>
    have ht' : t<n := by omega
    rw [Scan.boundaryState,dite_eq_left ht',ih (by omega)]
    simpa only [onGrid,Fin.val_mk,Nat.add_mul,Nat.one_mul] using
      C.localState_eq_raw x initial ⟨t,ht'⟩ B le_rfl

/-- Regrouping changes neither an output bit nor the inherited terminal state. -/
theorem output_onGrid (C : RawScan (n*B) q State)
    (x : Fin (n*B) → Fin q → Bool) (initial : State) (p : Grid n B) :
    C.onGrid.output (fun v => x (finProdFinEquiv v)) initial p =
      C.output x initial (finProdFinEquiv p) := by
  let j := scanOrder C.reverse p.1
  let i := scanOrder C.reverse p.2
  have hb := C.boundaryState_eq_raw x initial j.val j.isLt.le
  have hl := C.localState_eq_raw x initial j i.val i.isLt.le
  have ho := order_flatten C.reverse p.1 p.2
  have hv := congrArg Fin.val ho
  change (scanOrder C.reverse p.2).val+B*(scanOrder C.reverse p.1).val =
    (scanOrder C.reverse (finProdFinEquiv p)).val at hv
  unfold Scan.output
  change (C.step (finProdFinEquiv p)
    (C.onGrid.localState _ p.1 (C.onGrid.boundaryState _ initial j.val) i.val)
    (x (finProdFinEquiv p))).2 = _
  rw [hb]
  have hj : scanOrder C.reverse j = p.1 := scanOrder_involutive C.reverse p.1
  rw [hj] at hl
  rw [hl]
  unfold output
  congr 3
  dsimp [j,i]
  nlinarith [hv]

theorem terminal_onGrid (C : RawScan (n*B) q State)
    (x : Fin (n*B) → Fin q → Bool) (initial : State) :
    C.onGrid.terminal (fun v => x (finProdFinEquiv v)) initial = C.state x initial (n*B) :=
  C.boundaryState_eq_raw x initial n le_rfl

end RawScan
end BitWord
