import BitWord.ScanRaw
import BitWord.ScanAncestry
import BitWord.GeometryStageScales

/-! One public raw program, before any analytical bin scale is chosen. Its scan
is the ordinary single chronological pass; regrouping is proved, not assumed. -/
namespace BitWord
open Classical
set_option autoImplicit false

abbrev RawBanks (P q : ℕ) := Fin P → Fin q → Bool

structure RawScanLayer (P q : ℕ) (State : Type*) where
  stage : Fin q → Geometry.Stage P
  scan : RawScan P q State

namespace RawScanLayer
variable {P n B q : ℕ} {State : Type*}
def permuted (C : RawScanLayer P q State) (x : RawBanks P q) : RawBanks P q :=
  fun p a => x ((C.stage a).endpoint.symm p) a

def apply (C : RawScanLayer P q State) (x : RawBanks P q × State) : RawBanks P q × State :=
  (C.scan.output (C.permuted x.1) x.2,C.scan.state (C.permuted x.1) x.2 P)

def onGrid (C : RawScanLayer (n*B) q State) : ScanLayer n B q State where
  perm a := finProdFinEquiv.trans ((C.stage a).endpoint.trans finProdFinEquiv.symm)
  scan := C.scan.onGrid

@[simp] theorem permuted_onGrid (C : RawScanLayer (n*B) q State) (x : RawBanks (n*B) q) :
    C.onGrid.permuted (fun p => x (finProdFinEquiv p)) =
      fun p => C.permuted x (finProdFinEquiv p) := by
  funext p a
  change x (finProdFinEquiv (finProdFinEquiv.symm ((C.stage a).endpoint.symm
    (finProdFinEquiv p)))) a = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem apply_onGrid (C : RawScanLayer (n*B) q State) (x : RawBanks (n*B) q × State) :
    C.onGrid.apply (fun p => x.1 (finProdFinEquiv p),x.2) =
      (fun p => (C.apply x).1 (finProdFinEquiv p),(C.apply x).2) := by
  apply Prod.ext
  · funext p
    change C.scan.onGrid.output (C.onGrid.permuted _) x.2 p = _
    rw [permuted_onGrid]
    exact C.scan.output_onGrid (C.permuted x.1) x.2 p
  · change C.scan.onGrid.terminal (C.onGrid.permuted _) x.2 = _
    rw [permuted_onGrid]
    exact C.scan.terminal_onGrid (C.permuted x.1) x.2
end RawScanLayer

structure RawScanProgram (P q L : ℕ) (State : Type*) where
  copyInput : Fin q → Bool
  constants : RawBanks P q
  initialState : State
  layer : Fin L → RawScanLayer P q State

namespace RawScanProgram
variable {P n B q L : ℕ} {State : Type*}
def initial (C : RawScanProgram P q L State) (x : Fin P → Bool) : RawBanks P q × State :=
  (fun p a => if C.copyInput a then x p else C.constants p a,C.initialState)

def run (C : RawScanProgram P q L State) (x : Fin P → Bool) : ℕ → RawBanks P q × State
  | 0 => C.initial x
  | t+1 => if ht : t<L then (C.layer ⟨t,ht⟩).apply (C.run x t) else C.run x t

def onGrid (C : RawScanProgram (n*B) q L State) : ScanProgram n B q L State where
  copyInput := C.copyInput
  constants p := C.constants (finProdFinEquiv p)
  initialState := C.initialState
  layer t := (C.layer t).onGrid

/-- The same physical execution is represented at every aligned bin scale. -/
theorem run_onGrid (C : RawScanProgram (n*B) q L State) (x : Fin (n*B) → Bool) (t : ℕ) :
    C.onGrid.run (fun p => x (finProdFinEquiv p)) t =
      (fun p => (C.run x t).1 (finProdFinEquiv p),(C.run x t).2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [ScanProgram.run,run]
    split <;> rename_i ht
    · rw [ih]
      exact (C.layer ⟨t,ht⟩).apply_onGrid (C.run x t)
    · exact ih

/-- Changing only the proof of a known tape length does not change execution. -/
def castLength {P' : ℕ} (C : RawScanProgram P q L State) (h : P=P') :
    RawScanProgram P' q L State := h ▸ C

theorem run_castLength {P' : ℕ} (C : RawScanProgram P q L State) (h : P=P')
    (x : Fin P' → Bool) (t : ℕ) :
    (C.castLength h).run x t =
      (fun p => (C.run (fun z => x (Fin.cast h z)) t).1 (Fin.cast h.symm p),
       (C.run (fun z => x (Fin.cast h z)) t).2) := by
  subst P'
  rfl
end RawScanProgram
end BitWord
