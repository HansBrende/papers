import TransposeFollowup.BitPlaneRun
import TransposeFollowup.NativeMicrocode
import TransposeFollowup.FiniteProgramEncodingCore

/-! A fixed finite controller for a captured call of an arbitrary native machine.
The original machine is first represented by its already verified five-symbol
bit planes. Input and output are work tapes of the caller; history replay restores
those tapes without auxiliary origin or visited tracks. This file defines the literal
controller, not an assumed oracle instruction. -/
namespace BitWord.NativeOracle
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false

abbrev workCount (M : Transpose.TM) := M.k * BitPlaneAlphabet.width M.g
abbrev State (M : Transpose.TM) := Fin (M.q + 1)
abbrev Scanned (M : Transpose.TM) := Fin (workCount M) → Fin 5
abbrev Transition (M : Transpose.TM) := BitPlaneMachine.PlaneTransition M

/-- The existing bit-plane machine, with its fixed resource fields exposed for
finite controller indexing. This is definitionally the verified machine. -/
abbrev plane (M : Transpose.TM) : Transpose.TM :=
  { k := workCount M, g := 4, q := M.q, δ := BitPlaneMachine.delta M }

theorem plane_eq (M : Transpose.TM) : plane M=BitPlaneMachine.machine M := rfl

inductive Port (M : Transpose.TM)
  | input | capture | work (i : Fin (workCount M))
  deriving DecidableEq, Fintype

inductive Label (M : Transpose.TM)
  | input (state : State M)
  | scan (state : State M) (input : Option Bool) (seen : Scanned M)
      (next : Fin (workCount M + 1))
  | done
  deriving DecidableEq, Fintype

def start (M : Transpose.TM) : Label M := .input 0

def inputSymbol : Sym Bool → Option Bool
  | .data b => some b
  | _ => none

def move : Transpose.Dir → Microcode.Move
  | .left => .left | .stay => .stay | .right => .right

@[simp] theorem direction_move (d : Transpose.Dir) : NativeMicrocode.direction (move d) = d := by
  cases d <;> rfl

def actions (M : Transpose.TM) (tr : Transition M) : Port M → Microcode.Action
  | .input => ⟨none, move tr.2.1⟩
  | .work i => ⟨some (NativeMicrocode.symbolDecode (tr.2.2.1 i).1), move (tr.2.2.1 i).2⟩
  | .capture => ⟨tr.2.2.2.map Sym.data, if tr.2.2.2.isSome then .right else .stay⟩

def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .input state => .read .input (fun a => .scan state (inputSymbol a) (fun _ => 0) 0)
  | .scan state input seen next =>
      if hn : next.val < workCount M then
        .read (.work ⟨next.val, hn⟩) (fun a =>
          .scan state input (Function.update seen ⟨next.val, hn⟩ (NativeMicrocode.symbolCode a))
            ⟨next.val + 1, by omega⟩)
      else match (plane M).δ state input seen with
        | none => .jump .done
        | some tr => .act (actions M tr) (.input tr.1)
  | .done => .halt

noncomputable def encoding (M : Transpose.TM) :=
  NativeMicrocode.initialEncoding (T := Port M) (start M)
noncomputable def machine (M : Transpose.TM) :=
  NativeMicrocode.machine (encoding M) (program M)

def portEquiv (M : Transpose.TM) : Port M ≃ Fin 2 ⊕ Fin (workCount M) where
  toFun
    | .input => .inl 0 | .capture => .inl 1 | .work i => .inr i
  invFun
    | .inl j => if j=0 then .input else .capture
    | .inr i => .work i
  left_inv p := by cases p <;> simp
  right_inv p := by
    cases p with
    | inl j => fin_cases j <;> rfl
    | inr i => rfl

theorem fixed_resources (M : Transpose.TM) :
    (machine M).k = workCount M + 2 ∧ (machine M).g + 1 = 5 ∧
      (encoding M).label (start M) = 0 := by
  refine ⟨?_, rfl, NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Port M) = _
  rw [Fintype.card_congr (portEquiv M)]
  simp
  omega

/-- Scalar control and tape count depend on the simulated machine alone. -/
theorem oracle_computes_five_symbol (M : Transpose.TM) (w out : List Bool) (t : ℕ)
    (h : Transpose.ComputesWithin M w out t) :
    Transpose.ComputesWithin (plane M) w out t :=
  BitPlaneMachine.computesWithin M w out t h

end BitWord.NativeOracle
