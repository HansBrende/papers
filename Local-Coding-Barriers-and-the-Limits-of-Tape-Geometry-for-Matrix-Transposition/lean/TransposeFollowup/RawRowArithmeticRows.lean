import TransposeFollowup.RawRowArithmeticNative
import TransposeFollowup.BufferedRowRows

/-! Repeated raw-row updates use the existing finite-word scheduler.
The list semantics keeps the previous output for addition and the previous
original row for subtraction. The head remains at the end of the bank;
buffer clearing, rewind and raw external IO are separate paid obligations. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym symbols)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false

def rule (sub : Bool) : BufferedRows.Rule Bool where
  table := update sub
  carry := sub
  output xs ys := symbols (output sub xs ys)
  saved xs ys := symbols (saved sub xs ys)
  realizes := raw_outputs sub

def rowsResult (sub : Bool) (rows : List (List (Sym Bool))) :
    List (Sym Bool) → List (Sym Bool) × List (Sym Bool) :=
  rows.foldr (fun xs go ys =>
    let r := go (symbols (saved sub xs ys))
    (symbols (output sub xs ys)++r.1,r.2)) (fun ys => ([],ys))

def rowsSchedule (sub : Bool) (W r : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  ScheduledWord.schedule (fun _ : Unit => ticks W) (fun _ => schedule sub W)
    CoupledRowScan.idle (List.replicate r ())

theorem rows_active (sub : Bool) (W r i : ℕ) (c : State) :
    NativeIO.Active (rowsSchedule sub W r i) c :=
  BufferedRows.rows_active (rule sub) W r i c

theorem rows_lengths (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (ys : List (Sym Bool)) (hy : ys.length=W) :
    (rowsResult sub rows ys).1.length=rows.length*W ∧
      (rowsResult sub rows ys).2.length=W :=
  BufferedRows.rows_lengths (rule sub) W rows hw ys hy

theorem rows_exact (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode)
    (ys la lb ra rb : List (Sym Bool)) (hy : ys.length=W)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    ∃ m' : Mode,
      trajectory (rowsSchedule sub W rows.length) w
        (initial m rows.flatten ys la lb ra rb pos ip out) (rows.length*ticks W)=
      cfg m' ![⟨(rowsResult sub rows ys).1.reverse++la,ra⟩,
        ⟨lb,(rowsResult sub rows ys).2++rb⟩]
        (fun t => pos t+if bankOnly t then (rows.length*W : ℕ) else 0) ip out :=
  BufferedRows.rows_exact (rule sub) W rows hw m ys la lb ra rb hy pos ip out w

end TransposeFollowup.RawRowArithmetic
