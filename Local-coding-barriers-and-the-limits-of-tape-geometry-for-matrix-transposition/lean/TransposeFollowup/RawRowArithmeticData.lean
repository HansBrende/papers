import TransposeFollowup.CoupledRowScan
import TransposeFollowup.ModularRowWord
import TransposeFollowup.MaskedStrideCell

/-! The finite update table implements the existing carry recurrence.
Subtraction saves the original current row for the next difference;
addition saves its output. Blank scratch symbols decode to zero. -/
namespace TransposeFollowup.RawRowArithmetic
open FixedTapeCompiler
open CopyMachine (Sym symbols)
open CoupledRowCell (Mode)
open MaskedStrideCell (bit)
set_option autoImplicit false

def update (sub : Bool) (m : Mode) : Mode :=
  let a := bit m.2.1
  let b := BinaryCarry.operandBit sub (bit m.2.2)
  let y := BinaryCarry.digit m.1 a b
  (BinaryCarry.carry m.1 a b,.data y,.data (if sub then a else y))

theorem evaluate_eq (sub c : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    CoupledRowScan.evaluate (update sub) c xs ys=
      let r := BinaryCarry.result sub c (xs.map bit) (ys.map bit)
      (r.2,symbols r.1,symbols (if sub then xs.map bit else r.1)) := by
  induction xs generalizing c ys with
  | nil => cases sub <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [CoupledRowScan.evaluate,update,List.map_cons,BinaryCarry.result]
      rw [ih _ ys (by simpa using h)]
      cases sub <;> rfl

def output (sub : Bool) (xs ys : List (Sym Bool)) : List Bool :=
  ModularRowWord.rawOperation sub (xs.map bit) (ys.map bit)

def saved (sub : Bool) (xs ys : List (Sym Bool)) : List Bool :=
  if sub then xs.map bit else output sub xs ys

theorem raw_outputs (sub : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    (CoupledRowScan.evaluate (update sub) sub xs.reverse ys.reverse).2.1.reverse=
        symbols (output sub xs ys) ∧
    (CoupledRowScan.evaluate (update sub) sub xs.reverse ys.reverse).2.2.reverse=
        symbols (saved sub xs ys) := by
  rw [evaluate_eq sub sub xs.reverse ys.reverse (by simpa using h)]
  cases sub <;> simp only [output,saved,ModularRowWord.rawOperation,ModularRowWord.operation,
    symbols,List.map_reverse,List.reverse_reverse,Bool.false_eq_true,ite_false,ite_true,and_self]

theorem output_length (sub : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    (output sub xs ys).length=xs.length := by
  simpa only [output,List.length_map,h] using
    ModularRowWord.rawOperation_length sub (xs.map bit) (ys.map bit) (by simpa using h)

theorem saved_length (sub : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    (saved sub xs ys).length=xs.length := by
  cases sub <;> simp [saved,output_length _ _ _ h]

theorem output_value (sub : Bool) (xs ys : List (Sym Bool)) (h : xs.length=ys.length) :
    ModularRowWord.rawValue (output sub xs ys)=
      (if sub then ModularRowWord.rawValue (xs.map bit)+2^xs.length-ModularRowWord.rawValue (ys.map bit)
        else ModularRowWord.rawValue (xs.map bit)+ModularRowWord.rawValue (ys.map bit))%2^xs.length := by
  simpa only [output,List.length_map,h] using
    ModularRowWord.rawOperation_value sub (xs.map bit) (ys.map bit) (by simpa using h)

end TransposeFollowup.RawRowArithmetic
