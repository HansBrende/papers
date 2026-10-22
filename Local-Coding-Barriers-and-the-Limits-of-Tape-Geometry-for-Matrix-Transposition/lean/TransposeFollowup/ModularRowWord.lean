import TransposeFollowup.RepeatedAddData

/-! Fixed-width modular row arithmetic reuses the existing carry recurrence
and modular addition proof. Raw rows are big-endian; the carried operands
are little-endian. Reversal here is a semantic definition, not free IO. -/
namespace TransposeFollowup.ModularRowWord
open BinaryCompare (value)
set_option autoImplicit false

def operation (sub : Bool) (a x : List Bool) : List Bool := (BinaryCarry.result sub sub a x).1

theorem operation_length (sub : Bool) (a x : List Bool) (h : a.length=x.length) :
    (operation sub a x).length=x.length := (BinaryCarry.result_length sub sub a x h).trans h

theorem subtract_value (a x : List Bool) (h : a.length=x.length) :
    value (operation true a x)=(value a+2^x.length-value x)%2^x.length := by
  have hi := BinaryCarry.subtraction_identity a x h
  rw [h] at hi
  have he : value (operation true a x)+2^x.length*(BinaryCarry.result true true a x).2.toNat =
      value a+2^x.length-value x := by dsimp [operation]; omega
  have hv : value (operation true a x)<2^x.length := by
    simpa only [operation_length true a x h] using BinaryCarry.value_lt (operation true a x)
  have hm := congrArg (fun n => n%2^x.length) he
  simpa only [Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hv] using hm

theorem operation_value (sub : Bool) (a x : List Bool) (h : a.length=x.length) :
    value (operation sub a x)=
      (if sub then value a+2^x.length-value x else value a+value x)%2^x.length := by
  cases sub
  · exact RepeatedAdd.addWord_value a x h
  · exact subtract_value a x h

def rawValue (xs : List Bool) : ℕ := value xs.reverse

def rawOperation (sub : Bool) (a x : List Bool) : List Bool :=
  (operation sub a.reverse x.reverse).reverse

theorem rawOperation_length (sub : Bool) (a x : List Bool) (h : a.length=x.length) :
    (rawOperation sub a x).length=x.length := by
  simpa only [rawOperation,List.length_reverse] using operation_length sub a.reverse x.reverse (by simpa using h)

theorem rawOperation_value (sub : Bool) (a x : List Bool) (h : a.length=x.length) :
    rawValue (rawOperation sub a x)=
      (if sub then rawValue a+2^x.length-rawValue x else rawValue a+rawValue x)%2^x.length := by
  simpa only [rawValue,rawOperation,List.reverse_reverse,List.length_reverse] using
    operation_value sub a.reverse x.reverse (by simpa using h)

end TransposeFollowup.ModularRowWord
