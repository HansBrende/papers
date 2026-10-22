import TransposeFollowup.RawRowArithmeticData

/-! Increment and decrement are the existing carry recurrence with zero
second operand and the opposite initial carry. Arithmetic is modulo the
full fixed word width, including the zero-width case. -/
namespace TransposeFollowup.RawUnitArithmetic
open FixedTapeCompiler
open CopyMachine (Sym symbols)
open MaskedStrideCell (bit)
set_option autoImplicit false

def output (sub : Bool) (xs : List Bool) : List Bool :=
  (BinaryCarry.result sub (!sub) xs.reverse (List.replicate xs.length false)).1.reverse

theorem output_length (sub : Bool) (xs : List Bool) : (output sub xs).length=xs.length := by
  simpa only [output,List.length_reverse] using
    BinaryCarry.result_length sub (!sub) xs.reverse (List.replicate xs.length false) (by simp)

theorem output_value (sub : Bool) (xs : List Bool) :
    ModularRowWord.rawValue (output sub xs)=
      (if sub then ModularRowWord.rawValue xs+2^xs.length-1
        else ModularRowWord.rawValue xs+1)%2^xs.length := by
  have hz : BinaryCompare.value (List.replicate xs.length false)=0 := by
    simp [BinaryCompare.value]
  have hc := BinaryCarry.complement_identity (List.replicate xs.length false)
  simp only [hz,List.length_replicate,zero_add] at hc
  have hi := BinaryCarry.result_identity sub (!sub) xs.reverse (List.replicate xs.length false) (by simp)
  simp only [List.length_reverse] at hi
  have he : BinaryCompare.value
        (BinaryCarry.result sub (!sub) xs.reverse (List.replicate xs.length false)).1+
      2^xs.length*(BinaryCarry.result sub (!sub) xs.reverse (List.replicate xs.length false)).2.toNat=
      if sub then ModularRowWord.rawValue xs+2^xs.length-1 else ModularRowWord.rawValue xs+1 := by
    cases sub
    · simpa only [Bool.not_false,Bool.toNat_true,BinaryCarry.operandWord_false,hz,add_zero,
        Bool.false_eq_true,ite_false,ModularRowWord.rawValue] using hi
    · simp only [Bool.not_true,Bool.toNat_false,add_zero,ite_true,ModularRowWord.rawValue] at hi ⊢
      omega
  have hl : BinaryCompare.value
      (BinaryCarry.result sub (!sub) xs.reverse (List.replicate xs.length false)).1 < 2^xs.length := by
    have h := BinaryCarry.value_lt
      (BinaryCarry.result sub (!sub) xs.reverse (List.replicate xs.length false)).1
    simpa only [BinaryCarry.result_length sub (!sub) xs.reverse
      (List.replicate xs.length false) (by simp),List.length_reverse] using h
  have hm := congrArg (fun n => n%2^xs.length) he
  simpa only [output,ModularRowWord.rawValue,List.reverse_reverse,Nat.add_mod,
    Nat.mul_mod_right,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hl] using hm

theorem evaluate_output (sub : Bool) (xs : List (Sym Bool)) :
    (CoupledRowScan.evaluate (RawRowArithmetic.update sub) (!sub) xs.reverse
      (List.replicate xs.length .blank)).2.1.reverse=symbols (output sub (xs.map bit)) := by
  rw [RawRowArithmetic.evaluate_eq sub (!sub) xs.reverse (List.replicate xs.length .blank) (by simp)]
  simp only [output,symbols,List.map_replicate,List.map_reverse,List.length_map,bit]

end TransposeFollowup.RawUnitArithmetic
