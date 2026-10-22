import TransposeFollowup.BinaryCarryData
import TransposeFollowup.CappedAdditiveDivision

/-! The word-level specification of the repeated-addition controller. -/

namespace TransposeFollowup.RepeatedAdd

open BinaryCompare (value)
set_option autoImplicit false

def addWord (a x : List Bool) : List Bool := (BinaryCarry.result false false a x).1

theorem addWord_length (a x : List Bool) (h : a.length = x.length) :
    (addWord a x).length = x.length :=
  (BinaryCarry.result_length false false a x h).trans h

theorem addWord_value (a x : List Bool) (h : a.length = x.length) :
    value (addWord a x) = (value a + value x) % 2 ^ x.length := by
  have hi := congrArg (fun n => n % 2 ^ x.length) (BinaryCarry.addition_identity a x h)
  have hv : value (addWord a x) < 2 ^ x.length := by
    simpa only [addWord_length a x h] using BinaryCarry.value_lt (addWord a x)
  change value (BinaryCarry.result false false a x).1 < 2 ^ x.length at hv
  simpa [addWord, h, Nat.add_mod, Nat.mod_eq_of_lt hv] using hi

theorem copy_with_zero (xs : List Bool) :
    BinaryCarry.result false false xs (List.replicate xs.length false) = (xs, false) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a <;> simp [BinaryCarry.result, BinaryCarry.digit, BinaryCarry.carry,
      BinaryCarry.operandBit, List.replicate_succ, ih]

def repeatWord (x : List Bool) : ℕ → List Bool → List Bool
  | 0, a => a
  | n + 1, a => repeatWord x n (addWord a x)

theorem repeatWord_length (x : List Bool) (n : ℕ) (a : List Bool)
    (h : a.length = x.length) : (repeatWord x n a).length = x.length := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih => exact ih _ (addWord_length a x h)

theorem repeatWord_value (x : List Bool) (n : ℕ) (a : List Bool)
    (h : a.length = x.length) :
    value (repeatWord x n a) = (value a + n * value x) % 2 ^ x.length := by
  induction n generalizing a with
  | zero => simp only [repeatWord, Nat.zero_mul, Nat.add_zero,
      Nat.mod_eq_of_lt (by simpa [h] using BinaryCarry.value_lt a)]
  | succ n ih =>
    rw [repeatWord, ih _ (addWord_length a x h), addWord_value a x h]
    rw [Nat.mod_add_mod]
    congr 1
    ring

theorem repeatWord_value_exact (x : List Bool) (n : ℕ) (a : List Bool)
    (h : a.length = x.length) (hfit : value a + n * value x < 2 ^ x.length) :
    value (repeatWord x n a) = value a + n * value x := by
  rw [repeatWord_value x n a h, Nat.mod_eq_of_lt hfit]

end TransposeFollowup.RepeatedAdd
