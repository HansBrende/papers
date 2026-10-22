import TransposeFollowup.BinaryCompareData

/-! One carry recurrence handles addition and complemented-input subtraction.
The word has fixed width; overflow/no-borrow is returned as one Boolean. -/

namespace TransposeFollowup.BinaryCarry
set_option autoImplicit false
open BinaryCompare (value)

def digit (c a b : Bool) : Bool := xor (xor a b) c
def carry (c a b : Bool) : Bool := (a && b) || (a && c) || (b && c)
def operandBit (sub b : Bool) : Bool := xor sub b
def operandWord (sub : Bool) (ys : List Bool) : List Bool := ys.map (operandBit sub)

theorem digit_identity (c a b : Bool) :
    (digit c a b).toNat + 2 * (carry c a b).toNat = a.toNat + b.toNat + c.toNat := by
  cases c <;> cases a <;> cases b <;> decide

def result (sub : Bool) : Bool → List Bool → List Bool → List Bool × Bool
  | c, a :: xs, b :: ys =>
    let r := result sub (carry c a (operandBit sub b)) xs ys
    (digit c a (operandBit sub b) :: r.1, r.2)
  | c, _, _ => ([], c)

theorem result_length (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length) :
    (result sub c xs ys).1.length = xs.length := by
  induction xs generalizing ys c with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [result, List.length_cons]
      rw [ih _ _ (by simpa using h)]

theorem value_lt (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    rw [BinaryCompare.value_cons, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem result_identity (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length) :
    value (result sub c xs ys).1 + 2 ^ xs.length * (result sub c xs ys).2.toNat =
      value xs + value (operandWord sub ys) + c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp [result, operandWord]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have hi := ih (carry c a (operandBit sub b)) ys (by simpa using h)
      have hd := digit_identity c a (operandBit sub b)
      simp only [result, BinaryCompare.value_cons, List.length_cons, pow_succ,
        operandWord, List.map_cons] at hi ⊢
      nlinarith

@[simp] theorem operandWord_false (ys : List Bool) : operandWord false ys = ys := by
  have hf : operandBit false = id := by funext b; cases b <;> rfl
  simp [operandWord, hf]

theorem complement_identity (ys : List Bool) :
    value ys + value (operandWord true ys) + 1 = 2 ^ ys.length := by
  induction ys with
  | nil => rfl
  | cons b ys ih =>
    simp only [operandWord, List.map_cons, BinaryCompare.value_cons, List.length_cons,
      pow_succ] at ih ⊢
    cases b <;> simp only [operandBit, Bool.toNat_false, Bool.toNat_true,
      Bool.true_xor, Bool.not_false, Bool.not_true] <;> nlinarith

theorem addition_identity (xs ys : List Bool) (h : xs.length = ys.length) :
    value (result false false xs ys).1 + 2 ^ xs.length * (result false false xs ys).2.toNat =
      value xs + value ys := by
  simpa using result_identity false false xs ys h

theorem subtraction_identity (xs ys : List Bool) (h : xs.length = ys.length) :
    value (result true true xs ys).1 + 2 ^ xs.length * (result true true xs ys).2.toNat +
      value ys = value xs + 2 ^ xs.length := by
  have hi := result_identity true true xs ys h
  have hc := complement_identity ys
  rw [← h] at hc
  simp only [Bool.toNat_true] at hi
  omega

theorem noBorrow_iff (xs ys : List Bool) (h : xs.length = ys.length) :
    (result true true xs ys).2 = true ↔ value ys ≤ value xs := by
  have hi := subtraction_identity xs ys h
  have hv := value_lt (result true true xs ys).1
  rw [result_length _ _ _ _ h] at hv
  cases hc : (result true true xs ys).2 <;> simp only [hc, Bool.toNat_false,
    Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at hi <;> simp_all <;> omega

theorem subtract_value (xs ys : List Bool) (h : xs.length = ys.length)
    (hle : value ys ≤ value xs) :
    value (result true true xs ys).1 = value xs - value ys := by
  have hi := subtraction_identity xs ys h
  rw [(noBorrow_iff xs ys h).mpr hle] at hi
  simp only [Bool.toNat_true, Nat.mul_one] at hi
  omega

theorem carry_iff (xs ys : List Bool) (h : xs.length = ys.length) :
    (result false false xs ys).2 = true ↔ 2 ^ xs.length ≤ value xs + value ys := by
  have hi := addition_identity xs ys h
  have hv := value_lt (result false false xs ys).1
  rw [result_length _ _ _ _ h] at hv
  cases hc : (result false false xs ys).2 <;> simp only [hc, Bool.toNat_false,
    Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at hi <;> simp_all
  omega

theorem add_value (xs ys : List Bool) (h : xs.length = ys.length)
    (hlt : value xs + value ys < 2 ^ xs.length) :
    value (result false false xs ys).1 = value xs + value ys := by
  have hi := addition_identity xs ys h
  have hc : (result false false xs ys).2 = false := by
    have := (carry_iff xs ys h).not.mpr (by omega)
    cases hh : (result false false xs ys).2 <;> simp_all
  rw [hc] at hi
  simpa using hi

end TransposeFollowup.BinaryCarry
