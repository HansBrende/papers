import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

/-! Little-endian binary comparison, including zero-width and padded words.
The most significant unequal digit overrides the earlier comparison. -/

namespace TransposeFollowup.BinaryCompare
set_option autoImplicit false

inductive Result | less | equal | greater
  deriving DecidableEq

instance : Fintype Result where
  elems := {.less, .equal, .greater}
  complete := by intro r; cases r <;> simp

def value (xs : List Bool) : ℕ := Nat.ofDigits 2 (xs.map Bool.toNat)

@[simp] theorem value_nil : value [] = 0 := rfl

@[simp] theorem value_cons (b : Bool) (xs : List Bool) :
    value (b :: xs) = b.toNat + 2 * value xs := rfl

def update (r : Result) (a b : Bool) : Result :=
  if a = b then r else if a then .greater else .less

def scan : Result → List Bool → List Bool → Result
  | r, a :: xs, b :: ys => scan (update r a b) xs ys
  | r, _, _ => r

def numeric (r : Result) (a b : ℕ) : Result :=
  if a < b then .less else if b < a then .greater else r

theorem numeric_digit (r : Result) (a b : Bool) (x y : ℕ) :
    numeric (update r a b) x y = numeric r (a.toNat + 2*x) (b.toNat + 2*y) := by
  cases a <;> cases b <;>
    simp only [numeric, update, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, zero_add] <;>
    split_ifs <;> first | rfl | omega

theorem scan_numeric (r : Result) (xs ys : List Bool) (h : xs.length = ys.length) :
    scan r xs ys = numeric r (value xs) (value ys) := by
  induction xs generalizing ys r with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp [scan, numeric]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      rw [scan, ih _ _ (by simpa using h), value_cons, value_cons, numeric_digit]

theorem scan_equal_iff (xs ys : List Bool) (h : xs.length = ys.length) :
    scan .equal xs ys = .equal ↔ value xs = value ys := by
  rw [scan_numeric _ _ _ h]
  simp only [numeric]
  split_ifs <;> simp_all <;> omega

end TransposeFollowup.BinaryCompare
