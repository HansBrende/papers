import TransposeFollowup.RepeatedAddData

/-! Signed integers represented by differences of nonnegative binary words.
Cross-sum comparison requires explicit fit conditions; cancellation in the
represented integer alone is insufficient to justify a finite word width. -/

namespace TransposeFollowup.SignedPair

open BinaryCompare (Result value)
set_option autoImplicit false

def integer (a b : List Bool) : ℤ := (value a : ℤ) - (value b : ℤ)

def numeric (x y : ℤ) : Result :=
  if x < y then .less else if y < x then .greater else .equal

theorem numeric_less (x y : ℤ) : numeric x y = .less ↔ x < y := by
  simp only [numeric]
  split_ifs <;> simp_all

theorem numeric_equal (x y : ℤ) : numeric x y = .equal ↔ x = y := by
  simp only [numeric]
  split_ifs <;> simp_all <;> omega

theorem numeric_greater (x y : ℤ) : numeric x y = .greater ↔ y < x := by
  by_cases hxy : x < y
  · have hyx : ¬y < x := by omega
    simp [numeric, hxy, hyx]
  · simp [numeric, hxy]

theorem cross_sum (a b c d : ℕ) :
    BinaryCompare.numeric .equal (a+d) (c+b) =
      numeric ((a : ℤ) - b) ((c : ℤ) - d) := by
  simp only [BinaryCompare.numeric, numeric]
  split_ifs <;> first | rfl | omega

def result (a b c d : List Bool) : Result :=
  BinaryCompare.numeric .equal (value (RepeatedAdd.addWord a d))
    (value (RepeatedAdd.addWord c b))

theorem result_spec (a b c d : List Bool)
    (had : a.length = d.length) (hcb : c.length = b.length)
    (hleft : value a + value d < 2 ^ d.length)
    (hright : value c + value b < 2 ^ b.length) :
    result a b c d = numeric (integer a b) (integer c d) := by
  simp only [result, RepeatedAdd.addWord_value a d had,
    RepeatedAdd.addWord_value c b hcb, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  exact cross_sum _ _ _ _

/-- One spare high bit suffices when each nonnegative component is bounded.
This says nothing about how the padded words are loaded on the machine. -/
theorem cross_sums_fit (m a b c d : ℕ)
    (ha : a < 2 ^ m) (hb : b < 2 ^ m) (hc : c < 2 ^ m) (hd : d < 2 ^ m) :
    a + d < 2 ^ (m+1) ∧ c + b < 2 ^ (m+1) := by
  rw [pow_succ]
  omega

end TransposeFollowup.SignedPair
