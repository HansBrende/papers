import TransposeFollowup.NativeCounter

/-! The archived length-counting identity, expressed using the already
imported decrementer. Start with m ones, decrement m times, and complement.
The m-bit result represents m; no variable multiplication or division is
needed. Trimming it to logarithmic width is a separate physical operation. -/
namespace TransposeFollowup.MeasuredWord
open FixedTapeCompiler
set_option autoImplicit false

theorem nonzero (xs : List Bool) (hx : 0<Counter.value xs) : Counter.isZero xs=false := by
  cases hz : Counter.isZero xs
  · rfl
  · have h := (Counter.value_zero_iff xs).mpr hz
    omega

theorem after_length (r : ℕ) (xs : List Bool) : (Counter.wordAfter r xs).length=xs.length := by
  induction r generalizing xs with
  | zero => rfl
  | succ r ih => simpa only [Counter.wordAfter,Counter.length_decrement] using ih (Counter.decrement xs)

theorem after_value (r : ℕ) (xs : List Bool) (hr : r ≤ Counter.value xs) :
    Counter.value (Counter.wordAfter r xs)+r=Counter.value xs := by
  induction r generalizing xs with
  | zero => simp [Counter.wordAfter]
  | succ r ih =>
    have hd := Counter.decrement_value xs (nonzero xs (by omega))
    have h := ih (Counter.decrement xs) (by omega)
    simpa only [Counter.wordAfter] using (show Counter.value (Counter.wordAfter r (Counter.decrement xs))+(r+1)=Counter.value xs by omega)

theorem ones_value (m : ℕ) : Counter.value (List.replicate m true)+1=2^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ,Counter.value,pow_succ]; omega

theorem capacity (m : ℕ) : m ≤ Counter.value (List.replicate m true) := by
  have h := ones_value m
  have hp := Nat.lt_two_pow_self (n:=m)
  omega

theorem complement_value (xs : List Bool) :
    Counter.value (xs.map Bool.not)+Counter.value xs+1=2^xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [List.map_cons,Bool.not_false,Bool.not_true,Counter.value,List.length_cons,pow_succ] <;> omega

def counted (m : ℕ) : List Bool := Counter.wordAfter m (List.replicate m true)
def result (m : ℕ) : List Bool := (counted m).map Bool.not

theorem result_length (m : ℕ) : (result m).length=m := by
  simp only [result,counted,List.length_map,after_length,List.length_replicate]

theorem result_value (m : ℕ) : Counter.value (result m)=m := by
  have hv := after_value m (List.replicate m true) (capacity m)
  have ho := ones_value m
  have hc := complement_value (counted m)
  have hl : (counted m).length=m := by simp [counted,after_length]
  rw [hl] at hc
  change Counter.value (result m)+Counter.value (counted m)+1=2^m at hc
  change Counter.value (counted m)+m=Counter.value (List.replicate m true) at hv
  omega

theorem decrement_budget (m : ℕ) : 2*Counter.totalCost m (List.replicate m true) ≤ 12*m := by
  have h := NativeCounter.native_sequence_budget m (List.replicate m true)
  simp only [List.length_replicate] at h
  omega

end TransposeFollowup.MeasuredWord
