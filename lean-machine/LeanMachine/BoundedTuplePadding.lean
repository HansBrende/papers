import LeanMachine.BoundedTuples

/-! Zero-padding a bounded tuple to a larger fixed menu preserves its exact
sum and is injective. This pays a public capacity, never an extra set size. -/

namespace LeanMachine
open scoped BigOperators

def paddedTupleFunction {m n : ℕ} (f : Fin m → ℕ) (i : Fin n) : ℕ :=
  if hi : i.val < m then f ⟨i.val, hi⟩ else 0

theorem sum_paddedTupleFunction {m n : ℕ} (f : Fin m → ℕ) (h : m ≤ n) :
    ∑ i : Fin n, paddedTupleFunction f i = ∑ i : Fin m, f i := by
  induction n, h using Nat.le_induction with
  | base =>
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [paddedTupleFunction, dite_eq_left i.isLt]
  | succ n h ih =>
    rw [Fin.sum_univ_castSucc]
    have hf : (fun i : Fin n => paddedTupleFunction f i.castSucc) =
        fun i : Fin n => paddedTupleFunction f i := by
      funext i
      rfl
    rw [hf, ih]
    have hn : ¬ n < m := Nat.not_lt.mpr h
    simp only [paddedTupleFunction, Fin.val_last, dite_eq_right hn, add_zero]

def padBoundedTuple {m n T : ℕ} (h : m ≤ n) (f : BoundedTuple m T) : BoundedTuple n T :=
  ⟨paddedTupleFunction f.val, by rw [sum_paddedTupleFunction _ h]; exact f.property⟩

theorem padBoundedTuple_apply {m n T : ℕ} (h : m ≤ n) (f : BoundedTuple m T) (i : Fin m) :
    (padBoundedTuple h f).val (Fin.castLE h i) = f.val i := by
  simp only [padBoundedTuple, paddedTupleFunction, Fin.val_castLE, dite_eq_left i.isLt]

theorem padBoundedTuple_injective {m n T : ℕ} (h : m ≤ n) :
    Function.Injective (@padBoundedTuple m n T h) := by
  intro f g he
  apply Subtype.ext
  funext i
  have hh := congrFun (congrArg Subtype.val he) (Fin.castLE h i)
  simpa only [padBoundedTuple_apply] using hh

end LeanMachine
