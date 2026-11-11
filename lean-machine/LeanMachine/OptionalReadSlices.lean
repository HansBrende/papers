import Mathlib

/-! # Actual optional-read counts in consecutive list slices -/

namespace LeanMachine.OptionalReadSlices

open Finset
open scoped BigOperators

def reads {A : Type*} (xs : List (Option A)) : ℕ := (xs.filterMap id).length

theorem reads_append {A : Type*} (xs ys : List (Option A)) :
    reads (xs ++ ys) = reads xs + reads ys := by simp [reads]

theorem reads_take_le {A : Type*} (xs : List (Option A)) (n : ℕ) :
    reads (xs.take n) ≤ reads xs := by
  have he := reads_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at he
  omega

theorem reads_slice_add {A : Type*} (xs : List (Option A)) {a e : ℕ} (hae : a ≤ e) :
    reads ((xs.drop a).take (e - a)) + reads (xs.take a) = reads (xs.take e) := by
  have he : xs.take e = xs.take a ++ (xs.drop a).take (e - a) := by
    conv_lhs => rw [← Nat.add_sub_of_le hae]
    exact List.take_add
  rw [he, reads_append, Nat.add_comm]

theorem sum_reads_slices {A : Type*} (xs : List (Option A))
    (cut : ℕ → ℕ) (hcut : Monotone cut) (m : ℕ) :
    (∑ j ∈ range m, reads ((xs.drop (cut j)).take (cut (j + 1) - cut j))) +
      reads (xs.take (cut 0)) = reads (xs.take (cut m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hh := reads_slice_add xs (hcut (show m ≤ m + 1 by omega))
    omega

/-- Windows cover a prefix, so unread trailing local steps or reads do not
increase the sum paid to those windows. -/
theorem sum_reads_slices_le {A : Type*} (xs : List (Option A))
    (cut : ℕ → ℕ) (hcut : Monotone cut) (m : ℕ) :
    ∑ j : Fin m, reads ((xs.drop (cut j.val)).take (cut (j.val + 1) - cut j.val)) ≤ reads xs := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => reads ((xs.drop (cut j)).take (cut (j + 1) - cut j)))]
  have hh := sum_reads_slices xs cut hcut m
  have hl := reads_take_le xs (cut m)
  omega

end LeanMachine.OptionalReadSlices
