import TransposeFollowup.ScheduledWord
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A finite indexed expansion of the already proved chronological word
path. Missing slots contribute zero analytically, with no extra execution. -/
namespace TransposeFollowup.ScheduledWord
open Classical Finset
set_option autoImplicit false
variable {O T : Type*}

theorem path_eq_sum_slots (cost : O → ℕ) (move : O → T → ℕ → ℤ)
    (ops : List O) (K : ℕ) (hK : ops.length ≤ K) (t : T) (n : ℕ) :
    path cost move ops t n = ∑ j ∈ range K,
      (ops[j]?).elim 0 (fun op => move op t (n-ticks cost (ops.take j))) := by
  induction K generalizing ops n with
  | zero => have he : ops=[] := List.length_eq_zero_iff.mp (by omega); simp [he,path]
  | succ K ih =>
    cases ops with
    | nil => simp [path]
    | cons op ops =>
      have hlen : ops.length ≤ K := by simpa using hK
      rw [path,Finset.sum_range_succ']
      simp only [List.getElem?_cons_zero,List.take_zero,ticks,List.map_nil,List.sum_nil,Nat.sub_zero,Option.elim_some]
      rw [ih ops hlen (n-cost op)]
      rw [add_comm (move op t n)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [List.getElem?_cons_succ,List.take_succ_cons,ticks,List.map_cons,List.sum_cons,Nat.sub_sub]

end TransposeFollowup.ScheduledWord
