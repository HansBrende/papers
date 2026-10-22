import Mathlib.Tactic

/-! Quotients needed for grid neighbors may be capped at the grid size.
This reference loop uses comparison and addition only. Its fuel must still
be implemented by a paid physical counter; these are arithmetic invariants,
not a native time theorem. Negative numerators are included. -/

namespace TransposeFollowup
set_option autoImplicit false

def repeatedAdd (x : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => repeatedAdd x n + x

theorem repeatedAdd_eq (x : ℤ) (n : ℕ) : repeatedAdd x n = n * x := by
  induction n with
  | zero => simp [repeatedAdd]
  | succ n ih => simp [repeatedAdd, ih, add_mul]

def quotientStep (a d : ℤ) (s : ℕ × ℤ) : ℕ × ℤ :=
  if s.2 ≤ a then (s.1 + 1, s.2 + d) else s

def quotientRun (a d : ℤ) : ℕ → ℕ × ℤ
  | 0 => (0, d)
  | n + 1 => quotientStep a d (quotientRun a d n)

theorem trial_le_iff (a d : ℤ) (hd : 0 < d) (q : ℕ) :
    ((q : ℤ) + 1) * d ≤ a ↔ q < (a / d).toNat := by
  rw [← Int.le_ediv_iff_mul_le hd]
  omega

theorem quotientRun_eq (a d : ℤ) (hd : 0 < d) (n : ℕ) :
    quotientRun a d n =
      (min n (a / d).toNat, ((min n (a / d).toNat : ℕ) + 1 : ℤ) * d) := by
  induction n with
  | zero => simp [quotientRun]
  | succ n ih =>
    rw [quotientRun, ih]
    dsimp only [quotientStep]
    split_ifs with h
    · have hq := (trial_le_iff a d hd (min n (a / d).toNat)).mp h
      have hm : min (n + 1) (a / d).toNat = min n (a / d).toNat + 1 := by omega
      rw [hm]
      congr 1
      push_cast
      ring
    · have hq := (trial_le_iff a d hd (min n (a / d).toNat)).not.mp h
      have hm : min (n + 1) (a / d).toNat = min n (a / d).toNat := by omega
      rw [hm]

theorem quotientRun_bounds (a d : ℤ) (hd : 0 < d) (n : ℕ) :
    (quotientRun a d n).1 ≤ n ∧
      d ≤ (quotientRun a d n).2 ∧ (quotientRun a d n).2 ≤ ((n : ℤ) + 1) * d := by
  rw [quotientRun_eq a d hd]
  have hn : ((min n (a / d).toNat : ℕ) : ℤ) ≤ (n : ℤ) :=
    Int.ofNat_le.mpr (min_le_left _ _)
  have hq : (0 : ℤ) ≤ min n (a / d).toNat := by positivity
  refine ⟨min_le_left _ _, ?_, ?_⟩
  · nlinarith
  · exact mul_le_mul_of_nonneg_right (show
      ((min n (a / d).toNat : ℕ) : ℤ) + 1 ≤ (n : ℤ) + 1 by omega) hd.le

end TransposeFollowup
