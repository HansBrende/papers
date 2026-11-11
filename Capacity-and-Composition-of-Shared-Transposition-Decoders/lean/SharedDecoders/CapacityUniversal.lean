import SharedDecoders.CapacityMeans
import SharedDecoders.CapacityIteration
import SharedDecoders.CapacityAveraging
import SharedDecoders.CapacityRunsShifts

/-! # Assembly of the universal two-class capacity bound -/

namespace SharedDecoders

open Module CapacityRuns
open scoped BigOperators

variable {d : ℕ} [NeZero d]

/-- Averaging the actual binary change counts and actual cyclic gcds. -/
theorem two_class_bound_of_step (p : ZMod d → Bool) (D b : ℝ) (hb : 0 < b)
    (hstep : ∀ s : ZMod d,
      D ≤ 9 / 16 * b * d ^ 2 + 3 / 16 * b * d * changeCount p s -
        1 / 32 * b * d * changeCount p (2 • s) + 3 / 4 * b * d * Nat.gcd d s.val) :
    D ≤ 41 / 64 * b * d ^ 2 + 5 / 3 * b * d * Real.sqrt d := by
  let a (r : ℕ) : ℝ := (∑ s : ZMod d, (changeCount p ((2 ^ r) • s) : ℝ)) / d
  let g (r : ℕ) : ℝ := (∑ s : ZMod d, (Nat.gcd d ((2 ^ r) • s).val : ℝ)) / d
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have ha : ∀ r, 0 ≤ a r := by intro r; dsimp [a]; positivity
  have ha₀ : a 0 ≤ (d : ℝ) / 2 := by
    simpa only [a, pow_zero, one_nsmul] using mean_changeCount_le p
  have hg : ∀ r, g r ≤ 2 * Real.sqrt d * (Real.sqrt 2) ^ r := fun r =>
    mean_doubled_gcd_zmod_le r
  have hmean (r : ℕ) :
      D ≤ 9 / 16 * b * (d : ℝ) ^ 2 + 3 / 16 * b * d * a r -
        1 / 32 * b * d * a (r + 1) + 3 / 4 * b * d * g r := by
    have hn (s : ZMod d) : 2 • ((2 ^ r) • s) = (2 ^ (r + 1)) • s := by
      rw [← mul_nsmul, pow_succ]
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun s _ => hstep ((2 ^ r) • s))
    have real_nsmul (n : ℕ) (x : ℝ) : n • x = (n : ℝ) * x := nsmul_eq_mul n x
    simp only [hn, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, ZMod.card,
      real_nsmul] at hs
    dsimp [a, g]
    have hden : (d : ℝ) ≠ 0 := ne_of_gt hd
    apply (le_of_mul_le_mul_left (a := (d : ℝ)) ?_ hd)
    field_simp
    nlinarith only [hs, hd]
  exact two_class_averaging a g D b d hb hd ha ha₀ hg hmean

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
  [FiniteDimensional F A]

/-- The actual three translate intersections, the actual run graphs, and the
binary run budget give the negative doubled-step term. -/
theorem IsSharedCode.binary_step_bound {p : ZMod d → Bool}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C) (s : ZMod d) :
    32 * finrank F C + d * finrank F A * changeCount p (2 • s) ≤
      18 * (d * d * finrank F A) + 6 * d * finrank F A * changeCount p s +
        24 * d * finrank F A * Nat.gcd d s.val := by
  have hh := h.eight_mul_finrank_le s (3 • s) (9 • s)
  have h₁ := Nat.mul_le_mul_left (d * finrank F A) (componentCount_first_shift p s)
  have h₂ := Nat.mul_le_mul_left (d * finrank F A) (componentCount_second_shift p s)
  have h₃ := Nat.mul_le_mul_left (d * finrank F A) (componentCount_third_shift p s)
  have hrun := Nat.mul_le_mul_left (d * finrank F A) (weighted_run_budget p s)
  rw [ZMod.card] at hrun
  have hdouble := congrArg (fun n => d * finrank F A * n) (changeCount_double p s)
  nlinarith only [hh, h₁, h₂, h₃, hrun, hdouble]

/-- The universal two-class bound for linear sources and arbitrary deterministic
decoders. An entry may be any finite-dimensional module, with arbitrary coupling. -/
theorem IsSharedCode.two_class_capacity_bound {p : ZMod d → Bool}
    {C : Submodule F (State d A)} (h : IsSharedCode F p C) :
    (finrank F C : ℝ) ≤ 41 / 64 * finrank F A * (d : ℝ) ^ 2 +
      5 / 3 * finrank F A * d * Real.sqrt d := by
  by_cases hb : finrank F A = 0
  · have hdim := Submodule.finrank_le C
    rw [finrank_state, hb, mul_zero] at hdim
    have hc : finrank F C = 0 := Nat.eq_zero_of_le_zero hdim
    simp [hc, hb]
  · apply two_class_bound_of_step p (finrank F C) (finrank F A)
      (by exact_mod_cast Nat.pos_of_ne_zero hb)
    intro s
    have hnat := h.binary_step_bound s
    have hr := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at hr
    nlinarith only [hr]

end SharedDecoders
