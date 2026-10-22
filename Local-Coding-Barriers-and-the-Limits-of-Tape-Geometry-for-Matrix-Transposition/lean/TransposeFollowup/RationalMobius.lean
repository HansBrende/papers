import TransposeFollowup.IntervalOverlap

/-! Rational increasing Mobius maps on a nondegenerate rational interval.
Positive endpoint denominators imply continuity and strict increase on the
whole closed interval. Rational evaluation is an executable definition. -/

namespace TransposeFollowup

open Set
set_option autoImplicit false

structure RationalMobius where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  lo : ℚ
  hi : ℚ
  interval_nonempty : lo < hi
  determinant_pos : 0 < a * d - b * c
  denominator_lo_pos : 0 < c * lo + d
  denominator_hi_pos : 0 < c * hi + d

namespace RationalMobius

variable (F : RationalMobius)

def evalQ (x : ℚ) : ℚ := (F.a * x + F.b) / (F.c * x + F.d)

noncomputable def eval (x : ℝ) : ℝ := ((F.a : ℝ) * x + F.b) / ((F.c : ℝ) * x + F.d)

noncomputable def denom (x : ℝ) : ℝ := (F.c : ℝ) * x + F.d

def delta : ℚ := F.a * F.d - F.b * F.c

def lowerDenom : ℚ := min (F.c * F.lo + F.d) (F.c * F.hi + F.d)

def upperDenom : ℚ := max (F.c * F.lo + F.d) (F.c * F.hi + F.d)

theorem eval_cast (x : ℚ) : F.eval (x : ℝ) = (F.evalQ x : ℝ) := by
  simp only [eval, evalQ, Rat.cast_div, Rat.cast_add, Rat.cast_mul]

theorem delta_pos : (0 : ℝ) < F.delta := by exact_mod_cast F.determinant_pos

theorem lowerDenom_pos : (0 : ℝ) < F.lowerDenom := by
  exact_mod_cast (lt_min F.denominator_lo_pos F.denominator_hi_pos)

theorem denom_bounds {x : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi) :
    (F.lowerDenom : ℝ) ≤ F.denom x ∧ F.denom x ≤ F.upperDenom := by
  simp only [lowerDenom, upperDenom, Rat.cast_min, Rat.cast_max,
    Rat.cast_add, Rat.cast_mul]
  by_cases hc : (0 : ℝ) ≤ F.c
  · have hlo : (F.c : ℝ) * F.lo + F.d ≤ F.denom x := by dsimp [denom]; nlinarith [hx.1]
    have hhi : F.denom x ≤ (F.c : ℝ) * F.hi + F.d := by dsimp [denom]; nlinarith [hx.2]
    exact ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_right _ _)⟩
  · have hlo : (F.c : ℝ) * F.hi + F.d ≤ F.denom x := by dsimp [denom]; nlinarith [hx.2]
    have hhi : F.denom x ≤ (F.c : ℝ) * F.lo + F.d := by dsimp [denom]; nlinarith [hx.1]
    exact ⟨(min_le_right _ _).trans hlo, hhi.trans (le_max_left _ _)⟩

theorem denom_pos {x : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi) : 0 < F.denom x :=
  F.lowerDenom_pos.trans_le (F.denom_bounds hx).1

theorem continuousOn_eval : ContinuousOn F.eval (Icc (F.lo : ℝ) F.hi) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  exact fun x hx => (F.denom_pos hx).ne'

theorem difference_mul {x y : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi)
    (hy : y ∈ Icc (F.lo : ℝ) F.hi) :
    (F.eval x - F.eval y) * (F.denom x * F.denom y) = (F.delta : ℝ) * (x - y) := by
  have hdx : F.eval x * F.denom x = (F.a : ℝ) * x + F.b :=
    div_mul_cancel₀ _ (F.denom_pos hx).ne'
  have hdy : F.eval y * F.denom y = (F.a : ℝ) * y + F.b :=
    div_mul_cancel₀ _ (F.denom_pos hy).ne'
  calc
    _ = (F.eval x * F.denom x) * F.denom y -
        (F.eval y * F.denom y) * F.denom x := by ring
    _ = ((F.a : ℝ) * x + F.b) * F.denom y -
        ((F.a : ℝ) * y + F.b) * F.denom x := by rw [hdx, hdy]
    _ = _ := by dsimp [denom, delta]; push_cast; ring

theorem strictMonoOn_eval : StrictMonoOn F.eval (Icc (F.lo : ℝ) F.hi) := by
  intro x hx y hy hxy
  have hd := F.difference_mul hy hx
  have hp := mul_pos F.delta_pos (sub_pos.mpr hxy)
  have hden := mul_pos (F.denom_pos hy) (F.denom_pos hx)
  have hf : 0 < F.eval y - F.eval x := (mul_pos_iff_of_pos_right hden).mp (hd.symm ▸ hp)
  exact sub_pos.mp hf

theorem abs_difference_mul {x y : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi)
    (hy : y ∈ Icc (F.lo : ℝ) F.hi) :
    |F.eval x - F.eval y| * (F.denom x * F.denom y) = (F.delta : ℝ) * |x - y| := by
  have h := congrArg abs (F.difference_mul hx hy)
  simpa only [abs_mul, abs_of_pos (F.denom_pos hx), abs_of_pos (F.denom_pos hy),
    abs_of_pos F.delta_pos] using h

end RationalMobius
end TransposeFollowup
