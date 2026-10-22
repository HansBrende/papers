import TransposeFollowup.RationalMobius

/-! A computable integer distortion bound for a fixed rational Mobius map.
It is independent of the grid size, and controls both the map and its inverse. -/

namespace TransposeFollowup
namespace RationalMobius

open Set
set_option autoImplicit false

variable (F : RationalMobius)

def distortion : ℕ :=
  ⌈max (F.delta / (F.lowerDenom * F.lowerDenom))
    ((F.upperDenom * F.upperDenom) / F.delta)⌉₊

theorem distortion_forward_bound :
    (F.delta : ℝ) ≤ F.distortion * ((F.lowerDenom : ℝ) * F.lowerDenom) := by
  have hq : F.delta / (F.lowerDenom * F.lowerDenom) ≤ (F.distortion : ℚ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hr : (F.delta : ℝ) / ((F.lowerDenom : ℝ) * F.lowerDenom) ≤ F.distortion := by
    exact_mod_cast hq
  exact (div_le_iff₀ (mul_pos F.lowerDenom_pos F.lowerDenom_pos)).mp hr

theorem distortion_backward_bound :
    (F.upperDenom : ℝ) * F.upperDenom ≤ F.distortion * (F.delta : ℝ) := by
  have hq : (F.upperDenom * F.upperDenom) / F.delta ≤ (F.distortion : ℚ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hr : ((F.upperDenom : ℝ) * F.upperDenom) / F.delta ≤ F.distortion := by
    exact_mod_cast hq
  exact (div_le_iff₀ F.delta_pos).mp hr

theorem forward_bound {x y : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi)
    (hy : y ∈ Icc (F.lo : ℝ) F.hi) :
    |F.eval x - F.eval y| ≤ F.distortion * |x - y| := by
  have hprod : (F.lowerDenom : ℝ) * F.lowerDenom ≤ F.denom x * F.denom y :=
    mul_le_mul (F.denom_bounds hx).1 (F.denom_bounds hy).1 F.lowerDenom_pos.le (F.denom_pos hx).le
  have hcross := F.abs_difference_mul hx hy
  have h1 := mul_le_mul_of_nonneg_left hprod (abs_nonneg (F.eval x - F.eval y))
  have h2 := mul_le_mul_of_nonneg_right F.distortion_forward_bound (abs_nonneg (x - y))
  have hsmall :
      |F.eval x - F.eval y| * ((F.lowerDenom : ℝ) * F.lowerDenom) ≤
      (F.distortion * |x - y|) * ((F.lowerDenom : ℝ) * F.lowerDenom) := by
    nlinarith only [hcross, h1, h2]
  exact (mul_le_mul_iff_left₀ (mul_pos F.lowerDenom_pos F.lowerDenom_pos)).mp hsmall

theorem backward_bound {x y : ℝ} (hx : x ∈ Icc (F.lo : ℝ) F.hi)
    (hy : y ∈ Icc (F.lo : ℝ) F.hi) :
    |x - y| ≤ F.distortion * |F.eval x - F.eval y| := by
  have hu : (0 : ℝ) ≤ F.upperDenom :=
    (F.denom_pos hx).le.trans (F.denom_bounds hx).2
  have hprod : F.denom x * F.denom y ≤ (F.upperDenom : ℝ) * F.upperDenom :=
    mul_le_mul (F.denom_bounds hx).2 (F.denom_bounds hy).2 (F.denom_pos hy).le hu
  have hcross := F.abs_difference_mul hx hy
  have h1 := mul_le_mul_of_nonneg_left hprod (abs_nonneg (F.eval x - F.eval y))
  have h2 := mul_le_mul_of_nonneg_right F.distortion_backward_bound
    (abs_nonneg (F.eval x - F.eval y))
  have hsmall : |x - y| * (F.delta : ℝ) ≤
      (F.distortion * |F.eval x - F.eval y|) * (F.delta : ℝ) := by
    nlinarith only [hcross, h1, h2]
  exact (mul_le_mul_iff_left₀ F.delta_pos).mp hsmall

noncomputable def bounded : BoundedMonotoneMap F.distortion where
  domain := Ioo (F.lo : ℝ) F.hi
  map := F.eval
  strictMono := F.strictMonoOn_eval.mono Ioo_subset_Icc_self
  forward _x hx _y hy := F.forward_bound (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
  backward _x hx _y hy := F.backward_bound (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)

end RationalMobius
end TransposeFollowup
