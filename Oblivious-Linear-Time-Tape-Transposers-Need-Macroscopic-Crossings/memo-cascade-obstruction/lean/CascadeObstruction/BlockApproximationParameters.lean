import CascadeObstruction.BlockApproximation
import CascadeObstruction.RasterRegularity

/-! Compact normalized ramp parameters for a finite physical block list. -/

namespace CascadeObstruction.C5

open Set TransposeFollowup.AffineMotion
open scoped BigOperators

set_option autoImplicit false

theorem blocksDuration_take_le (bs : List Block) (n : ℕ) :
    blocksDuration (bs.take n) ≤ blocksDuration bs := by
  induction bs generalizing n with
  | nil => simp [blocksDuration]
  | cons b bs ih =>
    cases n with
    | zero => simp [blocksDuration]
    | succ n => simpa [blocksDuration] using Nat.add_le_add_left (ih n) b.duration

theorem get_duration_le (bs : List Block) (j : Fin bs.length) :
    (bs.get j).duration ≤ blocksDuration bs := by
  induction bs with
  | nil => exact Fin.elim0 j
  | cons b bs ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [blocksDuration]
    · exact (ih i).trans (by simp [blocksDuration])

theorem blockCurveFrom_eq_sum (bs : List Block) (h : Fin 3) (a : ℕ) (t : ℝ) :
    blockCurveFrom bs h a t =
      ∑ j : Fin bs.length,
        (bs.get j).ramp h (a + blocksDuration (bs.take j.val)) t := by
  induction bs generalizing a with
  | nil => simp [blockCurveFrom]
  | cons b bs ih =>
    simp only [List.length_cons]
    rw [blockCurveFrom, Fin.sum_univ_succ, ih]
    simp [blocksDuration, Nat.add_assoc]

theorem clippedRamp_normalize (D A V s : ℝ) (hV : 0 < V) :
    clippedRamp (D / V) (A / V) 1 s = clippedRamp D A 1 (V * s) / V := by
  have he : (V * s - A) / V = s - A / V := by
    field_simp
  simp only [clippedRamp, div_one]
  calc
    min (max (s - A / V) 0) (D / V) =
        min (max ((V * s - A) / V) (0 / V)) (D / V) := by rw [he, zero_div]
    _ = min (max (V * s - A) 0) D / V := by
      rw [max_div_div_right hV.le, min_div_div_right hV.le]

noncomputable def blockParameters (bs : List Block) (h : Fin 3)
    {a V : ℝ} (hV : 0 < V) (hb : (blocksDuration bs : ℝ) ≤ a * V) :
    Fin bs.length → Raster.Parameters a := fun j =>
  (⟨(bs.get j).slope h, (bs.get j).slope_bounds h⟩,
    ⟨(blocksDuration (bs.take j.val) : ℝ) / V,
      div_nonneg (by positivity) hV.le,
      (div_le_iff₀ hV).2 (le_trans
        (show (blocksDuration (bs.take j.val) : ℝ) ≤ blocksDuration bs from by
          exact_mod_cast blocksDuration_take_le bs j.val) hb)⟩,
    ⟨((bs.get j).duration : ℝ) / V,
      div_nonneg (by positivity) hV.le,
      (div_le_iff₀ hV).2 (le_trans
        (show ((bs.get j).duration : ℝ) ≤ blocksDuration bs from by
          exact_mod_cast get_duration_le bs j) hb)⟩)

theorem blockParameters_curve (bs : List Block) (h : Fin 3)
    {a V : ℝ} (hV : 0 < V) (hb : (blocksDuration bs : ℝ) ≤ a * V) (s : ℝ) :
    Raster.curve (blockParameters bs h hV hb) s = blockCurveFrom bs h 0 (V * s) / V := by
  rw [blockCurveFrom_eq_sum, Finset.sum_div]
  unfold Raster.curve
  apply Finset.sum_congr rfl
  intro j _
  simp only [Raster.ramp, blockParameters, Block.ramp, Nat.zero_add]
  rw [clippedRamp_normalize _ _ _ _ hV]
  ring

theorem blockParameters_error (bs : List Block) (h : Fin 3)
    {a V : ℝ} (hV : 0 < V) (hb : (blocksDuration bs : ℝ) ≤ a * V) (s : ℝ) :
    dist (Raster.curve (blockParameters bs h hV hb) s)
      ((position (expand bs) h ⌊V * s⌋₊ : ℝ) / V) ≤ 2 * (bs.length : ℝ) / V := by
  rw [blockParameters_curve, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hV,
    abs_sub_comm]
  exact div_le_div_of_nonneg_right (position_expand_curve_error bs h (V * s)) hV.le

end CascadeObstruction.C5
