import CascadeObstruction.C5Trace
import TransposeFollowup.ClippedAffineRamps

/-! Uniform real-time interpolation for finite lists of straight and
alternating unit-move blocks. Each block costs at most two cells of error. -/

namespace CascadeObstruction.C5

open Transpose TransposeFollowup.AffineMotion

set_option autoImplicit false

theorem dirValue_bounds (d : Dir) : -1 ≤ dirValue d ∧ dirValue d ≤ 1 := by
  cases d <;> simp [dirValue, Dir.shift]

theorem Tick.move_bounds (x : Tick) (h : Fin 3) : -1 ≤ x.move h ∧ x.move h ≤ 1 := by
  unfold Tick.move
  split_ifs <;> exact dirValue_bounds _

theorem Tick.move_real_bounds (x : Tick) (h : Fin 3) :
    (-1 : ℝ) ≤ x.move h ∧ (x.move h : ℝ) ≤ 1 := by
  exact_mod_cast x.move_bounds h

noncomputable def Block.slope : Block → Fin 3 → ℝ
  | .straight _ x, h => x.move h
  | .pairs _ x y, h => ((x.move h : ℝ) + y.move h) / 2

theorem Block.slope_bounds (b : Block) (h : Fin 3) :
    -1 ≤ b.slope h ∧ b.slope h ≤ 1 := by
  cases b with
  | straight n x => exact x.move_real_bounds h
  | pairs n x y =>
    have hx := x.move_real_bounds h
    have hy := y.move_real_bounds h
    dsimp [Block.slope]
    constructor <;> linarith

theorem Block.abs_slope_le (b : Block) (h : Fin 3) : |b.slope h| ≤ 1 :=
  abs_le.mpr (b.slope_bounds h)

/-- Integer-time interpolation loses at most the unpaired first tick. -/
theorem Block.displacement_error (b : Block) (h : Fin 3) (u : ℕ) :
    |(b.displacement h u : ℝ) - b.slope h * (min u b.duration : ℕ)| ≤ 1 := by
  cases b with
  | straight n x =>
    simp [Block.displacement, Block.slope, Block.duration, mul_comm]
  | pairs n x y =>
    have hs : min ((u + 1) / 2) n + min (u / 2) n = min u (2 * n) := by omega
    have he : min ((u + 1) / 2) n = min (u / 2) n ∨
        min ((u + 1) / 2) n = min (u / 2) n + 1 := by omega
    have hx := x.move_real_bounds h
    have hy := y.move_real_bounds h
    simp only [Block.displacement, Block.slope, Block.duration, Int.cast_add,
      Int.cast_mul, Int.cast_natCast]
    rw [← hs]
    rcases he with he | he
    · rw [he]
      push_cast
      ring_nf
      norm_num
    · rw [he]
      push_cast
      apply abs_le.mpr
      constructor <;> nlinarith

noncomputable def Block.ramp (b : Block) (h : Fin 3) (a : ℕ) (t : ℝ) : ℝ :=
  b.slope h * clippedRamp b.duration a 1 t

theorem Block.ramp_error (b : Block) (h : Fin 3) (a : ℕ) (t : ℝ) :
    |(b.displacement h (⌊t⌋₊ - a) : ℝ) - b.ramp h a t| ≤ 2 := by
  have hi := b.displacement_error h (⌊t⌋₊ - a)
  have hr := clippedRamp_sample_error b.duration a 1 t
  norm_num only [Nat.div_one, Nat.cast_one] at hr
  have hm : |b.slope h * (min (⌊t⌋₊ - a) b.duration : ℕ) -
      b.slope h * clippedRamp b.duration a 1 t| ≤ 1 := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (b.abs_slope_le h) hr (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  unfold Block.ramp
  exact (abs_sub_le _ _ _).trans (by linarith)

noncomputable def blockCurveFrom : List Block → Fin 3 → ℕ → ℝ → ℝ
  | [], _, _, _ => 0
  | b :: bs, h, a, t => b.ramp h a t + blockCurveFrom bs h (a + b.duration) t

theorem blockCurveFrom_error (bs : List Block) (h : Fin 3) (a : ℕ) (t : ℝ) :
    |(blockPosition bs h (⌊t⌋₊ - a) : ℝ) - blockCurveFrom bs h a t| ≤
      2 * (bs.length : ℝ) := by
  induction bs generalizing a with
  | nil => simp [blockPosition, blockCurveFrom]
  | cons b bs ih =>
    have hb := b.ramp_error h a t
    have ht := ih (a + b.duration)
    simp only [blockPosition, blockCurveFrom, Int.cast_add, List.length_cons, Nat.cast_add,
      Nat.cast_one, Nat.sub_sub] at *
    calc
      _ = |((b.displacement h (⌊t⌋₊ - a) : ℝ) - b.ramp h a t) +
          ((blockPosition bs h (⌊t⌋₊ - (a + b.duration)) : ℝ) -
            blockCurveFrom bs h (a + b.duration) t)| := by congr 1; ring
      _ ≤ |(b.displacement h (⌊t⌋₊ - a) : ℝ) - b.ramp h a t| +
          |(blockPosition bs h (⌊t⌋₊ - (a + b.duration)) : ℝ) -
            blockCurveFrom bs h (a + b.duration) t| := abs_add_le _ _
      _ ≤ 2 * ((bs.length : ℝ) + 1) := by linarith

theorem position_expand_curve_error (bs : List Block) (h : Fin 3) (t : ℝ) :
    |(position (expand bs) h ⌊t⌋₊ : ℝ) - blockCurveFrom bs h 0 t| ≤
      2 * (bs.length : ℝ) := by
  simpa only [position_expand, Nat.sub_zero] using blockCurveFrom_error bs h 0 t

end CascadeObstruction.C5
