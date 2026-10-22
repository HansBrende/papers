import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Open grid cells and their overlap under a monotone map. A common
forward/inverse Lipschitz bound gives the endpoint spans needed for the
explicit residue coloring. Endpoint coincidences create no spurious edge. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

def InGridCell {n : ℕ} (i : Fin n) (x : ℝ) : Prop :=
  (i.val : ℝ) < n * x ∧ (n : ℝ) * x < i.val + 1

theorem gridCell_order {n : ℕ} {i j : Fin n} {x y : ℝ}
    (hi : InGridCell i x) (hj : InGridCell j y) (hij : i.val < j.val) : x < y := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  have hv : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  dsimp [InGridCell] at hi hj
  nlinarith

theorem gridCell_index_mono {n : ℕ} {i j : Fin n} {x y : ℝ}
    (hi : InGridCell i x) (hj : InGridCell j y) (hxy : x ≤ y) : i.val ≤ j.val := by
  by_contra hn
  have hyx := gridCell_order hj hi (show j.val < i.val by omega)
  linarith

theorem gridCell_distance {n : ℕ} {i : Fin n} {x y : ℝ}
    (hi : InGridCell i x) (hj : InGridCell i y) : |(n : ℝ) * x - n * y| < 1 := by
  dsimp [InGridCell] at hi hj
  rw [abs_lt]
  constructor <;> linarith

theorem scaled_abs_bound {x y u v B : ℝ} (h : |x - y| ≤ B * |u - v|) (n : ℕ) :
    |(n : ℝ) * x - n * y| ≤ B * |(n : ℝ) * u - n * v| := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    _ = (n : ℝ) * |x - y| := by rw [← mul_sub, abs_mul, abs_of_nonneg hn]
    _ ≤ (n : ℝ) * (B * |u - v|) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    _ = _ := by rw [← mul_sub, abs_mul, abs_of_nonneg hn]; ring

structure BoundedMonotoneMap (B : ℕ) where
  domain : Set ℝ
  map : ℝ → ℝ
  strictMono : StrictMonoOn map domain
  forward : ∀ x ∈ domain, ∀ y ∈ domain, |map x - map y| ≤ B * |x - y|
  backward : ∀ x ∈ domain, ∀ y ∈ domain, |x - y| ≤ B * |map x - map y|

namespace BoundedMonotoneMap

variable {B : ℕ} (F : BoundedMonotoneMap B)

def Overlap {n : ℕ} (i j : Fin n) : Prop :=
  ∃ x ∈ F.domain, InGridCell i x ∧ InGridCell j (F.map x)

theorem overlap_order {n : ℕ} {i j i' j' : Fin n}
    (h : F.Overlap i j) (h' : F.Overlap i' j') (hi : i.val < i'.val) : j.val ≤ j'.val := by
  obtain ⟨x, hx, hxi, hxj⟩ := h
  obtain ⟨y, hy, hyi, hyj⟩ := h'
  have hxy := gridCell_order hxi hyi hi
  exact gridCell_index_mono hxj hyj (F.strictMono hx hy hxy).le

theorem overlap_row_span {n : ℕ} {i j j' : Fin n}
    (h : F.Overlap i j) (h' : F.Overlap i j') : j.val < j'.val + (B + 1) := by
  obtain ⟨x, hx, hxi, hxj⟩ := h
  obtain ⟨y, hy, hyi, hyj⟩ := h'
  have hd := gridCell_distance hxi hyi
  have hs := scaled_abs_bound (F.forward x hx y hy) n
  have hb : |(n : ℝ) * F.map x - n * F.map y| ≤ B :=
    hs.trans (mul_le_of_le_one_right (Nat.cast_nonneg B) hd.le)
  have hdiff := le_abs_self ((n : ℝ) * F.map x - n * F.map y)
  have hreal : (j.val : ℝ) < (j'.val : ℝ) + ((B + 1 : ℕ) : ℝ) := by
    dsimp [InGridCell] at hxj hyj
    push_cast
    linarith
  exact_mod_cast hreal

theorem overlap_column_span {n : ℕ} {i i' j : Fin n}
    (h : F.Overlap i j) (h' : F.Overlap i' j) : i.val < i'.val + (B + 1) := by
  obtain ⟨x, hx, hxi, hxj⟩ := h
  obtain ⟨y, hy, hyi, hyj⟩ := h'
  have hd := gridCell_distance hxj hyj
  have hs := scaled_abs_bound (F.backward x hx y hy) n
  have hb : |(n : ℝ) * x - n * y| ≤ B :=
    hs.trans (mul_le_of_le_one_right (Nat.cast_nonneg B) hd.le)
  have hdiff := le_abs_self ((n : ℝ) * x - n * y)
  have hreal : (i.val : ℝ) < (i'.val : ℝ) + ((B + 1 : ℕ) : ℝ) := by
    dsimp [InGridCell] at hxi hyi
    push_cast
    linarith
  exact_mod_cast hreal

end BoundedMonotoneMap
end TransposeFollowup
