import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-! A two-point remainder estimate for an ordered triple product near
the identity. The bound works without a norm-one identity assumption. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem triple_product_linear_remainder {K : Type*} [NormedRing K]
    (u v : Fin 3 → K) {r Y : ℝ} (hI : ‖(1 : K)‖ ≤ 2)
    (hr1 : r ≤ 1)
    (hu : ∀ i, ‖u i - 1‖ ≤ r) (hv : ∀ i, ‖v i - 1‖ ≤ r)
    (he : ∀ i, ‖u i - v i‖ ≤ Y) :
    ‖u 0 * u 1 * u 2 - v 0 * v 1 * v 2 -
      ((u 0 - v 0) + (u 1 - v 1) + (u 2 - v 2))‖ ≤ 12 * r * Y := by
  have hn (x : K) (hx : ‖x - 1‖ ≤ r) : ‖x‖ ≤ 3 := by
    have hh : ‖x‖ ≤ ‖x - 1‖ + ‖(1 : K)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - 1) (1 : K)
    linarith
  have hp (x y : K) (hx : ‖x - 1‖ ≤ r) (hy : ‖y - 1‖ ≤ r) :
      ‖x * y - 1‖ ≤ 4 * r := by
    rw [show x * y - 1 = (x - 1) * y + (y - 1) by noncomm_ring]
    have hh := norm_mul_le_of_le hx (hn y hy)
    have ha := norm_add_le ((x - 1) * y) (y - 1)
    linarith
  let A := (u 0 - v 0) * (u 1 * u 2 - 1)
  let B := (v 0 - 1) * (u 1 - v 1) * u 2
  let C := (u 1 - v 1) * (u 2 - 1)
  let D := (v 0 * v 1 - 1) * (u 2 - v 2)
  have hA : ‖A‖ ≤ Y * (4 * r) := norm_mul_le_of_le (he 0) (hp _ _ (hu 1) (hu 2))
  have hB : ‖B‖ ≤ (r * Y) * 3 :=
    norm_mul_le_of_le (norm_mul_le_of_le (hv 0) (he 1)) (hn _ (hu 2))
  have hC : ‖C‖ ≤ Y * r := norm_mul_le_of_le (he 1) (hu 2)
  have hD : ‖D‖ ≤ (4 * r) * Y := norm_mul_le_of_le (hp _ _ (hv 0) (hv 1)) (he 2)
  have hid : u 0 * u 1 * u 2 - v 0 * v 1 * v 2 -
      ((u 0 - v 0) + (u 1 - v 1) + (u 2 - v 2)) = A + B + C + D := by
    dsimp only [A, B, C, D]
    noncomm_ring
  rw [hid]
  linarith only [norm_add_le A B, norm_add_le (A + B) C,
    norm_add_le (A + B + C) D, hA, hB, hC, hD]

end TransposeFollowup
