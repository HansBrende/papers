import TransposeFollowup.XorPathCycleBound

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

theorem r1916_original_linear_ball_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G)
    (hballs : ∀ ell, 1 ≤ ell → ∀ i, (nearVertices G ell i).card ≤ 2 * ell - 1) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * Real.sqrt (8 * (n : ℝ))  := by
  have hstrong := C.linear_ball_broadcast_lower_bound hc G hG hballs hn
  have herror := linear_ball_error_le_sqrt n hn
  have hmul := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ (b : ℝ) * n)
  linarith

#print axioms r1916_original_linear_ball_broadcast_lower_bound

theorem r1916_original_cycle_embedding_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) {m : ℕ} [NeZero m]
    (f : G →g SimpleGraph.cycleGraph m) (hf : Function.Injective f) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * Real.sqrt (8 * (n : ℝ))  := by
  have hstrong := C.cycle_embedding_broadcast_lower_bound hc G hG f hf hn
  have herror := linear_ball_error_le_sqrt n hn
  have hmul := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ (b : ℝ) * n)
  linarith

#print axioms r1916_original_cycle_embedding_broadcast_lower_bound

theorem r1916_original_subcycle_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (hcycle : G ≤ SimpleGraph.cycleGraph n) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * Real.sqrt (8 * (n : ℝ))  := by
  have hstrong := C.subcycle_broadcast_lower_bound hc G hG hcycle hn
  have herror := linear_ball_error_le_sqrt n hn
  have hmul := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ (b : ℝ) * n)
  linarith

#print axioms r1916_original_subcycle_broadcast_lower_bound

theorem r1916_original_cycle_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.cycleGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * Real.sqrt (8 * (n : ℝ))  := by
  have hstrong := C.cycle_broadcast_lower_bound hc hG hn
  have herror := linear_ball_error_le_sqrt n hn
  have hmul := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ (b : ℝ) * n)
  linarith

#print axioms r1916_original_cycle_broadcast_lower_bound

theorem r1916_original_path_broadcast_lower_bound (hc : C.Correct)
    (hG : C.LocalTo (SimpleGraph.pathGraph n)) (hn : 0 < n) :
    (B : ℝ) ≥ (n * n * b : ℕ) - (b : ℝ) * n * Real.sqrt (8 * (n : ℝ))  := by
  have hstrong := C.path_broadcast_lower_bound hc hG hn
  have herror := linear_ball_error_le_sqrt n hn
  have hmul := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ (b : ℝ) * n)
  linarith

#print axioms r1916_original_path_broadcast_lower_bound

end RecodedXorCode
end TransposeFollowup
