import TransposeFollowup.RealMobiusAverage

/-! Quantitative stability of quadratic correlation under a small L2 change.
The generic estimate needs contraction, without a symmetry hypothesis. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem abs_correlation_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (f g : E) :
    |inner ℝ (T f) f - inner ℝ (T g) g| ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := by
  have hid : inner ℝ (T f) f - inner ℝ (T g) g =
      inner ℝ (T (f - g)) f + inner ℝ (T g) (f - g) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ |inner ℝ (T (f - g)) f| + |inner ℝ (T g) (f - g)| := abs_add_le _ _
    _ ≤ ‖T (f - g)‖ * ‖f‖ + ‖T g‖ * ‖f - g‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖f - g‖ * ‖f‖ + ‖g‖ * ‖f - g‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (hT _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hT _) (norm_nonneg _))
    _ = _ := by ring

theorem normalized_correlation_loss_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖) {f g : E} (hf : ‖f‖ = 1)
    (δ : ℝ) (hδ : ‖f - g‖ ≤ δ) :
    |inner ℝ (T f) f - inner ℝ (T g) g| ≤ δ * (2 + δ) := by
  have hd0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hg : ‖g‖ ≤ 1 + δ := by
    calc
      _ ≤ ‖f‖ + ‖g - f‖ := by simpa using norm_add_le f (g - f)
      _ = 1 + ‖f - g‖ := by rw [hf, norm_sub_rev]
      _ ≤ 1 + δ := add_le_add le_rfl hδ
  calc
    _ ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := abs_correlation_sub_le T hT f g
    _ ≤ δ * (2 + δ) := by
      rw [hf]
      exact mul_le_mul hδ (by linarith) (by positivity) hd0

/-- If a future frequency decomposition removes at most 1/16 in L2 norm,
the correlation lower bound survives with an explicit margin above 1/4. -/
theorem correlation_survives_small_change {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖) {f g : E} (hf : ‖f‖ = 1)
    (hdiff : ‖f - g‖ ≤ 1 / 16) (hcorr : 1 / 2 ≤ inner ℝ (T f) f) :
    95 / 256 ≤ inner ℝ (T g) g := by
  have h := (abs_le.mp (normalized_correlation_loss_le T hT hf (1 / 16) hdiff)).2
  linarith

namespace RealMobius

theorem average_correlation_survives_small_change {c : ℕ} (G : Fin c → Group)
    (hc : 0 < c) {f g : RealL2} (hf : ‖f‖ = 1)
    (hdiff : ‖f - g‖ ≤ 1 / 16) (hcorr : 1 / 2 ≤ inner ℝ (averageOperator G f) f) :
    95 / 256 ≤ inner ℝ (averageOperator G g) g :=
  correlation_survives_small_change (averageOperator G) (averageOperator_norm_le G hc)
    hf hdiff hcorr

end RealMobius
end TransposeFollowup
