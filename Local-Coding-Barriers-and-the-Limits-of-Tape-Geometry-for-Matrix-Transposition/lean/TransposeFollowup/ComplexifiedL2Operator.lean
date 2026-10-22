import TransposeFollowup.ComplexL2Parts
import TransposeFollowup.ContractionCorrelation

/-! Reuse a real L2 operator on complex Fourier components by applying it
to the real and imaginary parts. Contraction and real-input correlation
are preserved without rebuilding the underlying Mobius action. -/
namespace TransposeFollowup
open Classical MeasureTheory
open RealMobius
set_option autoImplicit false

noncomputable def complexifyL2 (T : RealL2 →L[ℝ] RealL2) : ComplexL2 →L[ℝ] ComplexL2 :=
  (ofRealL2.comp T).comp realPartL2 + Complex.I • (ofRealL2.comp T).comp imagPartL2

theorem complexifyL2_apply (T : RealL2 →L[ℝ] RealL2) (f : ComplexL2) :
    complexifyL2 T f = ofRealL2 (T (realPartL2 f)) + Complex.I • ofRealL2 (T (imagPartL2 f)) := by
  simp [complexifyL2]

theorem complexifyL2_coe (T : RealL2 →L[ℝ] RealL2) (f : ComplexL2) :
    ⇑(complexifyL2 T f) =ᵐ[volume]
      (fun x => (T (realPartL2 f) x : ℂ) + Complex.I * (T (imagPartL2 f) x : ℂ)) := by
  rw [complexifyL2_apply]
  filter_upwards [Lp.coeFn_add (ofRealL2 (T (realPartL2 f))) (Complex.I • ofRealL2 (T (imagPartL2 f))),
    Lp.coeFn_smul Complex.I (ofRealL2 (T (imagPartL2 f))),
    ofRealL2_coe (T (realPartL2 f)), ofRealL2_coe (T (imagPartL2 f))] with x ha hs hr hi
  rw [ha]
  change ofRealL2 (T (realPartL2 f)) x + (Complex.I • ofRealL2 (T (imagPartL2 f))) x = _
  rw [hr, hs]
  change _ + Complex.I * ofRealL2 (T (imagPartL2 f)) x = _
  rw [hi]

theorem realPartL2_complexify (T : RealL2 →L[ℝ] RealL2) (f : ComplexL2) :
    realPartL2 (complexifyL2 T f) = T (realPartL2 f) := by
  rw [complexifyL2_apply, map_add, realPartL2_ofReal, realPartL2_I_smul, imagPartL2_ofReal]
  simp

theorem imagPartL2_complexify (T : RealL2 →L[ℝ] RealL2) (f : ComplexL2) :
    imagPartL2 (complexifyL2 T f) = T (imagPartL2 f) := by
  rw [complexifyL2_apply, map_add, imagPartL2_ofReal, imagPartL2_I_smul, realPartL2_ofReal]
  simp

theorem complexifyL2_ofReal (T : RealL2 →L[ℝ] RealL2) (f : RealL2) :
    complexifyL2 T (ofRealL2 f) = ofRealL2 (T f) := by
  rw [complexifyL2_apply, realPartL2_ofReal, imagPartL2_ofReal]
  simp

theorem complexifyL2_norm_le (T : RealL2 →L[ℝ] RealL2)
    (hT : ∀ f, ‖T f‖ ≤ ‖f‖) (f : ComplexL2) : ‖complexifyL2 T f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexL2_norm_sq_parts (complexifyL2 T f), realPartL2_complexify,
    imagPartL2_complexify, complexL2_norm_sq_parts f]
  exact add_le_add
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT _))
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hT _))

theorem complexifyL2_real_correlation (T : RealL2 →L[ℝ] RealL2) (f : RealL2) :
    inner ℝ (complexifyL2 T (ofRealL2 f)) (ofRealL2 f) = inner ℝ (T f) f := by
  rw [complexifyL2_ofReal, ofRealL2_inner]

theorem complexifyL2_symmetric (T : RealL2 →L[ℝ] RealL2)
    (hT : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g)) (f g : ComplexL2) :
    inner ℝ (complexifyL2 T f) g = inner ℝ f (complexifyL2 T g) := by
  simp only [complexL2_inner_parts, realPartL2_complexify, imagPartL2_complexify, hT]

namespace RealMobius

/-- The reused action has exactly the expected complex weighted pullback
formula, including the inverse convention and null-set transport. -/
theorem complexify_action_coe (g : Group) (f : ComplexL2) :
    ⇑(complexifyL2 (actionCLM g) f) =ᵐ[volume]
      (fun x => (|denom g⁻¹ x|⁻¹ : ℝ) • f (eval g⁻¹ x)) := by
  have hr := weightedPullback_ae_congr g⁻¹ (realPartL2_coe f)
  have hi := weightedPullback_ae_congr g⁻¹ (imagPartL2_coe f)
  filter_upwards [complexifyL2_coe (actionCLM g) f, unitaryAction_coe g (realPartL2 f),
    unitaryAction_coe g (imagPartL2 f), hr, hi] with x houter hreal himag hr hi
  rw [houter]
  change (unitaryAction g (realPartL2 f) x : ℂ) +
    Complex.I * (unitaryAction g (imagPartL2 f) x : ℂ) = _
  rw [hreal, himag, hr, hi]
  simp only [weightedPullback, Complex.ofReal_mul, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im (f (eval g⁻¹ x))]
  ring

noncomputable def complexAverage {c : ℕ} (G : Fin c → Group) : ComplexL2 →L[ℝ] ComplexL2 :=
  complexifyL2 (averageOperator G)

theorem complexAverage_norm_le {c : ℕ} (G : Fin c → Group) (hc : 0 < c) (f : ComplexL2) :
    ‖complexAverage G f‖ ≤ ‖f‖ :=
  complexifyL2_norm_le (averageOperator G) (averageOperator_norm_le G hc) f

theorem complexAverage_real_correlation {c : ℕ} (G : Fin c → Group) (f : RealL2) :
    inner ℝ (complexAverage G (ofRealL2 f)) (ofRealL2 f) = inner ℝ (averageOperator G f) f :=
  complexifyL2_real_correlation (averageOperator G) f

theorem complexAverage_symmetric {c : ℕ} (G : Fin c → Group) (f g : ComplexL2) :
    inner ℝ (complexAverage G f) g = inner ℝ f (complexAverage G g) :=
  complexifyL2_symmetric (averageOperator G) (averageOperator_symmetric G) f g

end RealMobius
end TransposeFollowup
