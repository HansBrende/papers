import TransposeFollowup.SmoothedWalkAutocorrelation

/-! The autocorrelation average is A* A for the actual representation
average A. A large action survives passage to the symmetric measure. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
set_option autoImplicit false

theorem complexPullbackL2_inner_inverse (g : Group) (f h : ComplexL2) :
    inner ℝ (complexPullbackL2 g f) h = inner ℝ f (complexPullbackL2 g⁻¹ h) := by
  let A : ComplexL2 →ₗᵢ[ℝ] ComplexL2 :=
    { toLinearMap := (complexPullbackL2 g).toLinearMap
      norm_map' := complexPullbackL2_norm g }
  have he : complexPullbackL2 g (complexPullbackL2 g⁻¹ h) = h := by
    rw [← complexPullbackL2_mul, inv_mul_cancel, complexPullbackL2_one]
  calc
    _ = inner ℝ (A f) (A (complexPullbackL2 g⁻¹ h)) := by change _ = inner ℝ _ (complexPullbackL2 g _); rw [he]; rfl
    _ = _ := A.inner_map_map _ _

variable [MeasurableSpace Group] [BorelSpace Group]

theorem groupActionAverage_inv_integral (μ : Measure Group) (f : ComplexL2) :
    groupActionAverage μ.inv f = ∫ g, complexPullbackL2 g f ∂μ := by
  unfold groupActionAverage
  rw [Measure.inv_def, integral_map measurable_inv.aemeasurable
    (complexPullbackL2_inverse_continuous f).aestronglyMeasurable]
  simp only [inv_inv]

theorem groupActionAverage_adjoint_inner (μ : Measure Group) [IsFiniteMeasure μ] (f h : ComplexL2) :
    inner ℝ (groupActionAverage μ f) h = inner ℝ f (groupActionAverage μ.inv h) := by
  have hi : Integrable (fun g : Group => complexPullbackL2 g h) μ := by
    apply (integrable_const ‖h‖ : Integrable (fun _ : Group => ‖h‖) μ).mono'
      (complexPullbackL2_continuous h).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun g => (complexPullbackL2_norm g h).le)
  calc
    _ = ∫ g, inner ℝ h (complexPullbackL2 g⁻¹ f) ∂μ := by
      rw [real_inner_comm, groupActionAverage, integral_inner (integrable_complexPullbackL2_inverse μ f)]
    _ = ∫ g, inner ℝ f (complexPullbackL2 g h) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [real_inner_comm, complexPullbackL2_inner_inverse, inv_inv]
    _ = _ := by rw [integral_inner hi, groupActionAverage_inv_integral]

theorem groupActionAverage_autocorrelation_inner (μ : Measure Group) [IsFiniteMeasure μ] (f : ComplexL2) :
    inner ℝ f (groupActionAverage (μ.inv ∗ₘ μ) f) = ‖groupActionAverage μ f‖ ^ 2 := by
  have : IsFiniteMeasure μ.inv := by change IsFiniteMeasure (Measure.map Inv.inv μ); infer_instance
  rw [groupActionAverage_mconv, ← groupActionAverage_adjoint_inner, real_inner_self_eq_norm_sq]

theorem groupActionAverage_autocorrelation_norm_lower (μ : Measure Group) [IsFiniteMeasure μ]
    (f : ComplexL2) (hf : ‖f‖ = 1) :
    ‖groupActionAverage μ f‖ ^ 2 ≤ ‖groupActionAverage (μ.inv ∗ₘ μ) f‖ := by
  rw [← groupActionAverage_autocorrelation_inner]
  simpa only [hf, one_mul] using real_inner_le_norm f (groupActionAverage (μ.inv ∗ₘ μ) f)

theorem groupActionAverage_autocorrelation_symmetric (μ : Measure Group) [IsFiniteMeasure μ]
    (f h : ComplexL2) :
    inner ℝ (groupActionAverage (μ.inv ∗ₘ μ) f) h =
      inner ℝ f (groupActionAverage (μ.inv ∗ₘ μ) h) := by
  have : IsFiniteMeasure μ.inv := by change IsFiniteMeasure (Measure.map Inv.inv μ); infer_instance
  rw [groupActionAverage_adjoint_inner, inv_autocorrelation]

end TransposeFollowup.RealMobius
