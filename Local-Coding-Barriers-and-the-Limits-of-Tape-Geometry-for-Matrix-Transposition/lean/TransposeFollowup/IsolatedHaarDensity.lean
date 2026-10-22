import TransposeFollowup.MobiusHaarKernelBounds

/-! A right-smoothed density is controlled by the largest atom when its
smoothing ball meets at most one point of an almost-everywhere support. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mobiusSmoothedDensity_le_of_isolated_support (μ : Measure Group)
    {S : Set Group} (hμ : ∀ᵐ a ∂μ, a ∈ S) {η : ℝ} {A : ℝ≥0∞}
    (hatom : ∀ a, μ {a} ≤ A)
    (hunique : ∀ {a b x : Group}, a ∈ S → b ∈ S →
      a⁻¹ * x ∈ mobiusIdentityBall η → b⁻¹ * x ∈ mobiusIdentityBall η → a = b)
    (x : Group) : mobiusSmoothedDensity μ η x ≤
      A * ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ := by
  let C := ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹
  by_cases he : ∃ a ∈ S, a⁻¹ * x ∈ mobiusIdentityBall η
  · obtain ⟨a, ha, hax⟩ := he
    have hi : ∀ᵐ b ∂μ, mobiusHaarKernelDensity η (b⁻¹ * x) =
        ({a} : Set Group).indicator (fun _ => C) b := by
      filter_upwards [hμ] with b hb
      by_cases hba : b = a
      · subst b
        simp [mobiusHaarKernelDensity, hax, C]
      · have hout : b⁻¹ * x ∉ mobiusIdentityBall η :=
          fun hbx => hba (hunique hb ha hbx hax)
        simp [mobiusHaarKernelDensity, hout, hba]
    calc
      _ = ∫⁻ b, ({a} : Set Group).indicator (fun _ => C) b ∂μ := lintegral_congr_ae hi
      _ = C * μ {a} := by
        rw [lintegral_indicator (measurableSet_singleton a), lintegral_const,
          Measure.restrict_apply_univ]
      _ ≤ C * A := by gcongr; exact hatom a
      _ = _ := mul_comm _ _
  · have hi : ∀ᵐ b ∂μ, mobiusHaarKernelDensity η (b⁻¹ * x) = 0 := by
      filter_upwards [hμ] with b hb
      have hout : b⁻¹ * x ∉ mobiusIdentityBall η := fun hbx => he ⟨b, hb, hbx⟩
      simp [mobiusHaarKernelDensity, hout]
    change (∫⁻ b, mobiusHaarKernelDensity η (b⁻¹ * x) ∂μ) ≤ _
    rw [lintegral_congr_ae hi, lintegral_zero]
    exact bot_le

end TransposeFollowup.RealMobius
