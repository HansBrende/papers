import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic

/-! A probability mixture with positive mass has a translate retaining
half that mass, with its translating element in any almost-everywhere
support set. No attainment of an infinite supremum is assumed. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem exists_half_le_of_lintegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {T : Set α}
    (hT : ∀ᵐ a ∂μ, a ∈ T) {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤)
    (hm : p ≤ ∫⁻ a, f a ∂μ) : ∃ a ∈ T, p ≤ 2 * f a := by
  by_contra! hnone
  have hb : (∫⁻ a, f a ∂μ) ≤ p / 2 := by
    apply lintegral_le_const
    filter_upwards [hT] with a ha
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    simpa only [mul_comm] using (hnone a ha).le
  exact (not_lt_of_ge (hm.trans hb)) (ENNReal.half_lt_self hp.ne' hpt)

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem mconv_apply_eq_lintegral_left_preimage (μ ν : Measure G) [SFinite ν]
    {S : Set G} (hS : MeasurableSet S) :
    (μ ∗ₘ ν) S = ∫⁻ a, ν ((a * ·) ⁻¹' S) ∂μ := by
  rw [← lintegral_indicator_one hS, Measure.lintegral_mconv (measurable_one.indicator hS)]
  apply lintegral_congr
  intro a
  change (∫⁻ b, ((a * ·) ⁻¹' S).indicator (1 : G → ℝ≥0∞) b ∂ν) = _
  exact lintegral_indicator_one (hS.preimage (by fun_prop))

theorem exists_translate_mass_of_mconv (μ ν : Measure G) [IsProbabilityMeasure μ] [SFinite ν]
    {S T : Set G} (hS : MeasurableSet S) (hT : ∀ᵐ a ∂μ, a ∈ T)
    {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤) (hm : p ≤ (μ ∗ₘ ν) S) :
    ∃ a ∈ T, p ≤ 2 * ν ((a * ·) ⁻¹' S) := by
  apply exists_half_le_of_lintegral μ hT hp hpt
  rwa [← mconv_apply_eq_lintegral_left_preimage μ ν hS]

theorem mconv_apply_eq_lintegral_right_preimage (μ ν : Measure G) [SFinite μ] [SFinite ν]
    {S : Set G} (hS : MeasurableSet S) :
    (μ ∗ₘ ν) S = ∫⁻ b, μ ((· * b) ⁻¹' S) ∂ν := by
  rw [← lintegral_indicator_one hS, Measure.lintegral_mconv (measurable_one.indicator hS),
    lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro b
  change (∫⁻ a, ((· * b) ⁻¹' S).indicator (1 : G → ℝ≥0∞) a ∂μ) = _
  exact lintegral_indicator_one (hS.preimage (by fun_prop))

theorem exists_right_slice_mass_of_mconv (μ ν : Measure G) [SFinite μ] [IsProbabilityMeasure ν]
    {S T : Set G} (hS : MeasurableSet S) (hT : ∀ᵐ b ∂ν, b ∈ T)
    {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤) (hm : p ≤ (μ ∗ₘ ν) S) :
    ∃ b ∈ T, p ≤ 2 * μ ((· * b) ⁻¹' S) := by
  apply exists_half_le_of_lintegral ν hT hp hpt
  rwa [← mconv_apply_eq_lintegral_right_preimage μ ν hS]

end TransposeFollowup
