import TransposeFollowup.ContinuousDensityConvolution
import Mathlib.Topology.Semicontinuity.Basic

/-! Strict popular-product regions are open. Fatou's lemma supplies only
the lower semicontinuity needed here; no general continuity claim is used. -/
namespace TransposeFollowup
open Classical MeasureTheory Set Filter
open scoped ENNReal Topology Pointwise
set_option autoImplicit false

theorem lowerSemicontinuous_lintegral_family {X Y : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [MeasurableSpace Y] (σ : Measure Y) {F : X → Y → ℝ≥0∞}
    (hm : ∀ x, Measurable (F x)) (hl : ∀ y, LowerSemicontinuous (fun x => F x y)) :
    LowerSemicontinuous (fun x => ∫⁻ y, F x y ∂σ) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro x
  calc
    (∫⁻ y, F x y ∂σ) ≤ ∫⁻ y, liminf (fun z => F z y) (𝓝 x) ∂σ :=
      lintegral_mono fun y => (hl y).le_liminf x
    _ ≤ _ := lintegral_liminf_le hm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def popularProductSet (σ : Measure G) (A B : Set G) (t : ℝ≥0∞) : Set G :=
  {x | t < densityConvolution σ (A.indicator 1) (B.indicator 1) x}

omit [MeasurableMul₂ G] in
theorem densityConvolution_indicator_lowerSemicontinuous [TopologicalSpace G]
    [IsTopologicalGroup G] [BorelSpace G] [FirstCountableTopology G]
    (σ : Measure G) {A B : Set G} (hA : MeasurableSet A) (hB : IsOpen B) :
    LowerSemicontinuous (densityConvolution σ (A.indicator 1) (B.indicator 1)) := by
  apply lowerSemicontinuous_lintegral_family σ
  · intro x
    exact (measurable_const.indicator hA).mul
      ((measurable_const.indicator hB.measurableSet).comp (by fun_prop))
  · intro y
    by_cases hy : y ∈ A
    · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
      exact (hB.lowerSemicontinuous_indicator (show (0 : ℝ≥0∞) ≤ 1 from zero_le)).comp
        (by fun_prop)
    · simp only [Set.indicator_of_notMem hy, zero_mul]
      exact lowerSemicontinuous_const

omit [MeasurableMul₂ G] in
theorem popularProductSet_isOpen [TopologicalSpace G] [IsTopologicalGroup G]
    [BorelSpace G] [FirstCountableTopology G] (σ : Measure G) {A B : Set G}
    (hA : MeasurableSet A) (hB : IsOpen B) (t : ℝ≥0∞) :
    IsOpen (popularProductSet σ A B t) :=
  (densityConvolution_indicator_lowerSemicontinuous σ hA hB).isOpen_preimage t

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem densityConvolution_indicator_eq_zero_of_not_mem_mul (σ : Measure G)
    {A B : Set G} {x : G} (hx : x ∉ A * B) :
    densityConvolution σ (A.indicator 1) (B.indicator 1) x = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : y ∈ A
  · have hn : y⁻¹ * x ∉ B := by
      intro hz
      exact hx (by simpa only [mul_inv_cancel_left] using Set.mul_mem_mul hy hz)
    simp only [Set.indicator_of_notMem hn, mul_zero, Pi.zero_apply]
  · simp only [Set.indicator_of_notMem hy, zero_mul, Pi.zero_apply]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem popularProductSet_subset_mul (σ : Measure G) (A B : Set G) (t : ℝ≥0∞) :
    popularProductSet σ A B t ⊆ A * B := by
  intro x hx
  by_contra hn
  change t < densityConvolution σ (A.indicator 1) (B.indicator 1) x at hx
  have hz := densityConvolution_indicator_eq_zero_of_not_mem_mul σ hn
  exact (not_lt_of_ge zero_le) (by simpa only [hz] using hx)

end TransposeFollowup
