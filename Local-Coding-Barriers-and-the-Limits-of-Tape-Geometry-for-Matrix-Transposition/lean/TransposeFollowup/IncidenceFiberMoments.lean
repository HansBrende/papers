import TransposeFollowup.DensityConvolutionTrace

/-! Continuous fiber sizes and codegrees of a measurable bipartite
relation. Tonelli identifies the moments needed for weak-BSG selection. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def edgeFiberMass (μ : Measure X) (E : Set (X × Y)) (y : Y) : ℝ≥0∞ :=
  ∫⁻ x, E.indicator (1 : X × Y → ℝ≥0∞) (x, y) ∂μ

noncomputable def edgeCodegree (ν : Measure Y) (E : Set (X × Y)) (p : X × X) : ℝ≥0∞ :=
  ∫⁻ y, E.indicator (1 : X × Y → ℝ≥0∞) (p.1, y) * E.indicator 1 (p.2, y) ∂ν

noncomputable def edgeBadFiberMass (μ : Measure X) (ν : Measure Y) (E : Set (X × Y))
    (t : ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∫⁻ p in {p | edgeCodegree ν E p ≤ t},
    E.indicator (1 : X × Y → ℝ≥0∞) (p.1, y) * E.indicator 1 (p.2, y) ∂μ.prod μ

theorem edgeFiberMass_measurable (μ : Measure X) [SFinite μ] {E : Set (X × Y)}
    (hE : MeasurableSet E) : Measurable (edgeFiberMass μ E) := by
  unfold edgeFiberMass
  have he : Measurable (E.indicator (1 : X × Y → ℝ≥0∞)) := measurable_const.indicator hE
  exact Measurable.lintegral_prod_right (by fun_prop)

theorem edgeCodegree_measurable (ν : Measure Y) [SFinite ν] {E : Set (X × Y)}
    (hE : MeasurableSet E) : Measurable (edgeCodegree ν E) := by
  unfold edgeCodegree
  have he : Measurable (E.indicator (1 : X × Y → ℝ≥0∞)) := measurable_const.indicator hE
  exact Measurable.lintegral_prod_right (by fun_prop)

theorem edgeFiberMass_eq_measure (μ : Measure X) {E : Set (X × Y)}
    (hE : MeasurableSet E) (y : Y) : edgeFiberMass μ E y = μ {x | (x, y) ∈ E} := by
  calc
    _ = ∫⁻ x, {x | (x, y) ∈ E}.indicator (1 : X → ℝ≥0∞) x ∂μ := by
      apply lintegral_congr
      intro x
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    _ = _ := lintegral_indicator_one (hE.preimage (by fun_prop))

theorem edgeFiberMass_lintegral (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) :
    (∫⁻ y, edgeFiberMass μ E y ∂ν) = (μ.prod ν) E := by
  have he : Measurable (E.indicator (1 : X × Y → ℝ≥0∞)) := measurable_const.indicator hE
  exact (lintegral_prod_symm _ he.aemeasurable).symm.trans (lintegral_indicator_one hE)

theorem edgeFiberMass_second_moment_lower (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) :
    (μ.prod ν) E ^ 2 ≤ (∫⁻ y, edgeFiberMass μ E y ^ 2 ∂ν) * ν univ := by
  have h := lintegral_mul_sq_le_lintegral_sq_mul_lintegral_sq ν
    (edgeFiberMass_measurable μ hE) (show Measurable (1 : Y → ℝ≥0∞) from measurable_const)
  simpa only [Pi.one_apply, mul_one, one_pow, lintegral_one, edgeFiberMass_lintegral μ ν hE] using h

theorem edgeBadFiberMass_lintegral_le (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) (t : ℝ≥0∞) :
    (∫⁻ y, edgeBadFiberMass μ ν E t y ∂ν) ≤ t * μ univ ^ 2 := by
  have he : Measurable (E.indicator (1 : X × Y → ℝ≥0∞)) := measurable_const.indicator hE
  have hb : MeasurableSet {p | edgeCodegree ν E p ≤ t} :=
    measurableSet_le (edgeCodegree_measurable ν hE) measurable_const
  calc
    _ = ∫⁻ p in {p | edgeCodegree ν E p ≤ t}, edgeCodegree ν E p ∂μ.prod μ := by
      unfold edgeBadFiberMass edgeCodegree
      exact lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ _p in {p | edgeCodegree ν E p ≤ t}, t ∂μ.prod μ :=
      lintegral_mono_ae ((ae_restrict_mem hb).mono (fun _ hp => hp))
    _ = t * (μ.prod μ) {p | edgeCodegree ν E p ≤ t} := by rw [setLIntegral_const]
    _ ≤ t * (μ.prod μ) univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))
    _ = _ := by rw [← Set.univ_prod_univ, Measure.prod_prod, pow_two]

theorem edgeBadFiberMass_eq_measure (μ : Measure X) (ν : Measure Y)
    {E : Set (X × Y)} (hE : MeasurableSet E) (t : ℝ≥0∞) (y : Y) :
    edgeBadFiberMass μ ν E t y =
      (μ.prod μ) {p : X × X | (p.1, y) ∈ E ∧ (p.2, y) ∈ E ∧ edgeCodegree ν E p ≤ t} := by
  let F : Set (X × X) := {p | (p.1, y) ∈ E ∧ (p.2, y) ∈ E}
  have hF : MeasurableSet F := (hE.preimage (by fun_prop)).inter (hE.preimage (by fun_prop))
  calc
    _ = ∫⁻ p in {p | edgeCodegree ν E p ≤ t}, F.indicator (1 : X × X → ℝ≥0∞) p ∂μ.prod μ := by
      apply lintegral_congr
      intro p
      by_cases h1 : (p.1, y) ∈ E <;> by_cases h2 : (p.2, y) ∈ E <;>
        simp [F, h1, h2]
    _ = ((μ.prod μ).restrict {p | edgeCodegree ν E p ≤ t}) F := lintegral_indicator_one hF
    _ = _ := by
      rw [Measure.restrict_apply hF]
      congr 1
      ext p
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, F]
      tauto

end TransposeFollowup
