import TransposeFollowup.IncidenceFiberMoments
import TransposeFollowup.StrictDegreeTrimming

/-! Row degrees of open measurable relations, with exact complementary
degrees and pair-mass identities for restricted measures. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def relationRowDegree (ν : Measure Y) (E : Set (X × Y)) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, E.indicator (1 : X × Y → ℝ≥0∞) (x, y) ∂ν

theorem relationRowDegree_measurable (ν : Measure Y) [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) : Measurable (relationRowDegree ν E) := by
  have he : Measurable (E.indicator (1 : X × Y → ℝ≥0∞)) := measurable_const.indicator hE
  exact Measurable.lintegral_prod_right (by fun_prop)

theorem relationRowDegree_lowerSemicontinuous [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] (ν : Measure Y)
    {E : Set (X × Y)} (hE : IsOpen E) (hEm : MeasurableSet E) : LowerSemicontinuous (relationRowDegree ν E) := by
  apply lowerSemicontinuous_lintegral_family ν
  · intro x
    exact (measurable_const.indicator hEm).comp (by fun_prop)
  · intro y
    exact (hE.lowerSemicontinuous_indicator (show (0 : ℝ≥0∞) ≤ 1 from zero_le)).comp (by fun_prop)

omit [MeasurableSpace X] in
theorem relationRowDegree_le (ν : Measure Y) (E : Set (X × Y)) (x : X) :
    relationRowDegree ν E x ≤ ν univ := by
  calc
    _ ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂ν := lintegral_mono fun y => Set.indicator_le_self' (fun _ _ => zero_le) (x, y)
    _ = _ := lintegral_one

theorem relationRowDegree_add_compl (ν : Measure Y) {E : Set (X × Y)}
    (hE : MeasurableSet E) (x : X) :
    relationRowDegree ν E x + relationRowDegree ν Eᶜ x = ν univ := by
  have he : Measurable (fun y => E.indicator (1 : X × Y → ℝ≥0∞) (x, y)) :=
    (measurable_const.indicator hE).comp (by fun_prop)
  rw [relationRowDegree, relationRowDegree, ← lintegral_add_left he]
  calc
    _ = ∫⁻ _y, (1 : ℝ≥0∞) ∂ν := by
      apply lintegral_congr
      intro y
      by_cases hy : (x, y) ∈ E <;> simp [hy]
    _ = _ := lintegral_one

theorem relationRowDegree_lintegral (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) :
    (∫⁻ x, relationRowDegree ν E x ∂μ) = (μ.prod ν) E := by
  have he : Measurable (E.indicator (1 : X × Y → ℝ≥0∞)) := measurable_const.indicator hE
  exact (lintegral_prod _ he.aemeasurable).symm.trans (lintegral_indicator_one hE)

theorem relationRowDegree_restrict_lintegral (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (A : Set X) (B : Set Y)
    {E : Set (X × Y)} (hE : MeasurableSet E) :
    (∫⁻ x in A, relationRowDegree (ν.restrict B) E x ∂μ) =
      (μ.prod ν) {p | p.1 ∈ A ∧ p.2 ∈ B ∧ p ∈ E} := by
  rw [relationRowDegree_lintegral _ _ hE, Measure.prod_restrict, Measure.restrict_apply hE]
  congr 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq]
  tauto

end TransposeFollowup
