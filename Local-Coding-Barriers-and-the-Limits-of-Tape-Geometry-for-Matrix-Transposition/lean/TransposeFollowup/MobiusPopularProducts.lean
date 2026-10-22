import TransposeFollowup.PopularProductEnergy
import TransposeFollowup.ProductDensityPairs
import TransposeFollowup.MobiusSetEnergyRegularization

/-! A bounded high-energy open set gives a bounded open popular-product
region and a dense relation of actual pairs. This is input to weak BSG. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem popularProductSet_subset_entryBox {A B : Set Group} {Q R : ℝ}
    (hA : A ⊆ matrixEntryBox Q) (hB : B ⊆ matrixEntryBox R) (t : ℝ≥0∞) :
    popularProductSet (Measure.haar : Measure Group) A B t ⊆ matrixEntryBox (2 * Q * R) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp (popularProductSet_subset_mul Measure.haar A B t hx)
  exact matrixEntryBox_mul (hA ha) (hB hb)

theorem popularProductSet_geometry {O : Set Group} {Q : ℝ} (hO : IsOpen O)
    (hOb : O ⊆ matrixEntryBox Q) (hO0 : 0 < (Measure.haar : Measure Group) O)
    (hOt : (Measure.haar : Measure Group) O < ⊤) {L : ℝ≥0∞}
    (hL : 0 < L) (hLt : L ≠ ⊤)
    (hE : ((Measure.haar : Measure Group) O) ^ 3 ≤ L * haarMultiplicativeEnergy Measure.haar O O) :
    let H : Measure Group := Measure.haar
    let C := popularProductSet H O O (H O / (2 * L))
    C.Nonempty ∧ IsOpen C ∧ IsCompact (closure C) ∧
      closure C ⊆ matrixEntryBox (2 * Q ^ 2) ∧ 0 < H C ∧ H C < ⊤ ∧
      H C ≤ 2 * L * H O ∧ H O ^ 2 ≤ 2 * L *
        (H.prod H) {p : Group × Group | p.1 ∈ O ∧ p.2 ∈ O ∧ p.1 * p.2 ∈ C} := by
  let H : Measure Group := Measure.haar
  let C := popularProductSet H O O (H O / (2 * L))
  have hb := popularProductSet_bounds H hO.measurableSet hO0 hOt hL hLt hE
  have hCo : IsOpen C := popularProductSet_isOpen H hO.measurableSet hO _
  have hCn : C.Nonempty := by
    by_contra hn
    have hz : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hm := hb.2
    change H O ^ 2 ≤ 2 * L * ∫⁻ x in C, densityConvolution H (O.indicator 1) (O.indicator 1) x ∂H at hm
    rw [hz, Measure.restrict_empty, lintegral_zero_measure, mul_zero] at hm
    have hp : 0 < H O ^ 2 := by positivity
    exact (not_le_of_gt hp) hm
  have hCb : C ⊆ matrixEntryBox (2 * Q ^ 2) := by
    simpa only [pow_two, mul_assoc] using popularProductSet_subset_entryBox hOb hOb (H O / (2 * L))
  have hCc : closure C ⊆ matrixEntryBox (2 * Q ^ 2) :=
    closure_minimal hCb (matrixEntryBox_isCompact _).isClosed
  refine ⟨hCn, hCo, (matrixEntryBox_isCompact _).of_isClosed_subset isClosed_closure hCc,
    hCc, hCo.measure_pos H hCn, ?_, hb.1, ?_⟩
  · exact lt_of_le_of_lt hb.1 (by finiteness)
  · rw [← setLIntegral_densityConvolution_eq_pair_measure H hO.measurableSet hO.measurableSet hCo.measurableSet]
    exact hb.2

end TransposeFollowup.RealMobius
