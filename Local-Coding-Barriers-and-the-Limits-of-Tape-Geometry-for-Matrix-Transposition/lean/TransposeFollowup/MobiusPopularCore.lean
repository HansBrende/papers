import TransposeFollowup.HaarSandwichBounds
import TransposeFollowup.MobiusSmallProductBSG

/-! A concrete symmetric open core for a bounded SL2 set with small
quotient set. All sandwich powers, tripling and entry bounds are explicit. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem popular_overlap_core {A : Set Group} {Q : ℝ} (hA : IsOpen A)
    (hAb : A ⊆ matrixEntryBox Q) (hA0 : 0 < (Measure.haar : Measure Group) A)
    {K : ℝ≥0∞} (hKone : 1 ≤ K) (hKt : K ≠ ⊤)
    (hsmall : (Measure.haar : Measure Group) (A * A⁻¹) ≤ K * (Measure.haar : Measure Group) A) :
    let H : Measure Group := Measure.haar
    let T := popularProductSet H A⁻¹ A (H A / (2 * K))
    1 ∈ T ∧ IsOpen T ∧ (∀ x, x⁻¹ ∈ T ↔ x ∈ T) ∧
      IsCompact (closure T) ∧ closure T ⊆ matrixEntryBox (2 * Q ^ 2) ∧
      0 < H T ∧ H T < ⊤ ∧ H A ≤ 2 * K * H T ∧ H T ≤ 2 * K * H A ∧
      (∀ n : ℕ, H (A * T ^ n * A⁻¹) ≤ 2 ^ n * K ^ (2 * n + 1) * H A) ∧
      H (A * T) ≤ 2 * K ^ 3 * H A ∧ H (T ^ 3) ≤ 16 * K ^ 8 * H T := by
  let H : Measure Group := Measure.haar
  let t := H A / (2 * K)
  let T := popularProductSet H A⁻¹ A t
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) hKone
  have hAt : H A < ⊤ := (measure_mono hAb).trans_lt (matrixEntryBox_isCompact Q).measure_lt_top
  have hAn : A.Nonempty := (hA.measure_pos_iff H).mp hA0
  have hTo : IsOpen T := popularProductSet_isOpen H hA.measurableSet.inv hA t
  have hcancel : (2 * K) * t = H A := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have htlt : t < H A := by
    apply (ENNReal.mul_lt_mul_iff_right (by positivity : 2 * K ≠ 0) (by finiteness)).mp
    rw [hcancel]
    calc
      H A = 1 * H A := (one_mul _).symm
      _ < (2 * K) * H A := (ENNReal.mul_lt_mul_iff_left hA0.ne' hAt.ne).mpr (by
        calc
          (1 : ℝ≥0∞) < 2 * 1 := by norm_num
          _ ≤ 2 * K := mul_le_mul' le_rfl hKone)
  have hfone : densityConvolution H ((A⁻¹).indicator 1) (A.indicator 1) 1 = H A := by
    rw [inverse_indicator_convolution_eq_overlap H hA.measurableSet]
    calc
      _ = ∫⁻ y, A.indicator (1 : Group → ℝ≥0∞) y ∂H := by
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ A <;> simp [hy]
      _ = _ := lintegral_indicator_one hA.measurableSet
  have hT1 : 1 ∈ T := by
    change t < densityConvolution H ((A⁻¹).indicator 1) (A.indicator 1) 1
    rwa [hfone]
  have hTs : ∀ x, x⁻¹ ∈ T ↔ x ∈ T := by
    intro x
    change (t < densityConvolution H ((A⁻¹).indicator 1) (A.indicator 1) x⁻¹) ↔ _
    rw [inverse_indicator_convolution_inv H hA.measurableSet]
    rfl
  have hAi : A⁻¹ ⊆ matrixEntryBox Q := by
    intro x hx
    have hxi : x⁻¹ ∈ A := by simpa only [Set.mem_inv] using hx
    exact (matrixEntryBox_inv_iff Q x).mp (hAb hxi)
  have hTb : T ⊆ matrixEntryBox (2 * Q ^ 2) := by
    simpa only [pow_two, mul_assoc] using popularProductSet_subset_entryBox hAi hAb t
  have hTc : closure T ⊆ matrixEntryBox (2 * Q ^ 2) :=
    closure_minimal hTb (matrixEntryBox_isCompact _).isClosed
  have hAA : MeasurableSet (A * A⁻¹) := hA.mul_right.measurableSet
  obtain ⟨hTlow, hTup⟩ := popularOverlap_volume_bounds H hA.measurableSet hAA hA0 hAt hK hKt hsmall
  have hsand : ∀ n : ℕ, H (A * T ^ n * A⁻¹) ≤ 2 ^ n * K ^ (2 * n + 1) * H A := by
    intro n
    exact popularOverlap_sandwich_volume H hA.measurableSet hAA hA0 hAt hK hKt hsmall n
      (hA.mul_right.mul_right.measurableSet)
  refine ⟨hT1, hTo, hTs, (matrixEntryBox_isCompact _).of_isClosed_subset isClosed_closure hTc,
    hTc, hTo.measure_pos H ⟨1, hT1⟩, (measure_mono hTb).trans_lt (matrixEntryBox_isCompact _).measure_lt_top,
    hTlow, hTup, hsand, ?_, ?_⟩
  · calc
      H (A * T) ≤ H (A * T * A⁻¹) := haar_measure_le_right_product H (A * T) hAn.inv
      _ ≤ 2 * K ^ 3 * H A := by simpa only [pow_one] using hsand 1
  · calc
      H (T ^ 3) ≤ H (A * T ^ 3) := haar_measure_le_left_product H hAn _
      _ ≤ H (A * T ^ 3 * A⁻¹) := haar_measure_le_right_product H _ hAn.inv
      _ ≤ 8 * K ^ 7 * H A := by simpa only [show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num] using hsand 3
      _ ≤ 8 * K ^ 7 * (2 * K * H T) := mul_le_mul' le_rfl hTlow
      _ = _ := by ring

end TransposeFollowup.RealMobius
