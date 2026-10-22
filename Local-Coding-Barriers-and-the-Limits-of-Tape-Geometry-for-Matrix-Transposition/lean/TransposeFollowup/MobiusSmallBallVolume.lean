import TransposeFollowup.MobiusIdentityCoordinates

/-! Two-sided cubic Haar volume for the exact Frobenius-radius identity
balls used by the smoothing kernel. Constants are explicit and unoptimized. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem identityColumnBox_measurableSet (s t : ℝ) : MeasurableSet (identityColumnBox s t) := by
  rw [identityColumnBox_eq_prod]
  exact measurableSet_Icc.prod measurableSet_Icc

theorem volume_identityColumnBox {s t : ℝ} (hs : 0 ≤ s) :
    volume (identityColumnBox s t) = ENNReal.ofReal (8 * s ^ 2 * t) := by
  rw [identityColumnBox_eq_prod]
  change ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ))
    (Icc ![1 - s, -s] ![1 + s, s] ×ˢ Icc (-t) t) = _
  rw [Measure.prod_prod, Real.volume_Icc_pi, Real.volume_Icc]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_neg_eq_add,
    show 1 + s - (1 - s) = 2 * s by ring]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

variable [MeasurableSpace Group] [BorelSpace Group]

theorem columnChartMeasure_preimage_identityColumnBox (s t : ℝ) :
    columnChartMeasure (columnCoordinates ⁻¹' identityColumnBox s t) =
      volume (identityColumnBox s t) := by
  calc
    _ = (Measure.map columnCoordinates columnChartMeasure) (identityColumnBox s t) :=
      (Measure.map_apply columnCoordinates_continuous.measurable
        (identityColumnBox_measurableSet s t)).symm
    _ = _ := by rw [columnChartMeasure_map_coordinates]

theorem columnChartMeasure_identityBall_lower {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ENNReal.ofReal (η ^ 3 / 512) ≤ columnChartMeasure (mobiusIdentityBall η) := by
  calc
    _ = volume (identityColumnBox (η / 16) (η / 16)) := by
      rw [volume_identityColumnBox (by positivity)]
      congr 1
      ring
    _ = columnChartMeasure (columnCoordinates ⁻¹' identityColumnBox (η / 16) (η / 16)) :=
      (columnChartMeasure_preimage_identityColumnBox _ _).symm
    _ ≤ _ := measure_mono (column_box_subset_mobiusIdentityBall hη hηhalf)

theorem columnChartMeasure_identityBall_upper {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    columnChartMeasure (mobiusIdentityBall η) ≤ ENNReal.ofReal (96 * η ^ 3) := by
  calc
    _ ≤ columnChartMeasure (columnCoordinates ⁻¹' identityColumnBox η (12 * η)) :=
      measure_mono (mobiusIdentityBall_subset_column_box hη hηhalf)
    _ = volume (identityColumnBox η (12 * η)) := columnChartMeasure_preimage_identityColumnBox _ _
    _ = _ := by
      rw [volume_identityColumnBox hη.le]
      congr 1
      ring

theorem haar_identityBall_lower {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
      ENNReal.ofReal (η ^ 3 / 512) ≤ (Measure.haar : Measure Group) (mobiusIdentityBall η) := by
  conv_rhs => rw [haar_eq_columnChartMeasure]
  exact mul_le_mul' le_rfl (columnChartMeasure_identityBall_lower hη hηhalf)

theorem haar_identityBall_upper {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    (Measure.haar : Measure Group) (mobiusIdentityBall η) ≤
      (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
        ENNReal.ofReal (96 * η ^ 3) := by
  conv_lhs => rw [haar_eq_columnChartMeasure]
  exact mul_le_mul' le_rfl (columnChartMeasure_identityBall_upper hη hηhalf)

theorem haar_identityBall_doubling {η : ℝ} (hη : 0 < η) (hηquarter : η ≤ 1 / 4) :
    (Measure.haar : Measure Group) (mobiusIdentityBall (2 * η)) ≤
      393216 * (Measure.haar : Measure Group) (mobiusIdentityBall η) := by
  have hlo := haar_identityBall_lower hη (by linarith)
  have hhi := haar_identityBall_upper (by positivity : (0 : ℝ) < 2 * η) (by linarith)
  calc
    _ ≤ _ := hhi
    _ = 393216 * ((Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
        ENNReal.ofReal (η ^ 3 / 512)) := by
      rw [mul_left_comm (393216 : ℝ≥0∞), ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring
    _ ≤ _ := mul_le_mul' le_rfl hlo

end TransposeFollowup.RealMobius
