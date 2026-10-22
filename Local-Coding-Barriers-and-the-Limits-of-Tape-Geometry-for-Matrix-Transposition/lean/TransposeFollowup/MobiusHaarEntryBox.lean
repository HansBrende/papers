import TransposeFollowup.MobiusMatrixGeometryCore
import TransposeFollowup.MobiusColumnHaar

/-! A polynomial Haar-volume bound for bounded matrix entries, derived
from the proved column chart rather than assumed coordinate geometry. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem columnShear_abs_le_second_column (g : Group) :
    |columnShear g| ≤ (g 0 1 ^ 2 + g 1 1 ^ 2) / 2 := by
  let d := g 0 0 * g 0 1 + g 1 0 * g 1 1
  let q := columnSqNorm (firstColumn g)
  let r := g 0 1 ^ 2 + g 1 1 ^ 2
  have hq : 0 < q := columnSqNorm_pos (firstColumn_ne_zero g)
  have hgram : q * r - d ^ 2 = 1 := by
    calc
      _ = (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 := by
        dsimp [q, r, d, columnSqNorm, firstColumn]
        ring
      _ = _ := by rw [determinant]; norm_num
  have hd : 2 * |d| ≤ q * r := by
    nlinarith [sq_nonneg (|d| - 1), sq_abs d]
  change |d / q| ≤ r / 2
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  nlinarith only [hd]

theorem matrixEntryBox_column_bounds {B : ℝ} {g : Group} (hg : g ∈ matrixEntryBox B) :
    columnSqNorm (firstColumn g) ≤ 2 * B ^ 2 ∧ |columnShear g| ≤ B ^ 2 := by
  have hs (i j : Fin 2) : g i j ^ 2 ≤ B ^ 2 :=
    sq_le_sq' (abs_le.mp (hg i j)).1 (abs_le.mp (hg i j)).2
  constructor
  · change g 0 0 ^ 2 + g 1 0 ^ 2 ≤ _
    linarith [hs 0 0, hs 1 0]
  · have hb := columnShear_abs_le_second_column g
    linarith [hs 0 1, hs 1 1]

theorem matrixEntryBox_isCompact (B : ℝ) : IsCompact (matrixEntryBox B) := by
  have hc : Topology.IsClosedEmbedding (fun g : Group => fun i j : Fin 2 => g i j) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)
  have hi := hc.isCompact_preimage
    (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin 2 => -B) (fun _ _ : Fin 2 => B)))
  convert hi using 1
  ext g
  simp [matrixEntryBox, abs_le, Pi.le_def, forall_and]

theorem matrixEntryBox_coordinates_subset (B : ℝ) :
    columnCoordinates '' matrixEntryBox B ⊆
      Icc (fun _ : Fin 2 => -B) (fun _ : Fin 2 => B) ×ˢ Icc (-(B ^ 2)) (B ^ 2) := by
  rintro _ ⟨g, hg, rfl⟩
  have hb := (matrixEntryBox_column_bounds hg).2
  refine ⟨⟨?_, ?_⟩, abs_le.mp hb⟩
  · intro i
    exact (abs_le.mp (hg i 0)).1
  · intro i
    exact (abs_le.mp (hg i 0)).2

variable [MeasurableSpace Group] [BorelSpace Group]

theorem columnChartMeasure_entryBox_le {B : ℝ} (hB : 0 ≤ B) :
    columnChartMeasure (matrixEntryBox B) ≤ ENNReal.ofReal (8 * B ^ 4) := by
  calc
    _ = volume (columnCoordinates '' matrixEntryBox B) :=
      columnChartMeasure_compact _ (matrixEntryBox_isCompact B)
    _ ≤ volume (Icc (fun _ : Fin 2 => -B) (fun _ : Fin 2 => B) ×ˢ Icc (-(B ^ 2)) (B ^ 2)) :=
      measure_mono (matrixEntryBox_coordinates_subset B)
    _ = _ := by
      change ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ))
        (Icc (fun _ : Fin 2 => -B) (fun _ : Fin 2 => B) ×ˢ Icc (-(B ^ 2)) (B ^ 2)) = _
      rw [Measure.prod_prod, Real.volume_Icc_pi, Real.volume_Icc]
      simp only [Fin.prod_univ_two, sub_neg_eq_add]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem haar_entryBox_le {B : ℝ} (hB : 0 ≤ B) :
    (Measure.haar : Measure Group) (matrixEntryBox B) ≤
      (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) * ENNReal.ofReal (8 * B ^ 4) := by
  calc
    _ = (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
        columnChartMeasure (matrixEntryBox B) := by
      conv_lhs => rw [haar_eq_columnChartMeasure]
      rfl
    _ ≤ _ := by
      gcongr
      exact columnChartMeasure_entryBox_le hB

end TransposeFollowup.RealMobius
