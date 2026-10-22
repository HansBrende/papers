import TransposeFollowup.MobiusColumnChart
import TransposeFollowup.MobiusHaarKernel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Lebesgue measure in the global column/shear coordinates is Haar.
Left multiplication is a determinant-one linear map followed by a
fiberwise translation. The zero-column fiber is null. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem column_linear_measurePreserving (g : Group) :
    MeasurePreserving (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) ℝ)) volume volume := by
  constructor
  · change Measurable (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℝ))
    exact (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℝ)).continuous_of_finiteDimensional.measurable
  · change Measure.map (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℝ)) volume = volume
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [g.det_coe]; norm_num), g.det_coe]
    simp

theorem column_zero_fiber_ae : ∀ᵐ z : (Fin 2 → ℝ) × ℝ ∂volume, z.1 ≠ 0 :=
  Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0 : Fin 2 → ℝ))

variable [MeasurableSpace Group] [BorelSpace Group]

theorem columnAction_measurePreserving (g : Group) :
    MeasurePreserving (columnAction g) volume volume :=
  (column_linear_measurePreserving g).skew_product
    ((columnShift_measurable g).comp measurable_fst |>.add measurable_snd)
    (Filter.Eventually.of_forall fun v => (measurePreserving_add_left volume (columnShift g v)).map_eq)

noncomputable def columnChartMeasure : Measure Group := Measure.map columnChart volume

theorem columnChartMeasure_map_coordinates : Measure.map columnCoordinates columnChartMeasure = volume := by
  rw [columnChartMeasure, Measure.map_map columnCoordinates_continuous.measurable columnChart_measurable]
  calc
    _ = Measure.map id volume := Measure.map_congr (column_zero_fiber_ae.mono fun z hz =>
      columnCoordinates_columnChart z hz)
    _ = _ := Measure.map_id

instance instColumnChartMeasureLeftInvariant : Measure.IsMulLeftInvariant columnChartMeasure where
  map_mul_left_eq_self g := by
    have hg : Measurable (fun h : Group => g * h) := (continuous_const.mul continuous_id).measurable
    rw [columnChartMeasure, Measure.map_map hg
      columnChart_measurable]
    calc
      _ = Measure.map (columnChart ∘ columnAction g) volume :=
        Measure.map_congr (column_zero_fiber_ae.mono fun z hz => (columnChart_columnAction g z hz).symm)
      _ = Measure.map columnChart (Measure.map (columnAction g) volume) :=
        (Measure.map_map columnChart_measurable (columnAction_measurePreserving g).measurable).symm
      _ = _ := by rw [(columnAction_measurePreserving g).map_eq]

theorem columnChartMeasure_compact (K : Set Group) (hK : IsCompact K) :
    columnChartMeasure K = volume (columnCoordinates '' K) := by
  have hi : Function.Injective columnCoordinates := by
    intro g h he
    simpa only [columnChart_columnCoordinates] using congrArg columnChart he
  rw [← columnChartMeasure_map_coordinates, Measure.map_apply columnCoordinates_continuous.measurable
    (hK.image columnCoordinates_continuous).measurableSet, Set.preimage_image_eq _ hi]

instance instColumnChartMeasureFiniteOnCompacts : IsFiniteMeasureOnCompacts columnChartMeasure where
  lt_top_of_isCompact K hK := by
    rw [columnChartMeasure_compact K hK]
    exact (hK.image columnCoordinates_continuous).measure_lt_top

instance instColumnChartMeasureNeZero : NeZero columnChartMeasure :=
  ⟨(Measure.map_ne_zero_iff columnChart_measurable.aemeasurable).mpr (NeZero.ne volume)⟩

instance instColumnChartMeasureHaar : Measure.IsHaarMeasure columnChartMeasure where

theorem haar_eq_columnChartMeasure :
    (Measure.haar : Measure Group) =
      Measure.haarScalarFactor Measure.haar columnChartMeasure • columnChartMeasure :=
  Measure.isMulLeftInvariant_eq_smul Measure.haar columnChartMeasure

theorem haar_column_factor_pos :
    0 < Measure.haarScalarFactor (Measure.haar : Measure Group) columnChartMeasure :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

end TransposeFollowup.RealMobius
