import TransposeFollowup.MobiusColumnCoordinates
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace

/-! A total measurable column chart and its continuous inverse.
The exceptional zero-column fiber is assigned the identity matrix. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
set_option autoImplicit false

noncomputable def columnChart (z : (Fin 2 → ℝ) × ℝ) : Group :=
  if hv : z.1 ≠ 0 then columnMatrix z.1 hv z.2 else 1

noncomputable def columnCoordinates (g : Group) : (Fin 2 → ℝ) × ℝ :=
  (firstColumn g, columnShear g)

theorem columnChart_columnCoordinates (g : Group) : columnChart (columnCoordinates g) = g := by
  simp only [columnChart, columnCoordinates, dite_eq_left (firstColumn_ne_zero g),
    columnMatrix_coordinates]

theorem columnCoordinates_columnChart (z : (Fin 2 → ℝ) × ℝ) (hz : z.1 ≠ 0) :
    columnCoordinates (columnChart z) = z := by
  simp only [columnChart, dite_eq_left hz, columnCoordinates, firstColumn_columnMatrix,
    columnShear_columnMatrix, Prod.mk.eta]

theorem firstColumn_continuous : Continuous firstColumn := by
  unfold firstColumn
  fun_prop

theorem columnSqNorm_continuous : Continuous columnSqNorm := by
  unfold columnSqNorm
  fun_prop

theorem columnShear_continuous : Continuous columnShear := by
  exact (by fun_prop : Continuous (fun g : Group => g 0 0 * g 0 1 + g 1 0 * g 1 1)).div
    (columnSqNorm_continuous.comp firstColumn_continuous)
    (fun g => (columnSqNorm_pos (firstColumn_ne_zero g)).ne')

theorem columnCoordinates_continuous : Continuous columnCoordinates :=
  firstColumn_continuous.prodMk columnShear_continuous

theorem columnChart_measurable [MeasurableSpace Group] [BorelSpace Group] :
    Measurable columnChart := by
  have hc : Topology.IsClosedEmbedding (fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 2) (R := ℝ)
  apply hc.measurableEmbedding.measurable_comp_iff.mp
  have he : (fun z => (columnChart z : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun z : (Fin 2 → ℝ) × ℝ => if z.1 ≠ 0 then
        !![z.1 0, z.2 * z.1 0 - z.1 1 / columnSqNorm z.1;
           z.1 1, z.2 * z.1 1 + z.1 0 / columnSqNorm z.1] else 1 := by
    funext z
    simp only [columnChart]
    split <;> rfl
  change Measurable (fun z => (columnChart z : Matrix (Fin 2) (Fin 2) ℝ))
  rw [he]
  apply Measurable.ite
  · exact (measurableSet_eq_fun measurable_fst measurable_const).compl
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [columnSqNorm] <;> fun_prop
  · exact measurable_const

noncomputable def columnShift (g : Group) (v : Fin 2 → ℝ) : ℝ :=
  columnShear (g * columnChart (v, 0))

noncomputable def columnAction (g : Group) (z : (Fin 2 → ℝ) × ℝ) : (Fin 2 → ℝ) × ℝ :=
  (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) ℝ) z.1, columnShift g z.1 + z.2)

theorem columnShift_measurable [MeasurableSpace Group] [BorelSpace Group] (g : Group) :
    Measurable (columnShift g) := by
  exact (columnShear_continuous.comp (continuous_const.mul continuous_id)).measurable.comp
    (columnChart_measurable.comp (measurable_id.prodMk measurable_const))

theorem columnCoordinates_mul_columnChart (g : Group) (z : (Fin 2 → ℝ) × ℝ)
    (hz : z.1 ≠ 0) :
    columnCoordinates (g * columnChart z) = columnAction g z := by
  rw [show columnChart z = columnMatrix z.1 hz z.2 from by
    simp only [columnChart, dite_eq_left hz],
    columnMatrix_eq_base_mul_upperUnipotent z.1 hz z.2, ← mul_assoc]
  simp only [columnCoordinates, firstColumn_mul_upperUnipotent, columnShear_mul_upperUnipotent]
  apply Prod.ext
  · change firstColumn (g * columnMatrix z.1 hz 0) = _
    rw [firstColumn_mul, firstColumn_columnMatrix]
    rfl
  · change columnShear (g * columnMatrix z.1 hz 0) + z.2 = columnShift g z.1 + z.2
    simp only [columnShift, columnChart, dite_eq_left hz]

theorem columnChart_columnAction (g : Group) (z : (Fin 2 → ℝ) × ℝ) (hz : z.1 ≠ 0) :
    columnChart (columnAction g z) = g * columnChart z := by
  rw [← columnCoordinates_mul_columnChart g z hz, columnChart_columnCoordinates]

end TransposeFollowup.RealMobius
