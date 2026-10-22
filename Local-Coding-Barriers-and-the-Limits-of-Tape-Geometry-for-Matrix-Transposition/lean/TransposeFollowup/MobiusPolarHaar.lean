import TransposeFollowup.MobiusColumnHaar
import TransposeFollowup.MobiusAffineWavelet
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! The actual Haar integral in polar first-column coordinates. The
angular interval is (-pi,pi); the omitted ray is already null in the
library's polar change-of-variables theorem. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

noncomputable def polarColumn (a θ : ℝ) : Fin 2 → ℝ := ![a * Real.cos θ, a * Real.sin θ]

theorem columnSqNorm_polarColumn (a θ : ℝ) : columnSqNorm (polarColumn a θ) = a ^ 2 := by
  simp only [columnSqNorm, polarColumn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

theorem polarColumn_ne_zero {a : ℝ} (ha : 0 < a) (θ : ℝ) : polarColumn a θ ≠ 0 := by
  intro hz
  have he := columnSqNorm_polarColumn a θ
  rw [hz] at he
  simp only [columnSqNorm, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), zero_add] at he
  exact (sq_pos_of_pos ha).ne' he.symm

noncomputable def rotationMatrix (θ : ℝ) : Group :=
  ⟨!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ], by
    simpa [Matrix.det_fin_two, pow_two] using Real.cos_sq_add_sin_sq θ⟩

theorem columnChart_polar_factor {a : ℝ} (ha : 0 < a) (θ b : ℝ) :
    columnChart (polarColumn a θ, b) =
      rotationMatrix θ * affineWaveletMatrix (a ^ 2) (sq_pos_of_pos ha) (a ^ 2 * b) := by
  rw [columnChart, dite_eq_left (polarColumn_ne_zero ha θ)]
  apply Subtype.ext
  change !![a * Real.cos θ, b * (a * Real.cos θ) - (a * Real.sin θ) / columnSqNorm (polarColumn a θ);
      a * Real.sin θ, b * (a * Real.sin θ) + (a * Real.cos θ) / columnSqNorm (polarColumn a θ)] =
    !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] *
      !![Real.sqrt (a ^ 2), (a ^ 2 * b) / Real.sqrt (a ^ 2); 0, (Real.sqrt (a ^ 2))⁻¹]
  rw [columnSqNorm_polarColumn, Real.sqrt_sq ha.le]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  all_goals ring

theorem lintegral_column_polar (f : (Fin 2 → ℝ) → ℝ≥0∞) :
    (∫⁻ v, f v) = ∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * f (polarColumn p.1 p.2) := by
  calc
    _ = ∫⁻ p : ℝ × ℝ, f (MeasurableEquiv.finTwoArrow.symm p) := by
      simpa only [MeasurableEquiv.symm_apply_apply] using
        (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
          MeasurableEquiv.finTwoArrow.measurableEmbedding (fun p => f (MeasurableEquiv.finTwoArrow.symm p))
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • f (MeasurableEquiv.finTwoArrow.symm (polarCoord.symm p)) :=
      (lintegral_comp_polarCoord_symm _).symm
    _ = _ := by
      apply lintegral_congr
      intro p
      change ENNReal.ofReal p.1 * f _ = ENNReal.ofReal p.1 * f _
      congr 2

variable [MeasurableSpace Group] [BorelSpace Group]

theorem haar_lintegral_columnChart {f : Group → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ g, f g ∂(Measure.haar : Measure Group)) =
      (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
        ∫⁻ v : Fin 2 → ℝ, ∫⁻ b : ℝ, f (columnChart (v, b)) := by
  conv_lhs => rw [haar_eq_columnChartMeasure, lintegral_smul_measure]
  change (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
    (∫⁻ g, f g ∂Measure.map columnChart volume) = _
  rw [lintegral_map hf columnChart_measurable]
  congr 1
  exact lintegral_prod (fun z : (Fin 2 → ℝ) × ℝ => f (columnChart z))
    (hf.comp columnChart_measurable).aemeasurable

theorem haar_lintegral_polar {f : Group → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ g, f g ∂(Measure.haar : Measure Group)) =
      (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
        ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
          ∫⁻ b : ℝ, f (columnChart (polarColumn p.1 p.2, b)) := by
  rw [haar_lintegral_columnChart hf, lintegral_column_polar]

end TransposeFollowup.RealMobius
