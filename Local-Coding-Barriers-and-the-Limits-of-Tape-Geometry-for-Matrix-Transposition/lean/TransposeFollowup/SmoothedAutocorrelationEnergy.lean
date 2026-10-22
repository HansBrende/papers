import TransposeFollowup.SmoothedWalkAutocorrelation
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Autocorrelation energy: the maximum is at identity, and its value is
exactly the original density's squared L2 integral. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem autocorrelationDensity_le_one (σ : Measure H) [Measure.IsMulRightInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (x : H) :
    autocorrelationDensity σ f x ≤ autocorrelationDensity σ f 1 := by
  rw [autocorrelationDensity_eq_integral σ hf, autocorrelationDensity_one σ hf]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq σ Real.HolderConjugate.two_two hf.aemeasurable
    (show AEMeasurable (fun y => f (y * x)) σ from (by fun_prop))
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  rw [lintegral_mul_right_eq_self (μ := σ) (fun y => f y ^ 2) x] at h
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one] at h
  exact h

end TransposeFollowup

namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mobiusSmoothedAutocorrelation_le_one (μ : Measure Group) [SFinite μ] (η : ℝ) (x : Group) :
    mobiusSmoothedAutocorrelation μ η x ≤ mobiusSmoothedAutocorrelation μ η 1 :=
  autocorrelationDensity_le_one Measure.haar (mobiusSmoothedDensity_measurable μ η) x

theorem mobiusSmoothedAutocorrelation_one_toReal (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) :
    (mobiusSmoothedAutocorrelation μ η 1).toReal =
      ∫ x, (mobiusSmoothedDensity μ η x).toReal ^ 2 ∂(Measure.haar : Measure Group) := by
  rw [mobiusSmoothedAutocorrelation_one,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => sq_nonneg _))
      ((mobiusSmoothedDensity_measurable μ η).ennreal_toReal.pow_const 2).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (mobiusSmoothedDensity_lt_top μ hη x).ne]

end TransposeFollowup.RealMobius
