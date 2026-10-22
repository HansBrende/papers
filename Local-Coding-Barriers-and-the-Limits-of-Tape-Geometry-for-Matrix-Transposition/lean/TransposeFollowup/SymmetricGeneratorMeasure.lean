import TransposeFollowup.MobiusGroupSmoothing
import TransposeFollowup.ComplexAverageActionSum

/-! The actual symmetric generator probability measure and its equality
with the previously constructed finite complex average. Multiplicities
are retained when generators repeat. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group]

noncomputable def symmetricGeneratorMeasure {c : ℕ} (G : Fin c → Group) : Measure Group :=
  ((2 * c : ℕ) : ℝ≥0∞)⁻¹ • ∑ i : Fin c, (Measure.dirac (G i) + Measure.dirac (G i)⁻¹)

theorem symmetricGeneratorMeasure_probability {c : ℕ} (G : Fin c → Group) (hc : 0 < c) :
    IsProbabilityMeasure (symmetricGeneratorMeasure G) := by
  constructor
  have hne : (2 * c : ℕ) ≠ 0 := by omega
  have hm : (∑ i : Fin c, (Measure.dirac (G i) + Measure.dirac (G i)⁻¹)) univ =
      ((2 * c : ℕ) : ℝ≥0∞) := by
    simp [two_mul]
  rw [symmetricGeneratorMeasure, Measure.smul_apply, hm, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hne) (ENNReal.natCast_ne_top _)

variable [BorelSpace Group]

theorem groupActionAverage_symmetricGeneratorMeasure {c : ℕ} (G : Fin c → Group) (f : ComplexL2) :
    groupActionAverage (symmetricGeneratorMeasure G) f = complexAverage G f := by
  unfold groupActionAverage symmetricGeneratorMeasure
  rw [integral_smul_measure, integral_finsetSum_measure
    (fun i _ => integrable_complexPullbackL2_inverse (Measure.dirac (G i) + Measure.dirac (G i)⁻¹) f)]
  simp_rw [integral_add_measure (integrable_complexPullbackL2_inverse (Measure.dirac _) f)
    (integrable_complexPullbackL2_inverse (Measure.dirac _) f), integral_dirac]
  simp only [ENNReal.toReal_inv, Nat.cast_mul, Nat.cast_ofNat, inv_inv]
  unfold complexAverage averageOperator
  rw [complexifyL2_smul, complexifyL2_sum]
  simp only [smul_apply, sum_apply, complexifyL2_add, add_apply, complexPullbackL2, inv_inv]
  congr 1

end TransposeFollowup.RealMobius
