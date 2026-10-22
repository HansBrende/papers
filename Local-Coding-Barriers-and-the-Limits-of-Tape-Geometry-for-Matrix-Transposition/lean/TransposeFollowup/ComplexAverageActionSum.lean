import TransposeFollowup.MobiusSchwartzL2Derivative

/-! Linearity of complexification in the operator, and the exact finite
action-sum formula for the symmetric average on a Schwartz input. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
open RealMobius
set_option autoImplicit false

theorem complexifyL2_zero : complexifyL2 (0 : RealL2 →L[ℝ] RealL2) = 0 := by
  ext1 f
  simp [complexifyL2_apply]

theorem complexifyL2_add (S T : RealL2 →L[ℝ] RealL2) :
    complexifyL2 (S + T) = complexifyL2 S + complexifyL2 T := by
  ext1 f
  simp only [complexifyL2_apply, add_apply, map_add, smul_add]
  abel

theorem complexifyL2_smul (r : ℝ) (T : RealL2 →L[ℝ] RealL2) :
    complexifyL2 (r • T) = r • complexifyL2 T := by
  ext1 f
  simp only [complexifyL2_apply, smul_apply, map_smul, smul_add]
  rw [smul_comm Complex.I r]

theorem complexifyL2_sum {ι : Type*} (s : Finset ι) (T : ι → RealL2 →L[ℝ] RealL2) :
    complexifyL2 (∑ i ∈ s, T i) = ∑ i ∈ s, complexifyL2 (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, complexifyL2_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, complexifyL2_add, ih]

namespace RealMobius

theorem complexAverage_schwartz_apply {c : ℕ} (G : Fin c → Group) (u : 𝓢(ℝ, ℂ)) :
    complexAverage G (u.toLp 2 volume) = (2 * (c : ℝ))⁻¹ •
      ∑ i : Fin c, (schwartzActionL2 (G i) u + schwartzActionL2 (G i)⁻¹ u) := by
  unfold complexAverage averageOperator
  rw [complexifyL2_smul, complexifyL2_sum]
  simp only [smul_apply, sum_apply, complexifyL2_add,
    add_apply, schwartzActionL2, inv_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact add_comm _ _

theorem complexAverage_schwartz_inner_abs_le {c : ℕ} (G : Fin c → Group)
    (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) :
    |inner ℝ (complexAverage G (u.toLp 2 volume)) v| ≤ (2 * (c : ℝ))⁻¹ *
      ∑ i : Fin c, (|inner ℝ (schwartzActionL2 (G i) u) v| +
        |inner ℝ (schwartzActionL2 (G i)⁻¹ u) v|) := by
  rw [complexAverage_schwartz_apply, real_inner_smul_left, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (2 * (c : ℝ))⁻¹), sum_inner]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [inner_add_left]
  exact abs_add_le _ _

end RealMobius
end TransposeFollowup
