import TransposeFollowup.HaarSmoothingOverlap
import TransposeFollowup.HaarLocalPacking
import TransposeFollowup.MobiusLocalCoverGeometry

/-! Probability concentration after Haar-ball smoothing gives a finite
cover by controlled identity-ball translates. No thickness is assumed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_finite_cover_of_smoothed_concentration (ν : Measure Group)
    [IsProbabilityMeasure ν] {η Q : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (hQ : 0 < Q)
    {U : Set Group} (hU : MeasurableSet U) (hUb : U ⊆ matrixEntryBox Q)
    (hUt : (Measure.haar : Measure Group) U < ⊤) (Y : Finset Group)
    {c : ℝ≥0∞} (hct : c ≠ ⊤) (hY : (Y.card : ℝ≥0∞) ≤ c)
    (hcover : U ^ 2 ⊆ (Y : Set Group) * U) (x : Group)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hpt : p ≠ ⊤)
    (hp : p ≤ (ν ∗ₘ mobiusHaarKernel η) (x • U)) :
    ∃ F : Finset Group, (F : Set Group) ⊆ U ∧
      (F.card : ℝ≥0∞) * p * (Measure.haar : Measure Group) (mobiusIdentityBall η) ≤
        2 * c * (Measure.haar : Measure Group) U ∧
      U ⊆ (F : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η) := by
  let H : Measure Group := Measure.haar
  let S := mobiusIdentityBall η
  have hS := (mobiusIdentityBall_isOpen η).measurableSet
  have hS0 := mobiusIdentityBall_haar_pos hη
  have hSt := mobiusIdentityBall_haar_lt_top hη
  obtain ⟨g, hg⟩ := exists_local_haar_overlap_of_smoothing H ν hS0 hSt
    (hU.const_smul x) hp0 hpt hp
  let T := U ∩ (x⁻¹ * g) • S
  have hT : MeasurableSet T := hU.inter (hS.const_smul _)
  have hTU : T ⊆ U := Set.inter_subset_left
  have heq : H ((x • U) ∩ g • S) = H T := by
    calc
      _ = H (x • T) := by
        congr 1
        dsimp only [T]
        rw [Set.smul_set_inter, smul_smul, mul_inv_cancel_left]
      _ = H T := measure_smul H x T
  have hlocal : p * H S ≤ 2 * H T := by rwa [heq] at hg
  have hn : T.Nonempty := by
    apply nonempty_of_measure_ne_zero
    intro hz
    rw [hz, mul_zero] at hlocal
    exact (not_le_of_gt (ENNReal.mul_pos hp0.ne' hS0.ne')) hlocal
  have hsmall : H (U ^ 2) ≤ c * H U :=
    (measure_le_of_finite_left_cover H Y hcover).trans (mul_le_mul' hY le_rfl)
  obtain ⟨F, hF, hcard, hpack⟩ := exists_finite_cover_from_local_volume H hT hTU hUt hct
    (ENNReal.mul_pos hp0.ne' hS0.ne') hlocal hsmall
  refine ⟨F, hF, ?_, ?_⟩
  · simpa only [mul_assoc] using hcard
  · calc
      U ⊆ (F : Set Group) * T * T⁻¹ := hpack
      _ = (F : Set Group) * (T * T⁻¹) := mul_assoc _ _ _
      _ ⊆ (F : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η) := Set.mul_subset_mul le_rfl
        (local_piece_quotients_in_identityBall hQ hη hηone hUb hn)

end TransposeFollowup.RealMobius
