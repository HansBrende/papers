import TransposeFollowup.MobiusPopularCore

/-! Compose small-product BSG, Ruzsa and popular overlap to obtain
a symmetric core directly from the original bounded self-energy input. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_symmetric_core_from_self_energy {O : Set Group} {Q : ℝ}
    (hO : IsOpen O) (hOb : O ⊆ matrixEntryBox Q) (hO0 : 0 < (Measure.haar : Measure Group) O)
    {L : ℝ≥0∞} (hLone : 1 ≤ L) (hLt : L ≠ ⊤)
    (hE : ((Measure.haar : Measure Group) O) ^ 3 ≤ L * haarMultiplicativeEnergy Measure.haar O O) :
    let H : Measure Group := Measure.haar
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    ∃ A T : Set Group, A ⊆ O ∧ IsOpen A ∧ IsCompact (closure A) ∧ closure A ⊆ matrixEntryBox Q ∧
      0 < H A ∧ H A < ⊤ ∧ H O ≤ 64 * L ^ 2 * H A ∧ H (A * A⁻¹) ≤ K * H A ∧
      1 ∈ T ∧ IsOpen T ∧ (∀ x, x⁻¹ ∈ T ↔ x ∈ T) ∧
      IsCompact (closure T) ∧ closure T ⊆ matrixEntryBox (2 * Q ^ 2) ∧
      0 < H T ∧ H T < ⊤ ∧ H A ≤ 2 * K * H T ∧ H T ≤ 2 * K * H A ∧
      H O ≤ (2 : ℝ≥0∞) ^ 62 * L ^ 23 * H T ∧ H T ≤ (2 : ℝ≥0∞) ^ 56 * L ^ 21 * H O ∧
      (∀ n : ℕ, H (A * T ^ n * A⁻¹) ≤ 2 ^ n * K ^ (2 * n + 1) * H A) ∧
      H (A * T) ≤ 2 * K ^ 3 * H A ∧ H (T ^ 3) ≤ 16 * K ^ 8 * H T := by
  let H : Measure Group := Measure.haar
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  have hOt : H O < ⊤ := (measure_mono hOb).trans_lt (matrixEntryBox_isCompact Q).measure_lt_top
  obtain ⟨A, B, hAO, _, hAo, hBo, hAc, _, hAb, _, hA0, hAt, _, _, hAv, hBv, hABv, _, _⟩ :=
    exists_small_product_from_self_energy hO hOb hO0 hLone hLt hE
  have hKone : 1 ≤ K := by
    have hp : (1 : ℝ≥0∞) ≤ L ^ 21 := by simpa only [one_pow] using pow_le_pow_left' hLone 21
    simpa only [one_mul] using mul_le_mul' (by norm_num : (1 : ℝ≥0∞) ≤ 2 ^ 55) hp
  have hKt : K ≠ ⊤ := by finiteness
  have hru : H (A * A⁻¹) * H B ≤ H (A * B) ^ 2 :=
    haar_ruzsa_product_bound H hBo.measurableSet
      hAo.mul_right.measurableSet hAo.mul_right.measurableSet
  have hsmall : H (A * A⁻¹) ≤ K * H A := by
    apply (ENNReal.mul_le_mul_iff_right hO0.ne' hOt.ne).mp
    calc
      H O * H (A * A⁻¹) ≤ (8 * L * H B) * H (A * A⁻¹) := mul_le_mul' hBv le_rfl
      _ = (8 * L) * (H (A * A⁻¹) * H B) := by ring
      _ ≤ (8 * L) * H (A * B) ^ 2 := mul_le_mul' le_rfl hru
      _ ≤ (8 * L) * (8388608 * L ^ 9 * H O) ^ 2 := mul_le_mul' le_rfl (pow_le_pow_left' hABv 2)
      _ = H O * ((2 : ℝ≥0∞) ^ 49 * L ^ 19 * H O) := by ring
      _ ≤ H O * ((2 : ℝ≥0∞) ^ 49 * L ^ 19 * (64 * L ^ 2 * H A)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hAv)
      _ = H O * (K * H A) := by dsimp only [K]; ring
  obtain ⟨hT1, hTo, hTs, hTc, hTb, hT0, hTt, hTlow, hTup, hsand, hAT, hT3⟩ :=
    popular_overlap_core hAo (fun _ hx => hAb (subset_closure hx)) hA0 hKone hKt hsmall
  let T := popularProductSet H A⁻¹ A (H A / (2 * K))
  refine ⟨A, T, hAO, hAo, hAc, hAb, hA0, hAt, hAv, hsmall, hT1, hTo, hTs,
    hTc, hTb, hT0, hTt, hTlow, hTup, ?_, ?_, hsand, hAT, hT3⟩
  · calc
      H O ≤ 64 * L ^ 2 * H A := hAv
      _ ≤ 64 * L ^ 2 * (2 * K * H T) := mul_le_mul' le_rfl hTlow
      _ = _ := by dsimp only [K]; ring
  · calc
      H T ≤ 2 * K * H A := hTup
      _ ≤ 2 * K * H O := mul_le_mul' le_rfl (measure_mono hAO)
      _ = _ := by dsimp only [K]; ring

end TransposeFollowup.RealMobius
