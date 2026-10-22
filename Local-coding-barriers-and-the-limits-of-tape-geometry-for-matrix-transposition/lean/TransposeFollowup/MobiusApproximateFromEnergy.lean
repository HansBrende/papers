import TransposeFollowup.HaarApproximateCore
import TransposeFollowup.MobiusCoreFromEnergy

/-! An actual bounded approximate group and finite covers from self-energy.
The finite symmetric doubling witness lies inside the group's square,
and one translate retains a quantitatively large overlap with the input. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_approximate_group_from_self_energy {O : Set Group} {Q : ℝ}
    (hO : IsOpen O) (hOb : O ⊆ matrixEntryBox Q) (hO0 : 0 < (Measure.haar : Measure Group) O)
    {L : ℝ≥0∞} (hLone : 1 ≤ L) (hLt : L ≠ ⊤)
    (hE : ((Measure.haar : Measure Group) O) ^ 3 ≤ L * haarMultiplicativeEnergy Measure.haar O O) :
    let H : Measure Group := Measure.haar
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    ∃ (A U : Set Group) (Y W : Finset Group) (x : Group),
      A ⊆ O ∧ IsOpen A ∧ 0 < H A ∧ H A < ⊤ ∧ H O ≤ 64 * L ^ 2 * H A ∧
      1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
      closure U ⊆ matrixEntryBox (32 * Q ^ 6) ∧ 0 < H U ∧ H U < ⊤ ∧
      H O ≤ 128 * K * L ^ 2 * H U ∧ H U ≤ 8 * K ^ 7 * H O ∧
      (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
      (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
      IsApproximateSubgroup (512 * K ^ 16).toReal U ∧
      (W : Set Group) ⊆ A ∧ (W.card : ℝ≥0∞) ≤ 4 * K ^ 4 ∧ A ⊆ (W : Set Group) * U ∧
      x ∈ W ∧ x ∈ O ∧ H O ≤ 256 * L ^ 2 * K ^ 4 * H (O ∩ x • U) := by
  let H : Measure Group := Measure.haar
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  have hKt : K ≠ ⊤ := by finiteness
  obtain ⟨A, T, hAO, hAo, _, _, hA0, hAt, hAv, _, hT1, hTo, hTs, _, hTb,
      hT0, hTt, hTlow, _, _, _, hsand, hAT, _⟩ :=
    exists_symmetric_core_from_self_energy hO hOb hO0 hLone hLt hE
  have hAn : A.Nonempty := (hAo.measure_pos_iff H).mp hA0
  have hTi : T⁻¹ = T := by
    ext x
    exact (Set.mem_inv.trans (hTs x))
  let U := T ^ 3
  have hTsub : T ⊆ U := Set.subset_pow hT1 (by decide : (3 : ℕ) ≠ 0)
  have hpow : ∀ n : ℕ, H (T ^ n) ≤ 2 ^ n * K ^ (2 * n + 1) * H A := by
    intro n
    calc
      H (T ^ n) ≤ H (A * T ^ n) := haar_measure_le_left_product H hAn _
      _ ≤ H (A * T ^ n * A⁻¹) := haar_measure_le_right_product H _ hAn.inv
      _ ≤ _ := hsand n
  have h7 : H (T ^ 7) ≤ (256 * K ^ 16) * H T := by
    calc
      H (T ^ 7) ≤ 128 * K ^ 15 * H A := by
        simpa only [show (2 : ℝ≥0∞) ^ 7 = 128 by norm_num] using hpow 7
      _ ≤ 128 * K ^ 15 * (2 * K * H T) := mul_le_mul' le_rfl hTlow
      _ = _ := by ring
  obtain ⟨Y, hYsub, hYsym, hYcard, hYcover, happrox⟩ :=
    symmetric_cube_finite_cover H hTo.measurableSet hT1 hTi hT0 hTt
      (by finiteness : 256 * K ^ 16 ≠ ⊤) h7
  have heq : (2 : ℝ≥0∞) * (256 * K ^ 16) = 512 * K ^ 16 := by ring
  rw [heq] at hYcard happrox
  have hU1 : 1 ∈ U := Set.one_mem_pow hT1
  have hUo : IsOpen U := by
    change IsOpen (T ^ 3)
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two]
    exact hTo.mul_right.mul_right
  have hUi : U⁻¹ = U := by dsimp only [U]; rw [← inv_pow, hTi]
  have hUc : closure U ⊆ matrixEntryBox (32 * Q ^ 6) := by
    apply closure_minimal _ (matrixEntryBox_isCompact _).isClosed
    intro g hg
    change g ∈ T ^ 3 at hg
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two] at hg
    obtain ⟨ab, hab, c, hc, rfl⟩ := Set.mem_mul.mp hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hab
    have hm := matrixEntryBox_mul
      (matrixEntryBox_mul (hTb (subset_closure ha)) (hTb (subset_closure hb))) (hTb (subset_closure hc))
    simpa only [show 2 * (2 * (2 * Q ^ 2) * (2 * Q ^ 2)) * (2 * Q ^ 2) = 32 * Q ^ 6 by ring] using hm
  have hU0 : 0 < H U := hT0.trans_le (measure_mono hTsub)
  have hUupper : H U ≤ 8 * K ^ 7 * H A := by
    simpa only [show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num] using hpow 3
  have hUt : H U < ⊤ := hUupper.trans_lt (by finiteness)
  have hUlow : H O ≤ 128 * K * L ^ 2 * H U := by
    calc
      H O ≤ 64 * L ^ 2 * H A := hAv
      _ ≤ 64 * L ^ 2 * (2 * K * H T) := mul_le_mul' le_rfl hTlow
      _ ≤ 64 * L ^ 2 * (2 * K * H U) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hTsub))
      _ = _ := by ring
  have hATbound : H (A * T) ≤ (4 * K ^ 4) * H T := by
    calc
      H (A * T) ≤ 2 * K ^ 3 * H A := hAT
      _ ≤ 2 * K ^ 3 * (2 * K * H T) := mul_le_mul' le_rfl hTlow
      _ = _ := by ring
  obtain ⟨W, hWA, hWcard, hWcover⟩ := exists_finite_haar_translate_cover H
    hTo.measurableSet hT0 hTt (by finiteness : 4 * K ^ 4 ≠ ⊤) hATbound
  have hAW : A ⊆ (W : Set Group) * U := by
    calc
      A ⊆ (W : Set Group) * T * T⁻¹ := hWcover
      _ = (W : Set Group) * T ^ 2 := by rw [hTi, mul_assoc, pow_two]
      _ ⊆ (W : Set Group) * U := Set.mul_subset_mul le_rfl
        (Set.pow_subset_pow_right hT1 (by decide : 2 ≤ 3))
  obtain ⟨x, hx, hlarge⟩ := exists_large_overlap_of_finite_translate_cover H hAn hAO W hAW
  refine ⟨A, U, Y, W, x, hAO, hAo, hA0, hAt, hAv, hU1, hUo, hUi,
    (matrixEntryBox_isCompact _).of_isClosed_subset isClosed_closure hUc, hUc, hU0, hUt,
    hUlow, hUupper.trans (mul_le_mul' le_rfl (measure_mono hAO)), hYsub, hYsym, hYcard, hYcover,
    happrox, hWA, hWcard, hAW, hx, hAO (hWA hx), ?_⟩
  calc
    H O ≤ 64 * L ^ 2 * H A := hAv
    _ ≤ 64 * L ^ 2 * ((W.card : ℝ≥0∞) * H (O ∩ x • U)) := mul_le_mul' le_rfl hlarge
    _ ≤ 64 * L ^ 2 * ((4 * K ^ 4) * H (O ∩ x • U)) := mul_le_mul' le_rfl (mul_le_mul' hWcard le_rfl)
    _ = _ := by ring

end TransposeFollowup.RealMobius
