import TransposeFollowup.FiniteTranslateCover
import TransposeFollowup.MobiusApproximateRefinement
import TransposeFollowup.MobiusNearIdentityLocalization

/-! Fixed powers of the actual approximate-group witness are covered
by finitely many bounded translates of its localized set. This retains
the native covering radius and explicit polynomial costs. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem coveringNumber_power_le_localized {U A : Set G} (Y Z : Finset G) (n : ℕ)
    {Q B : ℝ} {η : ℝ≥0} (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hη : 0 < η)
    (hU : U ⊆ matrixEntryBox Q) (hA : A ⊆ matrixEntryBox B)
    (hY : (Y : Set G) ⊆ U ^ 2) (hZ : (Z : Set G) ⊆ U)
    (hdouble : U ^ 2 ⊆ (Y : Set G) * U) (hcover : U ⊆ (Z : Set G) * A) :
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (U ^ (n + 1))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (U ^ (n + 1))) : ℝ≥0∞).toReal ≤
        (8 * (2 * Q) ^ (2 * n + 1) + 1) ^ 4 * (Y.card : ℝ) ^ n * (Z.card : ℝ) *
          (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  let W : Finset G := Y ^ n * Z
  have hW : (W : Set G) ⊆ U ^ (2 * n + 1) := by
    simp only [W, Finset.coe_mul, Finset.coe_pow]
    calc
      _ ⊆ (U ^ 2) ^ n * U := Set.mul_subset_mul (Set.pow_subset_pow_left hY) hZ
      _ = _ := by rw [← pow_mul, ← pow_succ]
  have hWcard : W.card ≤ Y.card ^ n * Z.card :=
    (Finset.card_mul_le (s := Y ^ n) (t := Z)).trans (Nat.mul_le_mul_right _ Finset.card_pow_le)
  have hpow : U ^ (n + 1) ⊆ (W : Set G) * A := by
    calc
      _ ⊆ (Y : Set G) ^ n * U := by
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
          Set.pow_subset_pow_mul_of_sq_subset_mul hdouble (Nat.succ_ne_zero n)
      _ ⊆ (Y : Set G) ^ n * ((Z : Set G) * A) := Set.mul_subset_mul subset_rfl hcover
      _ = _ := by simp only [W, Finset.coe_mul, Finset.coe_pow, mul_assoc]
  obtain ⟨hAfin, hUfin, hbound⟩ := coveringNumber_le_finite_left_cover W
    (by positivity : 0 ≤ (2 * Q) ^ (2 * n + 1)) hB hη
    (fun w hw => matrixEntryBox_set_pow hU (2 * n + 1) (hW hw)) hA hpow
  have hWcardR : (W.card : ℝ) ≤ (Y.card : ℝ) ^ n * (Z.card : ℝ) := by exact_mod_cast hWcard
  refine ⟨hAfin, hUfin, hbound.trans ?_⟩
  calc
    _ ≤ (8 * (2 * Q) ^ (2 * n + 1) + 1) ^ 4 * ((Y.card : ℝ) ^ n * (Z.card : ℝ)) *
        (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWcardR (by positivity)) ENNReal.toReal_nonneg
    _ = _ := by ring

theorem localized_power_coveringNumber {U : Set G} (Y : Finset G) (n : ℕ)
    {Q α : ℝ} {η : ℝ≥0} (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1) (hη : 0 < η)
    (hU : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U)
    (hY : (Y : Set G) ⊆ U ^ 2) (hdouble : U ^ 2 ⊆ (Y : Set G) * U) :
    let A := U ^ 2 ∩ mobiusIdentityBall α
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (U ^ (n + 1))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (U ^ (n + 1))) : ℝ≥0∞).toReal ≤
        (8 * (2 * Q) ^ (2 * n + 1) + 1) ^ 4 * (Y.card : ℝ) ^ n *
          (33 ^ 4 * Q ^ 8 / α ^ 4) *
            (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  let A := U ^ 2 ∩ mobiusIdentityBall α
  obtain ⟨Z, hZ, hZcard, hcover⟩ := exists_near_identity_translate_cover hQ hα hαone hU hUi
  have hAb : A ⊆ matrixEntryBox 2 :=
    Set.inter_subset_right.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  obtain ⟨hAfin, hUfin, hbound⟩ := coveringNumber_power_le_localized Y Z n
    (by linarith : 0 ≤ Q) (by norm_num : (0 : ℝ) ≤ 2) hη hU hAb hY hZ hdouble hcover
  have hM : 0 ≤ 33 ^ 4 * Q ^ 8 / α ^ 4 := by positivity
  have hcard : (Z.card : ℝ) ≤ 33 ^ 4 * Q ^ 8 / α ^ 4 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZcard
    simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hM] using hh
  refine ⟨hAfin, hUfin, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity)) ENNReal.toReal_nonneg

theorem localized_set_pow_coveringNumber {U : Set G} (Y : Finset G) (n : ℕ)
    {Q α : ℝ} {η : ℝ≥0} (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1) (hη : 0 < η)
    (hU : U ⊆ matrixEntryBox Q) (hUi : U⁻¹ = U)
    (hY : (Y : Set G) ⊆ U ^ 2) (hdouble : U ^ 2 ⊆ (Y : Set G) * U) :
    let A := U ^ 2 ∩ mobiusIdentityBall α
    Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≠ ⊤ ∧
      Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ (n + 1))) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' (A ^ (n + 1))) : ℝ≥0∞).toReal ≤
        (8 * (2 * Q) ^ (4 * n + 3) + 1) ^ 4 * (Y.card : ℝ) ^ (2 * n + 1) *
          (33 ^ 4 * Q ^ 8 / α ^ 4) *
            (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  let A := U ^ 2 ∩ mobiusIdentityBall α
  obtain ⟨hAfin, hUfin, hbound⟩ := localized_power_coveringNumber Y (2 * n + 1) hQ hα hαone hη hU hUi hY hdouble
  have hsub : A ^ (n + 1) ⊆ U ^ (2 * n + 1 + 1) := by
    calc
      _ ⊆ (U ^ 2) ^ (n + 1) := Set.pow_subset_pow_left Set.inter_subset_left
      _ = _ := by rw [← pow_mul]; congr 1
  have hNle := Metric.externalCoveringNumber_mono_set (ε := η) (Set.image_mono (f := fun x : G => (x : RMat)) hsub)
  have hfin := ne_top_of_le_ne_top hUfin hNle
  have hreal := ENNReal.toReal_mono (ENat.toENNReal_ne_top.mpr hUfin) (ENat.toENNReal_mono hNle)
  refine ⟨hAfin, hfin, hreal.trans ?_⟩
  simpa only [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by omega] using hbound

end TransposeFollowup.SL2Projection
