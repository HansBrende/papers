import TransposeFollowup.MobiusApproximateFromEnergy
import TransposeFollowup.MobiusSetEnergyRegularization
import TransposeFollowup.MeasureOverlapTransfer

/-! Approximate-group concentration for the original measurable level.
Regularization is chosen after the energy loss, so its added volume
cannot consume the selected overlap. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_approximate_group_from_measurable_self_energy {D : Set Group} {R : ℝ}
    (hD : MeasurableSet D) (hDs : ∀ x, x⁻¹ ∈ D ↔ x ∈ D)
    (hae : (D ∩ matrixEntryBox R) =ᵐ[(Measure.haar : Measure Group)] D)
    (hD0 : 0 < (Measure.haar : Measure Group) D) (hDt : (Measure.haar : Measure Group) D < ⊤)
    {L₀ : ℝ≥0∞} (hL₀one : 1 ≤ L₀) (hL₀t : L₀ ≠ ⊤)
    (hE : ((Measure.haar : Measure Group) D) ^ 3 ≤ L₀ * haarMultiplicativeEnergy Measure.haar D D) :
    let H : Measure Group := Measure.haar
    let L := 8 * L₀
    let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
    ∃ (U : Set Group) (Y : Finset Group) (x : Group),
      1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
      closure U ⊆ matrixEntryBox (32 * (R + 1) ^ 6) ∧ 0 < H U ∧ H U < ⊤ ∧
      H D ≤ 128 * K * L ^ 2 * H U ∧ H U ≤ 16 * K ^ 7 * H D ∧
      (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
      (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
      IsApproximateSubgroup (512 * K ^ 16).toReal U ∧
      x ∈ matrixEntryBox (R + 1) ∧ H D ≤ 512 * L ^ 2 * K ^ 4 * H (D ∩ x • U) := by
  let H : Measure Group := Measure.haar
  let L := 8 * L₀
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let M := 256 * L ^ 2 * K ^ 4
  have hLone : 1 ≤ L := by
    calc
      (1 : ℝ≥0∞) ≤ 8 * 1 := by norm_num
      _ ≤ 8 * L₀ := mul_le_mul' le_rfl hL₀one
  have hLt : L ≠ ⊤ := by finiteness
  have hKone : 1 ≤ K := by
    calc
      (1 : ℝ≥0∞) ≤ 2 ^ 55 * 1 ^ 21 := by norm_num
      _ ≤ 2 ^ 55 * L ^ 21 := mul_le_mul' le_rfl (pow_le_pow_left' hLone 21)
  have hKt : K ≠ ⊤ := by finiteness
  have hMone : 1 ≤ M := by
    calc
      (1 : ℝ≥0∞) ≤ 256 * 1 ^ 2 * 1 ^ 4 := by norm_num
      _ ≤ 256 * L ^ 2 * K ^ 4 := mul_le_mul'
        (mul_le_mul' le_rfl (pow_le_pow_left' hLone 2)) (pow_le_pow_left' hKone 4)
  have hM0 : M ≠ 0 := (lt_of_lt_of_le zero_lt_one hMone).ne'
  have hMt : M ≠ ⊤ := by finiteness
  have hden0 : 2 * M ≠ 0 := by positivity
  have hdent : 2 * M ≠ ⊤ := by finiteness
  let ε := H D / (2 * M)
  have hε : 0 < ε := ENNReal.div_pos hD0.ne' hdent
  have hεle : ε ≤ H D := by
    apply (ENNReal.div_le_iff hden0 hdent).mpr
    calc
      H D = H D * 1 := (mul_one _).symm
      _ ≤ H D * (2 * M) := mul_le_mul' le_rfl
        ((by norm_num : (1 : ℝ≥0∞) ≤ 2 * 1).trans (mul_le_mul' le_rfl hMone))
  obtain ⟨O, hDO, _, hOo, _, _, hOb, hOl, hOu, hOE⟩ :=
    exists_symmetric_open_energy_superset_add hDs hae hD0 hDt hε
  have hOsub : O ⊆ matrixEntryBox (R + 1) := fun _ hx => hOb (subset_closure hx)
  have htwo : H O ≤ 2 * H D := by
    calc
      H O ≤ H D + ε := hOu
      _ ≤ H D + H D := add_le_add le_rfl hεle
      _ = _ := by ring
  have hratio : H O ^ 3 ≤ L * haarMultiplicativeEnergy H O O := by
    calc
      H O ^ 3 ≤ (2 * H D) ^ 3 := pow_le_pow_left' htwo 3
      _ = 8 * H D ^ 3 := by ring
      _ ≤ 8 * (L₀ * haarMultiplicativeEnergy H D D) := mul_le_mul' le_rfl hE
      _ ≤ 8 * (L₀ * haarMultiplicativeEnergy H O O) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hOE)
      _ = L * haarMultiplicativeEnergy H O O := by dsimp only [L]; ring
  obtain ⟨_, U, Y, _, x, _, _, _, _, _, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hUlo, hUhi, hYs, hYi, hYcard, hYcov, happrox, _, _, _, _, hxO, hover⟩ :=
    exists_approximate_group_from_self_energy hOo hOsub (hD0.trans_le hOl) hLone hLt hratio
  have htail : 2 * (M * ε) ≤ H D := by
    calc
      2 * (M * ε) = (2 * M) * ε := by ring
      _ ≤ H D := (ENNReal.mul_div_cancel hden0 hdent).le
  have hlarge : H D ≤ 2 * M * H (D ∩ x • U) := measure_overlap_survives_enlargement H
    (hD.inter (matrixEntryBox_isCompact R).isClosed.measurableSet) hae hDO hDt.ne
    hOu htail (hOl.trans hover)
  refine ⟨U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt, hOl.trans hUlo, ?_,
    hYs, hYi, hYcard, hYcov, happrox, hOsub hxO, ?_⟩
  · calc
      H U ≤ 8 * K ^ 7 * H O := hUhi
      _ ≤ 8 * K ^ 7 * (2 * H D) := mul_le_mul' le_rfl htwo
      _ = _ := by ring
  · simpa only [M, show (2 : ℝ≥0∞) * (256 * L ^ 2 * K ^ 4) = 512 * L ^ 2 * K ^ 4 by ring] using hlarge

end TransposeFollowup.RealMobius
