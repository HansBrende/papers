import TransposeFollowup.MobiusProductTrimming

/-! Continuous small-product BSG for bounded open SL2 sets.
The conservative explicit polynomial is sufficient for the subsequent
growth argument; no optimal-constant or novelty claim is made. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_small_product_from_self_energy {O : Set Group} {Q : ℝ}
    (hO : IsOpen O) (hOb : O ⊆ matrixEntryBox Q) (hO0 : 0 < (Measure.haar : Measure Group) O)
    {L : ℝ≥0∞} (hLone : 1 ≤ L) (hLt : L ≠ ⊤)
    (hE : ((Measure.haar : Measure Group) O) ^ 3 ≤ L * haarMultiplicativeEnergy Measure.haar O O) :
    let H : Measure Group := Measure.haar
    ∃ A B : Set Group, A ⊆ O ∧ B ⊆ O ∧ IsOpen A ∧ IsOpen B ∧
      IsCompact (closure A) ∧ IsCompact (closure B) ∧
      closure A ⊆ matrixEntryBox Q ∧ closure B ⊆ matrixEntryBox Q ∧
      0 < H A ∧ H A < ⊤ ∧ 0 < H B ∧ H B < ⊤ ∧
      H O ≤ 64 * L ^ 2 * H A ∧ H O ≤ 8 * L * H B ∧
      H (A * B) ≤ 8388608 * L ^ 9 * H O ∧
      IsCompact (closure (A * B)) ∧ closure (A * B) ⊆ matrixEntryBox (2 * Q ^ 2) := by
  let H : Measure Group := Measure.haar
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hOt : H O < ⊤ := (measure_mono hOb).trans_lt (matrixEntryBox_isCompact Q).measure_lt_top
  let C := popularProductSet H O O (H O / (2 * L))
  obtain ⟨_, hCo, _, hCc, _, _, hCv, hpair⟩ := popularProductSet_geometry hO hOb hO0 hOt hL hLt hE
  have hCb : C ⊆ matrixEntryBox (2 * Q ^ 2) := fun _ hx => hCc (subset_closure hx)
  let Ahi := O ∩ {a | H O / (4 * L) < relationRowDegree (H.restrict O) (productIncidence C) a}
  obtain ⟨hAho, hAh0, hAhsize, hAhdense⟩ := high_product_degree_rows hO hCo hO0 hOt hL hLt hpair
  have hAhO : Ahi ⊆ O := inter_subset_left
  let ε : ℝ≥0∞ := 1 / (64 * L)
  have hε0 : 0 < ε := ENNReal.div_pos (by norm_num) (by finiteness)
  have hεcancel : (64 * L) * ε = 1 := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hεone : ε ≤ 1 := by
    apply (ENNReal.mul_le_mul_iff_right (by positivity : 64 * L ≠ 0) (by finiteness)).mp
    rw [hεcancel, mul_one]
    calc
      (1 : ℝ≥0∞) ≤ 64 * 1 := by norm_num
      _ ≤ 64 * L := mul_le_mul' le_rfl hLone
  obtain ⟨b, _, hSAh, _, hSo, _, _, hS0, hSt, hsize, _, hDo, _, _, _, _, hDvol, hbad⟩ :=
    exists_weakBSG_productFiber hAho hO hCo (hAhO.trans hOb) hOb hCb hAh0 hO0
      (by positivity : 0 < 4 * L) (by finiteness : 4 * L ≠ ⊤) hε0 hεone hAhdense
  let S := productFiber Ahi C b
  let D := popularProductSet H C C⁻¹ (ε * H O / (2 * (4 * L) ^ 2))
  have hSsize : H O ≤ 32 * L ^ 2 * H S := by
    have hlin : H Ahi < 8 * L * H S := by
      by_contra hn
      have hh := pow_le_pow_left' (le_of_not_gt hn) 2
      have heq : (8 * L * H S) ^ 2 = 4 * (4 * L) ^ 2 * H S ^ 2 := by ring
      rw [heq] at hh
      exact (not_le_of_gt hsize) hh
    calc
      H O ≤ 4 * L * H Ahi := hAhsize
      _ ≤ 4 * L * (8 * L * H S) := mul_le_mul' le_rfl hlin.le
      _ = _ := by ring
  have hDsize : H D ≤ 8192 * L ^ 5 * H O := by
    have hh : ε * H D ≤ 128 * L ^ 4 * H O := by
      apply (ENNReal.mul_le_mul_iff_right hO0.ne' hOt.ne).mp
      calc
        H O * (ε * H D) = ε * H O * H D := by ring
        _ ≤ 2 * (4 * L) ^ 2 * H C ^ 2 := hDvol
        _ ≤ 2 * (4 * L) ^ 2 * (2 * L * H O) ^ 2 := mul_le_mul' le_rfl (pow_le_pow_left' hCv 2)
        _ = H O * (128 * L ^ 4 * H O) := by ring
    calc
      H D = (64 * L) * (ε * H D) := by rw [← mul_assoc, hεcancel, one_mul]
      _ ≤ (64 * L) * (128 * L ^ 4 * H O) := mul_le_mul' le_rfl hh
      _ = _ := by ring
  have hbadscaled : 64 * L * (H.prod H)
      {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} ≤ H S ^ 2 := by
    calc
      _ ≤ (64 * L) * (ε * H S ^ 2) := mul_le_mul' le_rfl hbad.le
      _ = _ := by rw [← mul_assoc, hεcancel, one_mul]
  obtain ⟨A, B, hAS, hBO, hAo, hBo, hAsize, hBsize, hprod⟩ :=
    exists_open_product_trim hO hSo hCo hDo hOt hS0 hSt hLone hLt
      (fun a ha => (hSAh ha).2) hbadscaled
  have hAO : A ⊆ O := hAS.trans (hSAh.trans hAhO)
  have hAc : closure A ⊆ matrixEntryBox Q :=
    closure_minimal (hAO.trans hOb) (matrixEntryBox_isCompact Q).isClosed
  have hBc : closure B ⊆ matrixEntryBox Q :=
    closure_minimal (hBO.trans hOb) (matrixEntryBox_isCompact Q).isClosed
  have hAv : H O ≤ 64 * L ^ 2 * H A := calc
    H O ≤ 32 * L ^ 2 * H S := hSsize
    _ ≤ 32 * L ^ 2 * (2 * H A) := mul_le_mul' le_rfl hAsize
    _ = _ := by ring
  have hA0 : 0 < H A := by
    by_contra hn
    have hz : H A = 0 := le_antisymm (le_of_not_gt hn) zero_le
    rw [hz, mul_zero] at hAv
    exact (not_le_of_gt hO0) hAv
  have hB0 : 0 < H B := by
    by_contra hn
    have hz : H B = 0 := le_antisymm (le_of_not_gt hn) zero_le
    rw [hz, mul_zero] at hBsize
    exact (not_le_of_gt hO0) hBsize
  have hPc : closure (A * B) ⊆ matrixEntryBox (2 * Q ^ 2) := by
    apply closure_minimal _ (matrixEntryBox_isCompact _).isClosed
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    simpa only [pow_two, mul_assoc] using matrixEntryBox_mul (hOb (hAO ha)) (hOb (hBO hb))
  refine ⟨A, B, hAO, hBO, hAo, hBo,
    (matrixEntryBox_isCompact Q).of_isClosed_subset isClosed_closure hAc,
    (matrixEntryBox_isCompact Q).of_isClosed_subset isClosed_closure hBc,
    hAc, hBc, hA0, (measure_mono hAO).trans_lt hOt, hB0, (measure_mono hBO).trans_lt hOt,
    hAv, hBsize, ?_, (matrixEntryBox_isCompact _).of_isClosed_subset isClosed_closure hPc, hPc⟩
  apply (ENNReal.mul_le_mul_iff_right hO0.ne' hOt.ne).mp
  calc
    H O * H (A * B) ≤ (32 * L ^ 2 * H S) * H (A * B) := mul_le_mul' hSsize le_rfl
    _ = (32 * L ^ 2) * (H S * H (A * B)) := by ring
    _ ≤ (32 * L ^ 2) * (16 * L * H D * H C) := mul_le_mul' le_rfl hprod
    _ ≤ (32 * L ^ 2) * (16 * L * (8192 * L ^ 5 * H O) * (2 * L * H O)) :=
      mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hDsize) hCv)
    _ = H O * (8388608 * L ^ 9 * H O) := by ring

end TransposeFollowup.RealMobius
