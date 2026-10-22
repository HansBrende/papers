import TransposeFollowup.ProductQuotientControl
import TransposeFollowup.MobiusPopularProducts

/-! Continuous weak BSG with explicit SL2 entry bounds. A large open
fiber has few exceptional quotients, and the controlling region is
nonempty open precompact with polynomial volume loss. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_weakBSG_productFiber {A B C : Set Group} {QA QB QC : ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C)
    (hAb : A ⊆ matrixEntryBox QA) (hBb : B ⊆ matrixEntryBox QB) (hCb : C ⊆ matrixEntryBox QC)
    (hA0 : 0 < (Measure.haar : Measure Group) A) (hB0 : 0 < (Measure.haar : Measure Group) B)
    {K ε : ℝ≥0∞} (hK : 0 < K) (hKt : K ≠ ⊤) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hdense : (Measure.haar : Measure Group) A * (Measure.haar : Measure Group) B ≤
      K * ((Measure.haar : Measure Group).prod Measure.haar)
        {p : Group × Group | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 ∈ C}) :
    let H : Measure Group := Measure.haar
    let t := ε * H B / (2 * K ^ 2)
    let D := popularProductSet H C C⁻¹ t
    ∃ b ∈ B, let S := productFiber A C b
      S ⊆ A ∧ S.Nonempty ∧ IsOpen S ∧ IsCompact (closure S) ∧ closure S ⊆ matrixEntryBox QA ∧
      0 < H S ∧ H S < ⊤ ∧ H A ^ 2 < 4 * K ^ 2 * H S ^ 2 ∧
      D.Nonempty ∧ IsOpen D ∧ IsCompact (closure D) ∧ closure D ⊆ matrixEntryBox (2 * QC ^ 2) ∧
      0 < H D ∧ H D < ⊤ ∧ ε * H B * H D ≤ 2 * K ^ 2 * H C ^ 2 ∧
      (H.prod H) {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} < ε * H S ^ 2 := by
  let H : Measure Group := Measure.haar
  let t := ε * H B / (2 * K ^ 2)
  let D := popularProductSet H C C⁻¹ t
  have hAt : H A < ⊤ := (measure_mono hAb).trans_lt (matrixEntryBox_isCompact QA).measure_lt_top
  have hBt : H B < ⊤ := (measure_mono hBb).trans_lt (matrixEntryBox_isCompact QB).measure_lt_top
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top (by simp) hεone
  obtain ⟨b, hb, hsize, hbad, hvol⟩ := exists_productFiber_quotient_control H
    hB.measurableSet hC.measurableSet hA0 hAt hB0 hBt hK hKt hε hεt hdense
  let S := productFiber A C b
  have hSA : S ⊆ A := inter_subset_left
  have hSo : IsOpen S := hA.inter (hC.preimage (by fun_prop))
  have hS0 : 0 < H S := by
    by_contra hn
    have hz : H S = 0 := le_antisymm (le_of_not_gt hn) zero_le
    change H A ^ 2 < 4 * K ^ 2 * H S ^ 2 at hsize
    simp only [hz, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, not_lt_zero] at hsize
  have hSc : closure S ⊆ matrixEntryBox QA :=
    closure_minimal (hSA.trans hAb) (matrixEntryBox_isCompact QA).isClosed
  have hCi : C⁻¹ ⊆ matrixEntryBox QC := by
    intro x hx
    have hxi : x⁻¹ ∈ C := by simpa only [Set.mem_inv] using hx
    exact (matrixEntryBox_inv_iff QC x).mp (hCb hxi)
  have hDb : D ⊆ matrixEntryBox (2 * QC ^ 2) := by
    simpa only [pow_two, mul_assoc] using popularProductSet_subset_entryBox hCb hCi t
  have hDc : closure D ⊆ matrixEntryBox (2 * QC ^ 2) :=
    closure_minimal hDb (matrixEntryBox_isCompact _).isClosed
  have hDo : IsOpen D := popularProductSet_isOpen H hC.measurableSet hC.inv t
  have hDn : D.Nonempty := by
    by_contra hn
    have hz : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have heq : {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} = S ×ˢ S := by
      ext p
      simp only [hz, Set.mem_ofPred_eq, Set.notMem_empty, not_false_eq_true, and_true, Set.mem_prod]
    have hh : H S ^ 2 < ε * H S ^ 2 := by
      change (H.prod H) {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} < ε * H S ^ 2 at hbad
      rw [heq, Measure.prod_prod] at hbad
      simpa only [pow_two] using hbad
    have hle : ε * H S ^ 2 ≤ H S ^ 2 := by
      simpa only [one_mul] using mul_le_mul' hεone (le_refl (H S ^ 2))
    exact (not_lt_of_ge hle) hh
  refine ⟨b, hb, hSA, (hSo.measure_pos_iff H).mp hS0, hSo,
    (matrixEntryBox_isCompact QA).of_isClosed_subset isClosed_closure hSc, hSc,
    hS0, (measure_mono hSA).trans_lt hAt, hsize, hDn, hDo,
    (matrixEntryBox_isCompact _).of_isClosed_subset isClosed_closure hDc, hDc,
    hDo.measure_pos H hDn, ?_, hvol, hbad⟩
  exact (measure_mono hDb).trans_lt (matrixEntryBox_isCompact _).measure_lt_top

theorem exists_weakBSG_from_self_energy {O : Set Group} {Q : ℝ}
    (hO : IsOpen O) (hOb : O ⊆ matrixEntryBox Q) (hO0 : 0 < (Measure.haar : Measure Group) O)
    {L ε : ℝ≥0∞} (hL : 0 < L) (hLt : L ≠ ⊤) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hE : ((Measure.haar : Measure Group) O) ^ 3 ≤ L * haarMultiplicativeEnergy Measure.haar O O) :
    let H : Measure Group := Measure.haar
    ∃ S D : Set Group, S ⊆ O ∧ S.Nonempty ∧ IsOpen S ∧ IsCompact (closure S) ∧
      closure S ⊆ matrixEntryBox Q ∧ D.Nonempty ∧ IsOpen D ∧ IsCompact (closure D) ∧
      closure D ⊆ matrixEntryBox (8 * Q ^ 4) ∧
      H O ^ 2 < 16 * L ^ 2 * H S ^ 2 ∧ ε * H D ≤ 32 * L ^ 4 * H O ∧
      (H.prod H) {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} < ε * H S ^ 2 := by
  let H : Measure Group := Measure.haar
  have hOt : H O < ⊤ := (measure_mono hOb).trans_lt (matrixEntryBox_isCompact Q).measure_lt_top
  let C := popularProductSet H O O (H O / (2 * L))
  obtain ⟨_, hCo, _, hCb, _, _, hCv, hpair⟩ := popularProductSet_geometry hO hOb hO0 hOt hL hLt hE
  obtain ⟨b, _, hSA, hSn, hSo, hSc, hSb, _, _, hsize, hDn, hDo, hDc, hDb, _, _, hvol, hbad⟩ :=
    exists_weakBSG_productFiber hO hO hCo hOb hOb
      (fun _ hx => hCb (subset_closure hx)) hO0 hO0
      (by positivity : 0 < 2 * L) (by finiteness : 2 * L ≠ ⊤) hε hεone
      (by simpa only [pow_two] using hpair)
  let S := productFiber O C b
  let D := popularProductSet H C C⁻¹ (ε * H O / (2 * (2 * L) ^ 2))
  refine ⟨S, D, hSA, hSn, hSo, hSc, hSb, hDn, hDo, hDc, ?_, ?_, ?_, hbad⟩
  · simpa only [show 2 * (2 * Q ^ 2) ^ 2 = 8 * Q ^ 4 by ring] using hDb
  · calc
      H O ^ 2 < 4 * (2 * L) ^ 2 * H S ^ 2 := hsize
      _ = 16 * L ^ 2 * H S ^ 2 := by ring
  · apply (ENNReal.mul_le_mul_iff_right hO0.ne' hOt.ne).mp
    calc
      H O * (ε * H D) = ε * H O * H D := by ring
      _ ≤ 2 * (2 * L) ^ 2 * H C ^ 2 := hvol
      _ ≤ 2 * (2 * L) ^ 2 * (2 * L * H O) ^ 2 :=
        mul_le_mul' le_rfl (pow_le_pow_left' hCv 2)
      _ = H O * (32 * L ^ 4 * H O) := by ring

end TransposeFollowup.RealMobius
