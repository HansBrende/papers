import TransposeFollowup.MobiusHighDegreeRows

/-! Rich rows and few exceptional quotients yield two open subsets
whose entire product has controlled Haar volume. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_open_product_trim {O S C D : Set Group}
    (hO : IsOpen O) (hS : IsOpen S) (hC : IsOpen C) (hD : IsOpen D)
    (hOt : (Measure.haar : Measure Group) O < ⊤)
    (hS0 : 0 < (Measure.haar : Measure Group) S) (hSt : (Measure.haar : Measure Group) S < ⊤)
    {L : ℝ≥0∞} (hLone : 1 ≤ L) (hLt : L ≠ ⊤)
    (hrich : ∀ a ∈ S, (Measure.haar : Measure Group) O / (4 * L) <
      relationRowDegree ((Measure.haar : Measure Group).restrict O) (productIncidence C) a)
    (hbad : 64 * L * ((Measure.haar : Measure Group).prod Measure.haar)
      {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} ≤
        ((Measure.haar : Measure Group) S) ^ 2) :
    let H : Measure Group := Measure.haar
    ∃ A B : Set Group, A ⊆ S ∧ B ⊆ O ∧ IsOpen A ∧ IsOpen B ∧
      H S ≤ 2 * H A ∧ H O ≤ 8 * L * H B ∧
      H S * H (A * B) ≤ 16 * L * H D * H C := by
  let H : Measure Group := Measure.haar
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  let E : Set (Group × Group) := {p | p.1 * p.2⁻¹ ∈ D}
  have hEo : IsOpen E := hD.preimage (by fun_prop)
  have hEm : MeasurableSet E := hEo.measurableSet
  let f := relationRowDegree (H.restrict S) E
  let g := relationRowDegree (H.restrict S) Eᶜ
  let r := H S / (32 * L)
  let T := {a | H S - r < f a}
  let A := S ∩ T
  have hTo : IsOpen T := (relationRowDegree_lowerSemicontinuous _ hEo hEm).isOpen_preimage _
  have hrcancel : (32 * L) * r = H S := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hr0 : 0 < r := ENNReal.div_pos hS0.ne' (by finiteness)
  have hrs : r ≤ H S := by
    apply (ENNReal.mul_le_mul_iff_right (by positivity : 32 * L ≠ 0) (by finiteness)).mp
    rw [hrcancel]
    calc
      H S = 1 * H S := (one_mul _).symm
      _ ≤ (32 * L) * H S := mul_le_mul' (by
        calc
          (1 : ℝ≥0∞) ≤ 32 * 1 := by norm_num
          _ ≤ 32 * L := mul_le_mul' le_rfl hLone) le_rfl
  have hfg : ∀ a, f a + g a = H S := fun a => by
    simpa only [Measure.restrict_apply_univ] using relationRowDegree_add_compl (H.restrict S) hEm a
  have hsmall : 2 * (∫⁻ a in S, g a ∂H) ≤ r * H S := by
    apply (ENNReal.mul_le_mul_iff_right (by positivity : 32 * L ≠ 0) (by finiteness)).mp
    calc
      (32 * L) * (2 * (∫⁻ a in S, g a ∂H)) =
          64 * L * (H.prod H) {p : Group × Group | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} := by
        dsimp only [g]
        rw [relationRowDegree_restrict_lintegral H H S S hEm.compl]
        simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq]
        ring
      _ ≤ H S ^ 2 := hbad
      _ = (32 * L) * (r * H S) := by rw [← mul_assoc, hrcancel, pow_two]
  obtain ⟨hAsize, hAg⟩ := strict_good_degree_trim (H.restrict S)
    (relationRowDegree_measurable _ hEm) (Measure.restrict_apply_univ S) hSt.ne hr0 hrs hfg hsmall
  have hsizeA : H S ≤ 2 * H A := by
    change H S ≤ 2 * (H.restrict S) T at hAsize
    simpa only [Measure.restrict_apply hTo.measurableSet, Set.inter_comm] using hAsize
  let col := edgeFiberMass (H.restrict S) (productIncidence C)
  have hCm : MeasurableSet (productIncidence C) := productIncidence_measurable hC.measurableSet
  have hcol : Measurable col := edgeFiberMass_measurable _ hCm
  have hcolsemi : LowerSemicontinuous col := by
    change LowerSemicontinuous (relationRowDegree (H.restrict S) {p : Group × Group | p.2 * p.1 ∈ C})
    have ho : IsOpen {p : Group × Group | p.2 * p.1 ∈ C} := hC.preimage (by fun_prop)
    exact relationRowDegree_lowerSemicontinuous _ ho ho.measurableSet
  have hcolbound : ∀ b, col b ≤ H S := fun b => by
    calc
      col b ≤ ∫⁻ _a in S, (1 : ℝ≥0∞) ∂H :=
        lintegral_mono fun a => Set.indicator_le_self' (fun _ _ => zero_le) (a, b)
      _ = H S := by rw [lintegral_one, Measure.restrict_apply_univ]
  let m := ∫⁻ b in O, col b ∂H
  have hmrow : m = ∫⁻ a in S, relationRowDegree (H.restrict O) (productIncidence C) a ∂H := by
    rw [relationRowDegree_lintegral _ _ hCm]
    exact edgeFiberMass_lintegral _ _ hCm
  have hmlo : H S * H O ≤ 4 * L * m := by
    calc
      H S * H O = (4 * L) * ((H O / (4 * L)) * H S) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel (by positivity) (by finiteness)]
        exact mul_comm _ _
      _ ≤ (4 * L) * m := by
        apply mul_le_mul' le_rfl
        rw [hmrow, ← setLIntegral_const]
        exact lintegral_mono_ae ((ae_restrict_mem hS.measurableSet).mono fun a ha => (hrich a ha).le)
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (by finiteness : H S * H O ≠ ⊤) (by
    calc
      m ≤ ∫⁻ _b in O, H S ∂H := lintegral_mono hcolbound
      _ = _ := by rw [setLIntegral_const])
  let u := H S / (8 * L)
  let U := {b | u < col b}
  let B := O ∩ U
  have hUo : IsOpen U := hcolsemi.isOpen_preimage u
  have hucancel : (8 * L) * u = H S := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hmhalf : 2 * (u * H O) ≤ m := by
    apply (ENNReal.mul_le_mul_iff_right (by positivity : 4 * L ≠ 0) (by finiteness)).mp
    calc
      (4 * L) * (2 * (u * H O)) = ((8 * L) * u) * H O := by ring
      _ = H S * H O := by rw [hucancel]
      _ ≤ (4 * L) * m := hmlo
  have hsplit : m ≤ u * H O + ∫⁻ b in B, col b ∂H := by
    have hh := lintegral_le_threshold_add_tail (H.restrict O) hcol u
    rw [Measure.restrict_apply_univ] at hh
    change m ≤ u * H O + ∫⁻ b, col b ∂((H.restrict O).restrict U) at hh
    rw [Measure.restrict_restrict hUo.measurableSet] at hh
    simpa only [Set.inter_comm] using hh
  have hm2 := ennreal_le_two_mul_of_small_add hmt hmhalf hsplit
  have htail : (∫⁻ b in B, col b ∂H) ≤ H S * H B := by
    calc
      _ ≤ ∫⁻ _b in B, H S ∂H := lintegral_mono hcolbound
      _ = _ := by rw [setLIntegral_const]
  have hsizeB : H O ≤ 8 * L * H B := by
    apply (ENNReal.mul_le_mul_iff_right hS0.ne' hSt.ne).mp
    calc
      H S * H O ≤ 4 * L * m := hmlo
      _ ≤ 4 * L * (2 * (H S * H B)) := mul_le_mul' le_rfl (hm2.trans (mul_le_mul' le_rfl htail))
      _ = H S * (8 * L * H B) := by ring
  let t := H S / (16 * L)
  have htcancel : (16 * L) * t = H S := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have htr : t + r ≤ u := by
    apply (ENNReal.mul_le_mul_iff_right (by positivity : 32 * L ≠ 0) (by finiteness)).mp
    calc
      (32 * L) * (t + r) = 2 * ((16 * L) * t) + (32 * L) * r := by ring
      _ = 3 * H S := by rw [htcancel, hrcancel]; ring
      _ ≤ 4 * H S := mul_le_mul' (by norm_num) le_rfl
      _ = (32 * L) * u := by rw [show (32 : ℝ≥0∞) * L * u = 4 * ((8 * L) * u) by ring, hucancel]
  have hprod : A * B ⊆ popularProductSet H D C t := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    change t < densityConvolution H (D.indicator 1) (C.indicator 1) (a * b)
    by_contra hn
    have hgb : g a < r := hAg a ha.2
    have hh := productNeighbor_degree_le_density_add_bad H S hC.measurableSet hD.measurableSet a b
    have hh' : col b ≤ u := calc
      col b ≤ densityConvolution H (D.indicator 1) (C.indicator 1) (a * b) + g a := hh
      _ ≤ t + r := add_le_add (le_of_not_gt hn) hgb.le
      _ ≤ u := htr
    exact (not_le_of_gt hb.2) hh'
  refine ⟨A, B, inter_subset_left, inter_subset_left, hS.inter hTo, hO.inter hUo,
    hsizeA, hsizeB, ?_⟩
  calc
    H S * H (A * B) = (16 * L) * (t * H (A * B)) := by rw [← mul_assoc, htcancel]
    _ ≤ (16 * L) * (t * H (popularProductSet H D C t)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hprod))
    _ ≤ (16 * L) * (H D * H C) := mul_le_mul' le_rfl
      (popularProductSet_threshold_measure_le H hD.measurableSet hC.measurableSet t)
    _ = _ := by ring

end TransposeFollowup.RealMobius
