import TransposeFollowup.MobiusWeakBSG
import TransposeFollowup.ProductNeighborOverlap

/-! Retain an open set of uniformly rich rows before weak BSG.
This supplies the uniform degree hypothesis needed by the final trim. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem high_product_degree_rows {O C : Set Group} (hO : IsOpen O) (hC : IsOpen C)
    (hO0 : 0 < (Measure.haar : Measure Group) O) (hOt : (Measure.haar : Measure Group) O < ⊤)
    {L : ℝ≥0∞} (hL : 0 < L) (hLt : L ≠ ⊤)
    (hdense : ((Measure.haar : Measure Group) O) ^ 2 ≤ 2 * L *
      ((Measure.haar : Measure Group).prod Measure.haar)
        {p : Group × Group | p.1 ∈ O ∧ p.2 ∈ O ∧ p.1 * p.2 ∈ C}) :
    let H : Measure Group := Measure.haar
    let f := relationRowDegree (H.restrict O) (productIncidence C)
    let A := O ∩ {a | H O / (4 * L) < f a}
    IsOpen A ∧ 0 < H A ∧ H O ≤ 4 * L * H A ∧
      H A * H O ≤ 4 * L * (H.prod H)
        {p : Group × Group | p.1 ∈ A ∧ p.2 ∈ O ∧ p.1 * p.2 ∈ C} := by
  let H : Measure Group := Measure.haar
  let f := relationRowDegree (H.restrict O) (productIncidence C)
  let t := H O / (4 * L)
  let T := {a | t < f a}
  let A := O ∩ T
  let m := ∫⁻ a in O, f a ∂H
  let tail := ∫⁻ a in A, f a ∂H
  have hEo : IsOpen (productIncidence C) := hC.preimage (by fun_prop)
  have hEm : MeasurableSet (productIncidence C) := hEo.measurableSet
  have hf : Measurable f := relationRowDegree_measurable _ hEm
  have hTo : IsOpen T := (relationRowDegree_lowerSemicontinuous _ hEo hEm).isOpen_preimage t
  have hAo : IsOpen A := hO.inter hTo
  have hfbound : ∀ a, f a ≤ H O := fun a => by
    simpa only [Measure.restrict_apply_univ] using relationRowDegree_le (H.restrict O) (productIncidence C) a
  have hm : H O ^ 2 ≤ 2 * L * m := by
    simpa only [m, f, relationRowDegree_restrict_lintegral H H O O hEm, productIncidence,
      Set.mem_ofPred_eq] using hdense
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (by finiteness : H O * H O ≠ ⊤) (by
    calc
      m ≤ ∫⁻ _a in O, H O ∂H := lintegral_mono hfbound
      _ = H O * H O := by rw [setLIntegral_const])
  have hcancel : (4 * L) * t = H O := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hsmall : 2 * (t * H O) ≤ m := by
    apply (ENNReal.mul_le_mul_iff_right (by positivity : 2 * L ≠ 0) (by finiteness)).mp
    calc
      2 * L * (2 * (t * H O)) = ((4 * L) * t) * H O := by ring
      _ = H O ^ 2 := by rw [hcancel, pow_two]
      _ ≤ 2 * L * m := hm
  have hsplit : m ≤ t * H O + tail := by
    have hh := lintegral_le_threshold_add_tail (H.restrict O) hf t
    rw [Measure.restrict_apply_univ] at hh
    change m ≤ t * H O + ∫⁻ a, f a ∂((H.restrict O).restrict T) at hh
    rw [Measure.restrict_restrict hTo.measurableSet] at hh
    simpa only [Set.inter_comm] using hh
  have hm2 : m ≤ 2 * tail := ennreal_le_two_mul_of_small_add hmt hsmall hsplit
  have htail : tail ≤ H O * H A := by
    calc
      tail ≤ ∫⁻ _a in A, H O ∂H := lintegral_mono hfbound
      _ = _ := by rw [setLIntegral_const]
  have hsize : H O ≤ 4 * L * H A := by
    apply (ENNReal.mul_le_mul_iff_right hO0.ne' hOt.ne).mp
    calc
      H O * H O ≤ 2 * L * m := by simpa only [pow_two] using hm
      _ ≤ 2 * L * (2 * tail) := mul_le_mul' le_rfl hm2
      _ ≤ 2 * L * (2 * (H O * H A)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl htail)
      _ = H O * (4 * L * H A) := by ring
  refine ⟨hAo, ?_, hsize, ?_⟩
  · by_contra hn
    have hz : H A = 0 := le_antisymm (le_of_not_gt hn) zero_le
    rw [hz, mul_zero] at hsize
    exact (not_le_of_gt hO0) hsize
  · calc
      H A * H O ≤ H O * H O := mul_le_mul' (measure_mono inter_subset_left) le_rfl
      _ ≤ 2 * L * m := by simpa only [pow_two] using hm
      _ ≤ 2 * L * (2 * tail) := mul_le_mul' le_rfl hm2
      _ = 4 * L * tail := by ring
      _ = _ := by
        dsimp only [tail, f]
        rw [relationRowDegree_restrict_lintegral H H A O hEm]
        rfl

end TransposeFollowup.RealMobius
