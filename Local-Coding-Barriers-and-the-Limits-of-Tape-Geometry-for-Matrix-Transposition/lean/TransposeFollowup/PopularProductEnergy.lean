import TransposeFollowup.OpenProductDensity
import TransposeFollowup.HaarSetEnergyBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! High continuous self-energy forces a controlled popular-product
region carrying substantial product mass. All cancellations are finite. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem densityConvolution_indicator_lintegral (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x, densityConvolution σ (A.indicator 1) (B.indicator 1) x ∂σ) = σ A * σ B := by
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  have hg : Measurable (B.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hB
  rw [densityConvolution_lintegral σ hf hg,
    lintegral_indicator_one hA, lintegral_indicator_one hB]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem densityConvolution_indicator_le_left (σ : Measure G) {A B : Set G}
    (hA : MeasurableSet A) (x : G) :
    densityConvolution σ (A.indicator 1) (B.indicator 1) x ≤ σ A := by
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  have h := densityConvolution_le_of_right_le σ hf
    (show ∀ x, B.indicator (1 : G → ℝ≥0∞) x ≤ 1 from
      fun x => Set.indicator_le_self' (fun _ _ => zero_le) x) x
  simpa only [lintegral_indicator_one hA, mul_one] using h

theorem popularProductSet_threshold_measure_le (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {A B : Set G} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (t : ℝ≥0∞) :
    t * σ (popularProductSet σ A B t) ≤ σ A * σ B := by
  have hf : Measurable (densityConvolution σ (A.indicator 1) (B.indicator 1)) :=
    densityConvolution_measurable σ (measurable_const.indicator hA) (measurable_const.indicator hB)
  calc
    _ ≤ t * σ {x | t ≤ densityConvolution σ (A.indicator 1) (B.indicator 1) x} :=
      mul_le_mul' le_rfl (measure_mono (fun x hx =>
        (show t < densityConvolution σ (A.indicator 1) (B.indicator 1) x from hx).le))
    _ ≤ _ := (mul_meas_ge_le_lintegral hf t).trans_eq (densityConvolution_indicator_lintegral σ hA hB)

theorem haarEnergy_le_popular_tail_add (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {A B : Set G} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (t : ℝ≥0∞) :
    haarMultiplicativeEnergy σ A B ≤ t * (σ A * σ B) +
      σ A * ∫⁻ x in popularProductSet σ A B t,
        densityConvolution σ (A.indicator 1) (B.indicator 1) x ∂σ := by
  let F := densityConvolution σ (A.indicator 1) (B.indicator 1)
  let C := popularProductSet σ A B t
  have hF : Measurable F := densityConvolution_measurable σ
    (measurable_const.indicator hA) (measurable_const.indicator hB)
  have hCm : MeasurableSet C := measurableSet_lt measurable_const hF
  have hm : (∫⁻ x, F x ∂σ) = σ A * σ B := densityConvolution_indicator_lintegral σ hA hB
  calc
    haarMultiplicativeEnergy σ A B ≤ ∫⁻ x, t * F x + σ A * C.indicator F x ∂σ := by
      apply lintegral_mono
      intro x
      change F x ^ 2 ≤ t * F x + σ A * C.indicator F x
      by_cases hx : x ∈ C
      · rw [Set.indicator_of_mem hx]
        calc
          F x ^ 2 ≤ σ A * F x := by
            rw [pow_two]
            exact mul_le_mul' (densityConvolution_indicator_le_left σ hA x) le_rfl
          _ ≤ _ := le_add_self
      · have hxt : F x ≤ t := le_of_not_gt hx
        rw [Set.indicator_of_notMem hx, mul_zero, add_zero, pow_two]
        exact mul_le_mul' hxt le_rfl
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun x => t * F x) from by fun_prop), lintegral_const_mul _ hF,
        lintegral_const_mul _ (hF.indicator hCm), lintegral_indicator hCm,
        hm]

theorem popularProductSet_bounds (σ : Measure G) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {A : Set G} (hA : MeasurableSet A) (hA0 : 0 < σ A) (hAt : σ A < ⊤)
    {L : ℝ≥0∞} (hL : 0 < L) (hLt : L ≠ ⊤)
    (hE : σ A ^ 3 ≤ L * haarMultiplicativeEnergy σ A A) :
    let t := σ A / (2 * L)
    let C := popularProductSet σ A A t
    σ C ≤ 2 * L * σ A ∧ σ A ^ 2 ≤ 2 * L *
      ∫⁻ x in C, densityConvolution σ (A.indicator 1) (A.indicator 1) x ∂σ := by
  let w := σ A
  let t := w / (2 * L)
  let C := popularProductSet σ A A t
  let E := haarMultiplicativeEnergy σ A A
  let M := ∫⁻ x in C, densityConvolution σ (A.indicator 1) (A.indicator 1) x ∂σ
  have hcancel : (2 * L) * t = w := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hmark : t * σ C ≤ w * w := popularProductSet_threshold_measure_le σ hA hA t
  have htail : 2 * (t * (w * w)) ≤ E := by
    apply (ENNReal.mul_le_mul_iff_right hL.ne' hLt).mp
    calc
      L * (2 * (t * (w * w))) = ((2 * L) * t) * w ^ 2 := by ring
      _ = w ^ 3 := by rw [hcancel]; ring
      _ ≤ L * E := hE
  have hpop : E ≤ 2 * (w * M) := ennreal_le_two_mul_of_small_add
    (haarMultiplicativeEnergy_lt_top σ hA hA hAt hAt).ne htail
    (haarEnergy_le_popular_tail_add σ hA hA t)
  constructor
  · apply (ENNReal.mul_le_mul_iff_right hA0.ne' hAt.ne).mp
    calc
      w * σ C = (2 * L) * (t * σ C) := by rw [← mul_assoc, hcancel]
      _ ≤ (2 * L) * (w * w) := mul_le_mul' le_rfl hmark
      _ = w * (2 * L * w) := by ring
  · apply (ENNReal.mul_le_mul_iff_right hA0.ne' hAt.ne).mp
    calc
      w * w ^ 2 = w ^ 3 := by ring
      _ ≤ L * E := hE
      _ ≤ L * (2 * (w * M)) := mul_le_mul' le_rfl hpop
      _ = w * (2 * L * M) := by ring

end TransposeFollowup
