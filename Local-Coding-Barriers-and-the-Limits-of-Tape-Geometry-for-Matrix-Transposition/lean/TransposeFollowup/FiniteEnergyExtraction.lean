import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalities

/-! Squared-integral bookkeeping for finitely many nonnegative densities.
The finite-sum loss is polynomial in the number of pieces. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem ennreal_sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, f i ^ 2 := by
  simpa only [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] using
    ENNReal.rpow_sum_le_const_mul_sum_rpow s f (show (1 : ℝ) ≤ 2 by norm_num)

theorem ennreal_add_sq_le_two_mul_sq_add_sq (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  simpa [Fin.sum_univ_two] using
    ennreal_sum_sq_le_card_mul_sum_sq Finset.univ (fun i : Fin 2 => if i = 0 then a else b)

theorem lintegral_sq_le_bound_mul_lintegral {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f) {a : ℝ≥0∞}
    (ha : ∀ x, f x ≤ a) : (∫⁻ x, f x ^ 2 ∂σ) ≤ a * ∫⁻ x, f x ∂σ := by
  calc
    _ ≤ ∫⁻ x, a * f x ∂σ := lintegral_mono fun x => by
      rw [pow_two]
      exact mul_le_mul' (ha x) le_rfl
    _ = _ := lintegral_const_mul _ hf

theorem lintegral_sum_sq_le {X ι : Type*} [MeasurableSpace X] (σ : Measure X)
    (s : Finset ι) {f : ι → X → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i)) :
    (∫⁻ x, (∑ i ∈ s, f i x) ^ 2 ∂σ) ≤
      (s.card : ℝ≥0∞) * ∑ i ∈ s, ∫⁻ x, f i x ^ 2 ∂σ := by
  calc
    _ ≤ ∫⁻ x, (s.card : ℝ≥0∞) * ∑ i ∈ s, f i x ^ 2 ∂σ :=
      lintegral_mono fun x => ennreal_sum_sq_le_card_mul_sum_sq s _
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_finsetSum]
      exact fun i hi => (hf i hi).pow_const 2

theorem lintegral_add_sq_le {X : Type*} [MeasurableSpace X] (σ : Measure X)
    {f g : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (f x + g x) ^ 2 ∂σ) ≤ 2 * ((∫⁻ x, f x ^ 2 ∂σ) + ∫⁻ x, g x ^ 2 ∂σ) := by
  calc
    _ ≤ ∫⁻ x, 2 * (f x ^ 2 + g x ^ 2) ∂σ :=
      lintegral_mono fun x => ennreal_add_sq_le_two_mul_sq_add_sq _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hf.pow_const 2)]

theorem ennreal_le_two_mul_of_small_add {E a B : ℝ≥0∞} (hE : E ≠ ⊤)
    (htail : 2 * a ≤ E) (hbound : E ≤ a + B) : E ≤ 2 * B := by
  have h : E + E ≤ E + 2 * B := by
    calc
      E + E = 2 * E := by ring
      _ ≤ 2 * (a + B) := mul_le_mul' le_rfl hbound
      _ = 2 * a + 2 * B := by ring
      _ ≤ E + 2 * B := add_le_add htail le_rfl
  exact (WithTop.add_le_add_iff_left hE).mp h

end TransposeFollowup
