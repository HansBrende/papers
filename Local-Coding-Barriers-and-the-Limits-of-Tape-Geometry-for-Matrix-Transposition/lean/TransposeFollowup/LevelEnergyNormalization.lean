import TransposeFollowup.NonflatteningLevelPair

/-! Remove the density weights from the extracted level energy. The
positive finite squared mass is cancelled explicitly. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {X : Type*} [MeasurableSpace X]

theorem dyadicDensityLevel_second_moment_le (σ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (a : ℝ≥0∞) (j : ℕ) :
    (a * 2 ^ j) ^ 2 * σ (dyadicDensityLevel f a j) ≤ ∫⁻ x, f x ^ 2 ∂σ := by
  calc
    _ = ∫⁻ x, (dyadicDensityLevel f a j).indicator (fun _ => (a * 2 ^ j) ^ 2) x ∂σ := by
      rw [lintegral_indicator (dyadicDensityLevel_measurableSet hf a j)]
      simp
    _ ≤ _ := lintegral_mono fun x => by
      by_cases hx : x ∈ dyadicDensityLevel f a j
      · simpa [hx] using pow_le_pow_left' hx.1 2
      · simp [hx]

theorem dyadicDensityLevel_measure_lt_top (σ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) < ⊤) {a : ℝ≥0∞} (ha : a ≠ 0) (j : ℕ) :
    σ (dyadicDensityLevel f a j) < ⊤ := by
  have h := (dyadicDensityLevel_mass_le σ hf a j).trans_lt hm
  exact ENNReal.lt_top_of_mul_ne_top_right h.ne (mul_ne_zero ha (by positivity))

theorem lintegral_sq_ne_zero_of_mass_ne_zero (σ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) ≠ 0) : (∫⁻ x, f x ^ 2 ∂σ) ≠ 0 := by
  intro h
  have hz := (lintegral_eq_zero_iff (hf.pow_const 2)).mp h
  apply hm
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hz] with x hx
  simpa only [Pi.zero_apply, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)] using hx

theorem normalize_weighted_pair_energy {a b A B U E θ K : ℝ≥0∞}
    (hU0 : U ≠ 0) (hUtop : U ≠ ⊤)
    (hA : a * A ≤ 1) (hB : b * B ≤ 1) (hA2 : a ^ 2 * A ≤ U) (hB2 : b ^ 2 * B ≤ U)
    (hE : θ * U ≤ K * a ^ 2 * b ^ 2 * E) :
    θ * A ^ 2 * B ≤ K * E ∧ θ * A * B ^ 2 ≤ K * E := by
  have hleft : θ * A ^ 2 * B * U ≤ K * E * U := by
    calc
      _ = θ * U * (A ^ 2 * B) := by ring
      _ ≤ (K * a ^ 2 * b ^ 2 * E) * (A ^ 2 * B) := mul_le_mul' hE le_rfl
      _ = (K * E) * ((a * A) ^ 2 * (b ^ 2 * B)) := by ring
      _ ≤ (K * E) * (1 ^ 2 * U) :=
        mul_le_mul' le_rfl (mul_le_mul' (pow_le_pow_left' hA 2) hB2)
      _ = _ := by simp
  have hright : θ * A * B ^ 2 * U ≤ K * E * U := by
    calc
      _ = θ * U * (A * B ^ 2) := by ring
      _ ≤ (K * a ^ 2 * b ^ 2 * E) * (A * B ^ 2) := mul_le_mul' hE le_rfl
      _ = (K * E) * ((a ^ 2 * A) * (b * B) ^ 2) := by ring
      _ ≤ (K * E) * (U * 1 ^ 2) :=
        mul_le_mul' le_rfl (mul_le_mul' hA2 (pow_le_pow_left' hB 2))
      _ = _ := by simp
  exact ⟨(ENNReal.mul_le_mul_iff_left hU0 hUtop).mp hleft,
    (ENNReal.mul_le_mul_iff_left hU0 hUtop).mp hright⟩

theorem weighted_pair_volume_window_left {a b A B U E θ K : ℝ≥0∞}
    (hU0 : U ≠ 0) (hUtop : U ≠ ⊤)
    (hA : a * A ≤ 1) (hB : b * B ≤ 1) (hA2 : a ^ 2 * A ≤ U) (hB2 : b ^ 2 * B ≤ U)
    (hE : θ * U ≤ K * a ^ 2 * b ^ 2 * E) (hEL : E ≤ A ^ 2 * B) (hER : E ≤ A * B ^ 2) :
    θ ≤ K * U * A ∧ θ * U * A ≤ K := by
  have hl : θ * U ≤ (K * (a * A) ^ 2) * U := by
    calc
      _ ≤ K * a ^ 2 * b ^ 2 * E := hE
      _ ≤ K * a ^ 2 * b ^ 2 * (A ^ 2 * B) := mul_le_mul' le_rfl hEL
      _ = (K * (a * A) ^ 2) * (b ^ 2 * B) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hB2
  have hl' : θ ≤ K * (a * A) ^ 2 := (ENNReal.mul_le_mul_iff_left hU0 hUtop).mp hl
  have hu : θ * U ≤ K * (a ^ 2 * A) := by
    calc
      _ ≤ K * a ^ 2 * b ^ 2 * E := hE
      _ ≤ K * a ^ 2 * b ^ 2 * (A * B ^ 2) := mul_le_mul' le_rfl hER
      _ = (K * (a ^ 2 * A)) * (b * B) ^ 2 := by ring
      _ ≤ (K * (a ^ 2 * A)) * 1 ^ 2 := mul_le_mul' le_rfl (pow_le_pow_left' hB 2)
      _ = _ := by simp
  constructor
  · calc
      _ ≤ K * (a * A) ^ 2 := hl'
      _ = K * (a ^ 2 * A) * A := by ring
      _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hA2) le_rfl
  · calc
      _ ≤ (K * (a ^ 2 * A)) * A := mul_le_mul' hu le_rfl
      _ = K * (a * A) ^ 2 := by ring
      _ ≤ K * 1 ^ 2 := mul_le_mul' le_rfl (pow_le_pow_left' hA 2)
      _ = _ := by simp

end TransposeFollowup
