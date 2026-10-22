import TransposeFollowup.ContinuousDensityConvolution
import TransposeFollowup.FiniteEnergyExtraction

/-! Measurable dyadic bands for a bounded nonnegative density. The low tail
is retained separately; the upper envelope uses at most `N` levels. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {X : Type*}

noncomputable def densityLow (f : X → ℝ≥0∞) (a : ℝ≥0∞) : X → ℝ≥0∞ :=
  {x | f x < a}.indicator f

noncomputable def densityHigh (f : X → ℝ≥0∞) (a : ℝ≥0∞) : X → ℝ≥0∞ :=
  {x | a ≤ f x}.indicator f

def dyadicDensityLevel (f : X → ℝ≥0∞) (a : ℝ≥0∞) (j : ℕ) : Set X :=
  {x | a * 2 ^ j ≤ f x ∧ f x < a * 2 ^ (j + 1)}

noncomputable def dyadicDensityMajorant (f : X → ℝ≥0∞) (a : ℝ≥0∞) (N : ℕ) (x : X) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range N, (a * 2 ^ (j + 1)) * (dyadicDensityLevel f a j).indicator 1 x

theorem densityLow_add_densityHigh (f : X → ℝ≥0∞) (a : ℝ≥0∞) (x : X) :
    densityLow f a x + densityHigh f a x = f x := by
  by_cases h : f x < a
  · simp [densityLow, densityHigh, h, not_le.mpr h]
  · simp [densityLow, densityHigh, h, le_of_not_gt h]

theorem densityLow_le (f : X → ℝ≥0∞) (a : ℝ≥0∞) (x : X) : densityLow f a x ≤ f x :=
  Set.indicator_le_self' (fun _ _ => zero_le) x

theorem densityHigh_le (f : X → ℝ≥0∞) (a : ℝ≥0∞) (x : X) : densityHigh f a x ≤ f x :=
  Set.indicator_le_self' (fun _ _ => zero_le) x

theorem densityLow_le_threshold (f : X → ℝ≥0∞) (a : ℝ≥0∞) (x : X) : densityLow f a x ≤ a := by
  by_cases h : f x < a
  · simpa [densityLow, h] using h.le
  · simp [densityLow, h]

theorem exists_dyadicDensityLevel {f : X → ℝ≥0∞} {a : ℝ≥0∞} {N : ℕ} {x : X}
    (ha : a ≤ f x) (hN : f x < a * 2 ^ N) :
    ∃ j < N, x ∈ dyadicDensityLevel f a j := by
  induction N with
  | zero => simp only [pow_zero, mul_one] at hN; exact (not_lt_of_ge ha hN).elim
  | succ N ih =>
    by_cases h : f x < a * 2 ^ N
    · obtain ⟨j, hj, hx⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hx⟩
    · exact ⟨N, Nat.lt_succ_self N, le_of_not_gt h, hN⟩

theorem densityHigh_le_dyadicDensityMajorant {f : X → ℝ≥0∞} {a : ℝ≥0∞} {N : ℕ}
    (hN : ∀ x, f x < a * 2 ^ N) (x : X) :
    densityHigh f a x ≤ dyadicDensityMajorant f a N x := by
  by_cases ha : a ≤ f x
  · obtain ⟨j, hj, hx⟩ := exists_dyadicDensityLevel ha (hN x)
    calc
      _ = f x := by simp [densityHigh, ha]
      _ ≤ a * 2 ^ (j + 1) := hx.2.le
      _ = (a * 2 ^ (j + 1)) * (dyadicDensityLevel f a j).indicator 1 x := by simp [hx]
      _ ≤ _ := by
        unfold dyadicDensityMajorant
        exact Finset.single_le_sum (f := fun i =>
          (a * 2 ^ (i + 1)) * (dyadicDensityLevel f a i).indicator 1 x)
          (fun _ _ => zero_le) (Finset.mem_range.mpr hj)
  · simp [densityHigh, ha]

theorem dyadicDensityLevel_inv {H : Type*} [Inv H] {f : H → ℝ≥0∞}
    (hs : ∀ x, f x⁻¹ = f x) (a : ℝ≥0∞) (j : ℕ) (x : H) :
    x⁻¹ ∈ dyadicDensityLevel f a j ↔ x ∈ dyadicDensityLevel f a j := by
  simp only [dyadicDensityLevel, Set.mem_ofPred_eq, hs]

variable [MeasurableSpace X]

theorem densityLow_measurable {f : X → ℝ≥0∞} (hf : Measurable f) (a : ℝ≥0∞) :
    Measurable (densityLow f a) := hf.indicator (measurableSet_lt hf measurable_const)

theorem densityHigh_measurable {f : X → ℝ≥0∞} (hf : Measurable f) (a : ℝ≥0∞) :
    Measurable (densityHigh f a) := hf.indicator (measurableSet_le measurable_const hf)

theorem dyadicDensityLevel_measurableSet {f : X → ℝ≥0∞} (hf : Measurable f)
    (a : ℝ≥0∞) (j : ℕ) : MeasurableSet (dyadicDensityLevel f a j) :=
  (measurableSet_le measurable_const hf).inter (measurableSet_lt hf measurable_const)

theorem dyadicDensityMajorant_measurable {f : X → ℝ≥0∞} (hf : Measurable f)
    (a : ℝ≥0∞) (N : ℕ) : Measurable (dyadicDensityMajorant f a N) := by
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (measurable_const.indicator (dyadicDensityLevel_measurableSet hf a j))

theorem dyadicDensityLevel_mass_le (σ : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f)
    (a : ℝ≥0∞) (j : ℕ) :
    (a * 2 ^ j) * σ (dyadicDensityLevel f a j) ≤ ∫⁻ x, f x ∂σ := by
  calc
    _ = ∫⁻ x, (dyadicDensityLevel f a j).indicator (fun _ => a * 2 ^ j) x ∂σ := by
      rw [lintegral_indicator (dyadicDensityLevel_measurableSet hf a j)]
      simp
    _ ≤ _ := lintegral_mono fun x => by
      by_cases hx : x ∈ dyadicDensityLevel f a j
      · simpa [hx] using hx.1
      · simp [hx]

end TransposeFollowup
