import TransposeFollowup.FiniteEnergyExtraction

/-! A simultaneous large-weight/small-error selection by integration.
Positive finite margins avoid subtraction of extended-real infinities. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem exists_large_weight_small_error {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) {f g : Y → ℝ≥0∞} (hf : Measurable f)
    {T : Set Y} (hT : ∀ᵐ y ∂ν, y ∈ T) (hν0 : 0 < ν univ) (hνt : ν univ ≠ ⊤)
    {ε z : ℝ≥0∞} (hε0 : 0 < ε) (hεt : ε ≠ ⊤) (hz0 : 0 < z) (hzt : z ≠ ⊤)
    (hlarge : 4 * z * ν univ ≤ ∫⁻ y, f y ∂ν)
    (hsmall : (∫⁻ y, g y ∂ν) ≤ 2 * ε * z * ν univ) :
    ∃ y ∈ T, z < f y ∧ g y < ε * f y := by
  by_contra hn
  push Not at hn
  have hp : ∀ᵐ y ∂ν, ε * f y ≤ ε * z + g y := by
    filter_upwards [hT] with y hy
    by_cases hs : z < f y
    · exact (hn y hy hs).trans le_add_self
    · exact (mul_le_mul' le_rfl (le_of_not_gt hs)).trans le_self_add
  have hint : ε * (∫⁻ y, f y ∂ν) ≤ (ε * z) * ν univ + ∫⁻ y, g y ∂ν := by
    calc
      _ = ∫⁻ y, ε * f y ∂ν := (lintegral_const_mul ε hf).symm
      _ ≤ ∫⁻ y, ε * z + g y ∂ν := lintegral_mono_ae hp
      _ = _ := by rw [lintegral_add_left measurable_const, lintegral_const]
  have hc : (4 : ℝ≥0∞) ≤ 3 := by
    apply (ENNReal.mul_le_mul_iff_left (by positivity : ε * z * ν univ ≠ 0) (by finiteness)).mp
    calc
      4 * (ε * z * ν univ) = ε * (4 * z * ν univ) := by ring
      _ ≤ ε * ∫⁻ y, f y ∂ν := mul_le_mul' le_rfl hlarge
      _ ≤ (ε * z) * ν univ + ∫⁻ y, g y ∂ν := hint
      _ ≤ (ε * z) * ν univ + 2 * ε * z * ν univ := add_le_add le_rfl hsmall
      _ = 3 * (ε * z * ν univ) := by ring
  norm_num at hc

end TransposeFollowup
