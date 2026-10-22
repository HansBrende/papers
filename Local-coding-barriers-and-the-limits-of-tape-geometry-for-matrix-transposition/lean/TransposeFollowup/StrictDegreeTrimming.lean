import TransposeFollowup.PopularProductEnergy

/-! Degree trimming through strict superlevels. These sets remain open
when the good degree is lower semicontinuous. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {X : Type*} [MeasurableSpace X]

theorem lintegral_le_threshold_add_tail (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) (t : ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) ≤ t * μ univ + ∫⁻ x in {x | t < f x}, f x ∂μ := by
  have hT : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  calc
    _ ≤ ∫⁻ x, t + {x | t < f x}.indicator f x ∂μ := by
      apply lintegral_mono
      intro x
      change f x ≤ t + {x | t < f x}.indicator f x
      by_cases hx : x ∈ {x | t < f x}
      · rw [Set.indicator_of_mem hx]
        exact le_add_self
      · rw [Set.indicator_of_notMem hx, add_zero]
        exact le_of_not_gt hx
    _ = _ := by rw [lintegral_add_left measurable_const, lintegral_const, lintegral_indicator hT]

theorem strict_good_degree_trim (μ : Measure X) {f g : X → ℝ≥0∞}
    (hf : Measurable f) {s r : ℝ≥0∞} (hs : μ univ = s) (hst : s ≠ ⊤)
    (hr : 0 < r) (hrs : r ≤ s) (hfg : ∀ x, f x + g x = s)
    (hsmall : 2 * (∫⁻ x, g x ∂μ) ≤ r * s) :
    s ≤ 2 * μ {x | s - r < f x} ∧ ∀ x, s - r < f x → g x < r := by
  let T := {x | s - r < f x}
  have hT : MeasurableSet T := measurableSet_lt measurable_const hf
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top hst hrs
  have hbad : r * μ Tᶜ ≤ ∫⁻ x, g x ∂μ := by
    calc
      _ = ∫⁻ x, Tᶜ.indicator (fun _ => r) x ∂μ := by
        rw [lintegral_indicator hT.compl, setLIntegral_const]
      _ ≤ _ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ Tᶜ
        · rw [Set.indicator_of_mem hx]
          have hle : f x ≤ s - r := le_of_not_gt hx
          have hft : f x ≠ ⊤ := ne_top_of_le_ne_top hst (by rw [← hfg x]; exact le_self_add)
          apply (WithTop.add_le_add_iff_left hft).mp
          calc
            f x + r ≤ s := (ENNReal.le_sub_iff_add_le_right hrt hrs).mp hle
            _ = f x + g x := (hfg x).symm
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
  have hhalf : 2 * μ Tᶜ ≤ s := by
    apply (ENNReal.mul_le_mul_iff_right hr.ne' hrt).mp
    calc
      r * (2 * μ Tᶜ) = 2 * (r * μ Tᶜ) := by ring
      _ ≤ 2 * (∫⁻ x, g x ∂μ) := mul_le_mul' le_rfl hbad
      _ ≤ r * s := hsmall
  constructor
  · apply ennreal_le_two_mul_of_small_add hst hhalf
    exact le_of_eq (by rw [add_comm, measure_add_measure_compl hT, hs])
  · intro x hx
    have hh : s < f x + r := (ENNReal.sub_lt_iff_lt_right hrt hrs).mp hx
    rw [← hfg x] at hh
    exact lt_of_add_lt_add_left hh

end TransposeFollowup
