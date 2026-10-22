import TransposeFollowup.BinarySlotApproximation

/-! A convergent normalized stride supplies uniformly shifted finite-affine
approximants for any sequence of analytic slots. Slot types may change
arbitrarily, and the resulting errors are independent of the start times. -/
namespace TransposeFollowup.BinaryBankSlot
open Classical Set Filter Topology AffineMotion
set_option autoImplicit false

theorem affine_approximation_of_ratio {P : ℕ → ℕ} (hP : ∀ i, 0 < P i)
    (ops : ℕ → Option BinaryBankOperation.Operation)
    (hv : ∀ᶠ i in atTop, Valid (P i) (ops i))
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    {α : ℝ} (hα : 0 ≤ α)
    (hratio : Tendsto (fun i => (stride (ops i) : ℝ)/P i) atTop (𝓝 α))
    {H : ℝ} (hH : 0 ≤ H) :
    ∃ (J : ℕ) (e : ℕ → ℝ) (q : ℕ → ℕ → Fin 2 → ℝ → ℝ),
      0 < J ∧ Tendsto e atTop (𝓝 0) ∧ ∀ᶠ i in atTop, ∀ A,
        (∀ h, HasAffineIntervalCover J (q i A h) H) ∧
        ∀ h t, |(path (P i) (ops i) h (⌊(P i : ℝ)*t⌋₊-A) : ℝ)/P i-q i A h t| ≤ e i := by
  by_cases hz : α=0
  · rw [hz] at hratio
    refine ⟨coverBound 0,fun i => (7*(stride (ops i) : ℝ)+14)/P i,
      fun i A h t => smallApproximation (P i) A (ops i) h ((P i : ℝ)*t)/P i,
      coverBound_pos 0,?_,?_⟩
    · have hr : Tendsto (fun i => (14 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hPinf
      simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using (hratio.const_mul 7).add hr
    · filter_upwards [hv] with i hi
      intro A
      have hp : (0 : ℝ) < P i := by exact_mod_cast hP i
      refine ⟨fun h => (smallApproximation_cover (P i) A (ops i) (mul_nonneg hp.le hH) h).rescale hp,?_⟩
      intro h t
      rw [← sub_div,abs_div,abs_of_pos hp]
      exact div_le_div_of_nonneg_right (smallApproximation_error (P i) A (ops i) hi h _) hp.le
  · have hpα : 0 < α := lt_of_le_of_ne hα (Ne.symm hz)
    obtain ⟨B,hB⟩ := RawMaskedStride.eventually_bounded_groups hP hpα hratio
    refine ⟨coverBound B,fun i => (2*(B : ℝ)+14)/P i,
      fun i A h t => approximation (P i) A (ops i) h ((P i : ℝ)*t)/P i,
      coverBound_pos B,tendsto_const_nhds.div_atTop hPinf,?_⟩
    filter_upwards [hv,hB] with i hi hb
    intro A
    have hp : (0 : ℝ) < P i := by exact_mod_cast hP i
    refine ⟨fun h => (approximation_cover (P i) A B (ops i) hb (mul_nonneg hp.le hH) h).rescale hp,?_⟩
    intro h t
    rw [← sub_div,abs_div,abs_of_pos hp]
    have hbR : ((P i/stride (ops i) : ℕ) : ℝ) ≤ B := by exact_mod_cast hb
    exact div_le_div_of_nonneg_right ((approximation_error (P i) A (ops i) hi h _).trans (by linarith)) hp.le

end TransposeFollowup.BinaryBankSlot
