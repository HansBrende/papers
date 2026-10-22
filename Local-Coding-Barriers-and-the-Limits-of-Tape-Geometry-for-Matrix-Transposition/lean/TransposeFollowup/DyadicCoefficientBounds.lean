import TransposeFollowup.DyadicSmoothCutoff
import TransposeFollowup.DyadicAnnulusOverlap

/-! Actual uniform coefficient bounds for all derivative orders of the
dyadic cutoffs and of q_j(xi)=2*pi*i*xi*chi_j(xi). -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

noncomputable def dyadicBandWeight (j : ℕ) : ℝ := (((2 : ℝ) ^ j)⁻¹) ^ 2

theorem dyadicBandWeight_nonneg (j : ℕ) : 0 ≤ dyadicBandWeight j := by
  unfold dyadicBandWeight
  positivity

theorem dyadicBandWeight_le_one (j : ℕ) : dyadicBandWeight j ≤ 1 := by
  exact pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))

theorem baseAnnularCutoff_tsupport_subset :
    tsupport (⇑baseAnnularCutoff) ⊆ {x : ℝ | 1 ≤ |x| ∧ |x| ≤ 4} := by
  apply closure_minimal
  · intro x hx
    change baseAnnularCutoff x ≠ 0 at hx
    constructor
    · by_contra h
      have hz := dyadicAnnularCutoff_eq_zero_low 0 (x := x) (by simpa using (lt_of_not_ge h).le)
      exact hx (by simpa only [dyadicAnnularCutoff, schwartzDyadicDilate_zero] using hz)
    · by_contra h
      have hz := dyadicAnnularCutoff_eq_zero_high 0 (x := x) (by norm_num; exact (lt_of_not_ge h).le)
      exact hx (by simpa only [dyadicAnnularCutoff, schwartzDyadicDilate_zero] using hz)
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)

theorem schwartzFrequencyDerivative_tsupport_subset (u : 𝓢(ℝ, ℂ)) :
    tsupport (⇑(schwartzFrequencyDerivative u)) ⊆ tsupport (⇑u) := by
  apply closure_mono
  intro x hx
  change schwartzFrequencyDerivative u x ≠ 0 at hx
  change u x ≠ 0
  intro hz
  exact hx (by rw [schwartzFrequencyDerivative_apply, hz, mul_zero])

theorem schwartzDyadicDilate_derivative_norm_le (u : 𝓢(ℝ, ℂ)) (j n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (schwartzDyadicDilate u j) x‖ ≤ SchwartzMap.seminorm ℝ 0 n u := by
  rw [schwartzDyadicDilate_iteratedDeriv_norm]
  have hscale : (((2 : ℝ) ^ j)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  apply (mul_le_of_le_one_left (norm_nonneg _) hscale).trans
  simpa only [pow_zero, one_mul] using u.le_seminorm' ℝ 0 n (((2 : ℝ) ^ j)⁻¹ * x)

theorem finite_annular_dilation_derivative_energy_le (s : Finset ℕ) (u : 𝓢(ℝ, ℂ))
    (hu : tsupport (⇑u) ⊆ {x : ℝ | 1 ≤ |x| ∧ |x| ≤ 4}) (n : ℕ) (x : ℝ) :
    (∑ j ∈ s, ‖iteratedDeriv n (schwartzDyadicDilate u j) x‖ ^ 2) ≤
      3 * (SchwartzMap.seminorm ℝ 0 n u) ^ 2 := by
  apply dyadic_annulus_sum_le_three s x _ (sq_nonneg _)
  · intro j _
    exact pow_le_pow_left₀ (norm_nonneg _) (schwartzDyadicDilate_derivative_norm_le u j n x) 2
  · intro j _ hj
    apply schwartz_annular_derivative_support u hu j n
    intro hz
    exact hj (by rw [hz, norm_zero, zero_pow (by decide)])

theorem frequencyDerivative_dilation_normalized_energy (u : 𝓢(ℝ, ℂ)) (j n : ℕ) (x : ℝ) :
    dyadicBandWeight j *
      ‖iteratedDeriv n (schwartzFrequencyDerivative (schwartzDyadicDilate u j)) x‖ ^ 2 =
      ‖iteratedDeriv n (schwartzDyadicDilate (schwartzFrequencyDerivative u) j) x‖ ^ 2 := by
  rw [schwartzFrequencyDerivative_dyadicDilate]
  change dyadicBandWeight j * ‖iteratedDeriv n
    (((2 : ℝ) ^ j) • ⇑(schwartzDyadicDilate (schwartzFrequencyDerivative u) j)) x‖ ^ 2 = _
  rw [iteratedDeriv_const_smul_field, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j), mul_pow, dyadicBandWeight,
    ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_pow, one_mul]

theorem dyadicAnnularCutoff_derivative_square_sum_le (s : Finset ℕ) (n : ℕ) (x : ℝ) :
    (∑ j ∈ s, dyadicBandWeight j * ‖iteratedDeriv n (dyadicAnnularCutoff j) x‖ ^ 2) ≤
      3 * (SchwartzMap.seminorm ℝ 0 n baseAnnularCutoff) ^ 2 := by
  apply (Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (sq_nonneg _)
    (dyadicBandWeight_le_one j))).trans
  exact finite_annular_dilation_derivative_energy_le s baseAnnularCutoff
    baseAnnularCutoff_tsupport_subset n x

theorem dyadicAnnularCutoff_frequency_derivative_square_sum_le (s : Finset ℕ) (n : ℕ) (x : ℝ) :
    (∑ j ∈ s, dyadicBandWeight j *
      ‖iteratedDeriv n (schwartzFrequencyDerivative (dyadicAnnularCutoff j)) x‖ ^ 2) ≤
      3 * (SchwartzMap.seminorm ℝ 0 n (schwartzFrequencyDerivative baseAnnularCutoff)) ^ 2 := by
  simp only [dyadicAnnularCutoff, frequencyDerivative_dilation_normalized_energy]
  exact finite_annular_dilation_derivative_energy_le s (schwartzFrequencyDerivative baseAnnularCutoff)
    ((schwartzFrequencyDerivative_tsupport_subset _).trans baseAnnularCutoff_tsupport_subset) n x

end TransposeFollowup
