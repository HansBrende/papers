import LeanMachine.BoundedWeight.Hermitian
import LeanMachine.SpectralCounting

/-! Polynomial bounds for the spectral count and the decoder code. -/

namespace LeanMachine.BoundedWeight

open scoped Matrix

variable {d : ℕ}

/-- Saturation at minus and plus one, as in backlog A3. -/
abbrev clip := SpectralCounting.clip

/-- A3 with only a one-sided approximation at the actual eigenvalues. -/
theorem two_mul_nPlus_le_of_lower_bound {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (q : Polynomial ℝ) (η : ℝ)
    (hodd : ∀ x, q.eval (-x) = -q.eval x)
    (happrox : ∀ i, clip ((hermPart_isHermitian K).eigenvalues i) - η ≤
      q.eval ((hermPart_isHermitian K).eigenvalues i)) :
    2 * (nPlus K : ℝ) ≤ (1 + η) * (d : ℝ) ^ 2 +
      (∑ k ∈ q.support, |q.coeff k| * γ ^ k) * d := by
  have hc := SpectralCounting.two_mul_card_ge_one_le
    (hermPart_isHermitian K).eigenvalues (fun x => q.eval x) η happrox
  have hm := SpectralCounting.abs_sum_eval_le_of_odd_moments
    (hermPart_isHermitian K).eigenvalues γ d (fun _ hk => abs_sum_eigenvalues_pow_le h hk)
    q hodd
  have hu := (le_abs_self _).trans hm
  have hc' := hc.trans (add_le_add le_rfl hu)
  simpa [nPlus, Nat.card_eq_fintype_card, Idx, pow_two] using hc'

/-- Backlog A3(ii): uniform two-sided approximation is a sufficient certificate. -/
theorem two_mul_nPlus_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ} (h : HasWeight K γ)
    (q : Polynomial ℝ) (η : ℝ) (hodd : ∀ x, q.eval (-x) = -q.eval x)
    (happrox : ∀ x ∈ Set.Icc (-γ) γ, |q.eval x - clip x| ≤ η) :
    2 * (nPlus K : ℝ) ≤ (1 + η) * (d : ℝ) ^ 2 +
      (∑ k ∈ q.support, |q.coeff k| * γ ^ k) * d := by
  apply two_mul_nPlus_le_of_lower_bound h q η hodd
  intro i
  have hi := (abs_le.mp (happrox _ (abs_le.mp (h.abs_eigenvalues_hermPart_le i)))).1
  linarith

/-- The polynomial certificate also bounds the code dimension directly. -/
theorem two_mul_finrank_code_le_polynomial {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (q : Polynomial ℝ) (η : ℝ)
    (hodd : ∀ x, q.eval (-x) = -q.eval x)
    (happrox : ∀ x ∈ Set.Icc (-γ) γ, |q.eval x - clip x| ≤ η) :
    2 * (Module.finrank ℂ (code K) : ℝ) ≤ (1 + η) * (d : ℝ) ^ 2 +
      (∑ k ∈ q.support, |q.coeff k| * γ ^ k) * d :=
  (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (finrank_code_le_nPlus K)) (by norm_num)).trans
    (two_mul_nPlus_le h q η hodd happrox)

end LeanMachine.BoundedWeight
