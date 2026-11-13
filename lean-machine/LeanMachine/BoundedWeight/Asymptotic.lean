import LeanMachine.BoundedWeight.Polynomial
import LeanMachine.OddPolynomialApproximation

/-! A uniform asymptotic half-rate bound for decoders of bounded weight. -/

namespace LeanMachine.BoundedWeight

open scoped Matrix

theorem continuous_clip : Continuous clip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clip_neg (x : ℝ) : clip (-x) = -clip x := by
  simp only [clip, SpectralCounting.clip, ← min_neg_neg, ← max_neg_neg, neg_neg,
    min_max_distrib_left]
  norm_num

/-- A nonnegative linear correction bounds the spectral count uniformly over
all decoders whose weights are at most `Γ`. The constant depends only on `Γ, η`. -/
theorem exists_uniform_spectral_excess (Γ η : ℝ) (hΓ : 0 ≤ Γ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (γ : ℝ) (K : Matrix (Idx d) (Idx d) ℂ),
      γ ≤ Γ → HasWeight K γ → (nPlus K : ℝ) ≤ (1 / 2 + η) * (d : ℝ) ^ 2 + C * d := by
  obtain ⟨q, hodd, hq⟩ := exists_odd_polynomial_near clip Γ (2 * η)
    continuous_clip.continuousOn clip_neg (by positivity)
  let C := (∑ k ∈ q.support, |q.coeff k| * Γ ^ k) / 2
  refine ⟨C, ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (pow_nonneg hΓ _))
      (by norm_num)
  · intro d γ K hγ hK
    have h := two_mul_nPlus_le (hK.mono hγ) q (2 * η) hodd (fun x hx => (hq x hx).le)
    dsimp [C]
    linarith

/-- Backlog A4: fixed weight gives rate at most one half asymptotically. -/
theorem exists_linear_excess (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ (d : ℕ) (K : Matrix (Idx d) (Idx d) ℂ), HasWeight K γ →
      (Module.finrank ℂ (code K) : ℝ) ≤ (1 / 2 + η) * (d : ℝ) ^ 2 + C * d := by
  obtain ⟨C, _, hC⟩ := exists_uniform_spectral_excess γ η hγ hη
  exact ⟨C, fun d K hK => (Nat.cast_le.mpr (finrank_code_le_nPlus K)).trans
    (hC d γ K le_rfl hK)⟩

end LeanMachine.BoundedWeight
