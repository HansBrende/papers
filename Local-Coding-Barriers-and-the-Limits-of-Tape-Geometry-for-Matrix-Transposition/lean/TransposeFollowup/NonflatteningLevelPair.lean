import TransposeFollowup.DensityLevelEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Failure to flatten produces a large-energy pair among logarithmically
many measurable level sets. The threshold and every logarithmic loss are
chosen explicitly; there is no finite-group discretization hypothesis. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem exists_logarithmic_dyadic_cutoff (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, 0 < N ∧ C < a * 2 ^ N ∧
      (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (C / a)) := by
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near (le_max_left 1 (C / a)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, Nat.succ_pos n, ?_, ?_⟩
  · have h := (le_max_right 1 (C / a)).trans_lt hhi
    have := (div_lt_iff₀ ha).mp h
    simpa only [mul_comm] using this
  · have hx : 0 < max 1 (C / a) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hn : (n : ℝ) ≤ Real.logb 2 (max 1 (C / a)) := by
      apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hx).mpr
      simpa only [Real.rpow_natCast] using hlo
    push_cast
    linarith

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem exists_nonflattening_level_pair (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) ≤ 1)
    {C τ : ℝ} (hτ : 0 < τ) (hC : ∀ x, f x ≤ ENNReal.ofReal C)
    (hnonflat : ENNReal.ofReal τ ≤ ∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) :
    let a := ENNReal.ofReal (τ / 16)
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / τ)) ∧
      ∃ i < N, ∃ j < N,
        ENNReal.ofReal τ ≤ 4 * (N : ℝ≥0∞) ^ 4 *
          ((a * 2 ^ (i + 1)) * (a * 2 ^ (j + 1))) ^ 2 *
            haarMultiplicativeEnergy σ (dyadicDensityLevel f a i) (dyadicDensityLevel f a j) := by
  dsimp only
  have ha : 0 < τ / 16 := by positivity
  obtain ⟨N, hN, hcap, hlog⟩ := exists_logarithmic_dyadic_cutoff C ha
  have hcap' (x : H) : f x < ENNReal.ofReal (τ / 16) * 2 ^ N := by
    calc
      _ ≤ ENNReal.ofReal C := hC x
      _ < ENNReal.ofReal (τ / 16 * 2 ^ N) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hcap
      _ = _ := by rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_pow (by norm_num)]; norm_num
  have htail : 16 * ENNReal.ofReal (τ / 16) ≤ ENNReal.ofReal τ := by
    have h : (16 : ℝ≥0∞) * ENNReal.ofReal (τ / 16) = ENNReal.ofReal τ := by
      rw [← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    exact h.le
  obtain ⟨i, hi, j, hj, hE⟩ := exists_dyadicDensityLevel_large_energy σ hf hm hN hcap'
    ENNReal.ofReal_ne_top htail hnonflat
  refine ⟨N, hN, ?_, i, hi, j, hj, hE⟩
  convert hlog using 1
  congr 3
  ring

end TransposeFollowup
