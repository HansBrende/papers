import LeanMachine.BoundedWeight.Basic

/-! Dimension bounds for bounded-weight transposition decoders (backlog A2). -/

namespace LeanMachine.BoundedWeight

open Module
open scoped Matrix Kronecker

variable {d : ℕ} {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}

/-- A weight is necessarily nonnegative, including in dimension zero. -/
theorem HasWeight.nonneg (h : HasWeight K γ) : 0 ≤ γ := by
  obtain ⟨m, c, A, B, hc, hγ, _⟩ := h
  rw [← hγ]
  exact Finset.sum_nonneg fun a _ => hc a

/-- The coefficient sum bounds the Euclidean operator norm. -/
theorem HasWeight.norm_apply_le (h : HasWeight K γ) (x : EuclideanSpace ℂ (Idx d)) :
    ‖K.toEuclideanLin x‖ ≤ γ * ‖x‖ := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  calc
    ‖∑ a, (c a : ℂ) • (A a ⊗ₖ B a).toEuclideanLin x‖ ≤
        ∑ a, ‖(c a : ℂ) • (A a ⊗ₖ B a).toEuclideanLin x‖ := norm_sum_le _ _
    _ ≤ ∑ a, c a * ‖x‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, Complex.norm_of_nonneg (hc a)]
      exact mul_le_mul_of_nonneg_left
        (RecoveryTrace.norm_toEuclideanLin_le _ ((hA a).kronecker (hB a)) x) (hc a)
    _ = _ := by rw [← Finset.sum_mul, hγ]

/-- Composing with transpose does not change the norm bound. -/
theorem HasWeight.norm_T_apply_le (h : HasWeight K γ) (x : EuclideanSpace ℂ (Idx d)) :
    ‖(T K).toEuclideanLin x‖ ≤ γ * ‖x‖ := by
  rw [T, Matrix.toLpLin_mul_same, LinearMap.comp_apply, norm_swapMat_apply]
  exact h.norm_apply_le x

/-- A tensor summand has a swapped trace of magnitude at most the side length. -/
theorem norm_trace_swapMat_kronecker_le (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : IsContraction A) (hB : IsContraction B) :
    ‖(swapMat d * (A ⊗ₖ B)).trace‖ ≤ d := by
  rw [trace_swapMat_kronecker]
  have h := RecoveryTrace.norm_trace_le (A * B).toEuclideanLin 1 (fun x => by
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, one_mul]
    exact (RecoveryTrace.norm_toEuclideanLin_le A hA _).trans
      (RecoveryTrace.norm_toEuclideanLin_le B hB x))
  simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq,
    finrank_euclideanSpace, Fintype.card_fin, mul_one] using h

/-- The length-one case of the odd-word trace bound, sufficient for A2. -/
theorem HasWeight.norm_trace_T_le (h : HasWeight K γ) : ‖(T K).trace‖ ≤ γ * d := by
  obtain ⟨m, c, A, B, hc, hγ, hA, hB, rfl⟩ := h
  simp only [T, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul]
  calc
    ‖∑ a, (c a : ℂ) • (swapMat d * (A a ⊗ₖ B a)).trace‖ ≤
        ∑ a, ‖(c a : ℂ) • (swapMat d * (A a ⊗ₖ B a)).trace‖ := norm_sum_le _ _
    _ ≤ ∑ a, c a * (d : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, Complex.norm_of_nonneg (hc a)]
      exact mul_le_mul_of_nonneg_left
        (norm_trace_swapMat_kronecker_le (A a) (B a) (hA a) (hB a)) (hc a)
    _ = _ := by rw [← Finset.sum_mul, hγ]

/-- A sharper form of A2 retains the actual real trace. -/
theorem finrank_code_le_trace (h : HasWeight K γ) :
    (1 + γ) * (finrank ℂ (code K) : ℝ) ≤ γ * (d : ℝ) ^ 2 + (T K).trace.re := by
  have hdim := RecoveryTrace.weighted_finrank_fixed_le (T K) γ h.norm_T_apply_le
  rw [← code_eq_ker] at hdim
  simpa [Idx, pow_two] using hdim

/-- Backlog A2: bounded weight limits the dimension of a transposition code. -/
theorem finrank_code_le (h : HasWeight K γ) :
    (1 + γ) * (finrank ℂ (code K) : ℝ) ≤ γ * ((d : ℝ) ^ 2 + d) := by
  have ht := (Complex.re_le_norm (T K).trace).trans h.norm_trace_T_le
  nlinarith only [finrank_code_le_trace h, ht]

/-- Backlog A2 for weight at most one. -/
theorem two_mul_finrank_code_le_of_le_one (h : HasWeight K γ) (hγ : γ ≤ 1) :
    2 * (finrank ℂ (code K) : ℝ) ≤ (d : ℝ) ^ 2 + γ * d := by
  have hd : (finrank ℂ (code K) : ℝ) ≤ (d : ℝ) ^ 2 := by
    have hd := Submodule.finrank_le (code K)
    simp only [Module.finrank_pi, Idx, Fintype.card_prod, Fintype.card_fin] at hd
    rw [pow_two]
    exact_mod_cast hd
  have hprod := mul_nonneg (sub_nonneg.mpr hγ) (sub_nonneg.mpr hd)
  nlinarith only [finrank_code_le h, hprod]

/-- Below weight one no nonzero matrix can be transposed by the decoder. -/
theorem code_eq_bot_of_lt_one (h : HasWeight K γ) (hγ : γ < 1) : code K = ⊥ := by
  rw [code_eq_ker]
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  apply sub_eq_zero.mp
  have hx : (T K).mulVecLin (x - y) = x - y := by
    have hz : (1 - T K).mulVecLin (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    simpa only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero, eq_comm] using hz
  let v : EuclideanSpace ℂ (Idx d) := WithLp.toLp 2 (x - y)
  have hv : (T K).toEuclideanLin v = v := congrArg (WithLp.toLp 2) hx
  have hn := h.norm_T_apply_le v
  rw [hv] at hn
  have hz : v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  exact congrArg WithLp.ofLp hz

end LeanMachine.BoundedWeight
