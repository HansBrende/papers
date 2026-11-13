import LeanMachine.BoundedWeight.Words
import LeanMachine.HermitianSpectrum

/-! Symmetrization preserves the weight and gives odd spectral-moment bounds. -/

noncomputable section

namespace LeanMachine.BoundedWeight

open scoped Matrix

variable {d : ℕ}

/-- The Hermitian part of the swapped decoder. -/
def hermPart (K : Matrix (Idx d) (Idx d) ℂ) : Matrix (Idx d) (Idx d) ℂ :=
  (1 / 2 : ℂ) • (T K + (T K)ᴴ)

theorem hermPart_isHermitian (K : Matrix (Idx d) (Idx d) ℂ) :
    (hermPart K).IsHermitian := by
  show (hermPart K)ᴴ = hermPart K
  simp [hermPart, Matrix.conjTranspose_smul, add_comm]

/-- The tensor combination underlying the Hermitian part. -/
def hermCore (K : Matrix (Idx d) (Idx d) ℂ) : Matrix (Idx d) (Idx d) ℂ :=
  (1 / 2 : ℂ) • (K + swapMat d * Kᴴ * swapMat d)

theorem hermPart_eq_T_hermCore (K : Matrix (Idx d) (Idx d) ℂ) :
    hermPart K = T (hermCore K) := by
  simp [hermPart, hermCore, T, Matrix.mul_add,
    Matrix.conjTranspose_mul, conjTranspose_swapMat, ← Matrix.mul_assoc, swapMat_mul_self]

/-- Symmetrization has no cost in weight. -/
theorem HasWeight.hermCore {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) : HasWeight (hermCore K) γ := by
  have hs := (h.add h.conjTranspose.swap_conj).smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change HasWeight ((1 / 2 : ℂ) • (K + swapMat d * Kᴴ * swapMat d)) γ
  have hw : (1 / 2 : ℝ) * (γ + γ) = γ := by ring
  simpa only [hw, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hs

theorem HasWeight.norm_hermPart_apply_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (x : EuclideanSpace ℂ (Idx d)) :
    ‖(hermPart K).toEuclideanLin x‖ ≤ γ * ‖x‖ := by
  rw [hermPart_eq_T_hermCore]
  exact h.hermCore.norm_T_apply_le x

/-- A constant word is a power, with no expansion into adjoint choices. -/
theorem word_replicate_true (K : Matrix (Idx d) (Idx d) ℂ) (k : ℕ) :
    word K (List.replicate k true) = T K ^ k := by
  induction k with
  | zero => simp [word]
  | succ k ih => simp [List.replicate_succ, word, ih, pow_succ']

/-- Every odd moment of the Hermitian part inherits the original trace bound. -/
theorem norm_trace_hermPart_pow_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) {k : ℕ} (hk : Odd k) :
    ‖((hermPart K) ^ k).trace‖ ≤ γ ^ k * d := by
  have ht := norm_trace_word_le h.hermCore (List.replicate k true) (by simpa using hk)
  simpa only [word_replicate_true, ← hermPart_eq_T_hermCore, List.length_replicate] using ht

/-- Every eigenvalue of the Hermitian part lies in the weight interval. -/
theorem HasWeight.abs_eigenvalues_hermPart_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) (i : Idx d) :
    |(hermPart_isHermitian K).eigenvalues i| ≤ γ :=
  HermitianSpectrum.eigenvalues_abs_le (hermPart_isHermitian K) h.norm_hermPart_apply_le i

/-- The real eigenvalue moments satisfy the odd trace bound. -/
theorem abs_sum_eigenvalues_pow_le {K : Matrix (Idx d) (Idx d) ℂ} {γ : ℝ}
    (h : HasWeight K γ) {k : ℕ} (hk : Odd k) :
    |∑ i, (hermPart_isHermitian K).eigenvalues i ^ k| ≤ γ ^ k * d := by
  have ht := norm_trace_hermPart_pow_le h hk
  rw [HermitianSpectrum.trace_pow_eq_sum (hermPart_isHermitian K)] at ht
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_eq_abs] using ht

/-- Code vectors have Rayleigh quotient exactly one for the Hermitian part. -/
theorem re_inner_hermPart_eq (K : Matrix (Idx d) (Idx d) ℂ)
    (x : EuclideanSpace ℂ (Idx d)) (hx : x ∈ LinearMap.ker (1 - T K).toEuclideanLin) :
    (inner ℂ x ((hermPart K).toEuclideanLin x)).re = ‖x‖ ^ 2 := by
  have hfix : (T K).toEuclideanLin x = x := by
    have he := LinearMap.mem_ker.mp hx
    exact (sub_eq_zero.mp (by
      simpa only [map_sub, Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.id_apply]
        using he)).symm
  simp only [hermPart, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, inner_smul_right, inner_add_right,
    LinearMap.adjoint_inner_right, hfix, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]
  ring

/-- Eigenvalues of the Hermitian part at least one, counted with multiplicity. -/
def nPlus (K : Matrix (Idx d) (Idx d) ℂ) : ℕ :=
  Nat.card {i : Idx d // 1 ≤ (hermPart_isHermitian K).eigenvalues i}

/-- Backlog A3(i). This dimension bound does not require a weight hypothesis. -/
theorem finrank_code_le_nPlus (K : Matrix (Idx d) (Idx d) ℂ) :
    Module.finrank ℂ (code K) ≤ nPlus K := by
  rw [code_eq_ker, ← RecoveryTrace.finrank_ker_toEuclideanLin]
  have h := HermitianSpectrum.finrank_le_card_eigenvalues_ge (hermPart_isHermitian K)
    (LinearMap.ker (1 - T K).toEuclideanLin) 1 (fun x hx => by
      rw [one_mul, re_inner_hermPart_eq K x hx])
  simpa only [nPlus, Nat.card_eq_fintype_card] using h

end LeanMachine.BoundedWeight
