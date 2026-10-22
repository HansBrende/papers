import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Compatible dyadic walk lengths and smoothing radii. The radius is
(1/4)^j, and the logarithmic flattening threshold is an explicit inequality.
No flattening theorem is assumed or proved by these scalar lemmas. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem dyadic_smoothing_error_of_integer_bounds {A r : ℝ} (hA : 0 ≤ A)
    {N K j ell : ℕ} (hN : (1 / 2 : ℝ) ^ N ≤ r)
    (hK : A * (1 / 2 : ℝ) ^ K ≤ 1 / 2) (hj : N * ell + K ≤ j) :
    A * (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j ≤ r ^ ell / 2 := by
  have heq : (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j = (1 / 2 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  calc
    _ = A * (1 / 2 : ℝ) ^ j := by rw [mul_assoc, heq]
    _ ≤ A * (1 / 2 : ℝ) ^ (N * ell + K) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) hA
    _ = (A * (1 / 2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ N) ^ ell := by rw [pow_add, pow_mul]; ring
    _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ N) ^ ell :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ r ^ ell / 2 := by
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 / 2 : ℝ) ^ N) hN ell
      linarith

theorem exists_dyadic_smoothing_integer_parameters (Nmin : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∃ N J : ℕ, 0 < N ∧ Nmin ≤ N ∧ 0 < J ∧ 2 * N ≤ J ∧
      ∀ j ell : ℕ, J ≤ j → 2 * N * ell ≤ j →
        A * (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j ≤ r ^ ell / 2 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  let N := max Nmin (max 1 n)
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1)
    ((le_max_left 1 n).trans (le_max_right _ _))
  have hN : (1 / 2 : ℝ) ^ N ≤ r :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      ((le_max_right 1 n).trans (le_max_right _ _))).trans hn.le
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
    (by positivity : (0 : ℝ) < 1 / (2 * (A + 1))) (by norm_num : (1 / 2 : ℝ) < 1)
  have hKbound : A * (1 / 2 : ℝ) ^ K ≤ 1 / 2 := by
    have hk := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (A + 1))).mp hK
    have hp : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
    nlinarith
  refine ⟨N, max (2 * K + 1) (2 * N), hNpos, le_max_left _ _, ?_, le_max_right _ _, ?_⟩
  · exact lt_of_lt_of_le (by omega : 0 < 2 * K + 1) (le_max_left _ _)
  · intro j ell hj hell
    apply dyadic_smoothing_error_of_integer_bounds hA hN hKbound
    have hk : 2 * K + 1 ≤ j := (le_max_left _ _).trans hj
    have he : 2 * (N * ell) ≤ j := by simpa [Nat.mul_assoc] using hell
    omega

theorem exists_dyadic_length_in_window {N j : ℕ} (hN : 0 < N) (hj : 2 * N ≤ j) :
    ∃ m : ℕ, 2 * N * 2 ^ m ≤ j ∧ (j : ℝ) / (4 * N) < (2 : ℝ) ^ m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2N : (0 : ℝ) < 2 * N := by positivity
  have h4N : (0 : ℝ) < 4 * N := by positivity
  have hbase : (1 : ℝ) ≤ (j : ℝ) / (2 * N) := by
    apply (le_div_iff₀ h2N).mpr
    norm_num
    exact_mod_cast hj
  obtain ⟨m, hlo, hhi⟩ := exists_nat_pow_near hbase (by norm_num : (1 : ℝ) < 2)
  refine ⟨m, ?_, ?_⟩
  · have h := (le_div_iff₀ h2N).mp hlo
    have he : (2 : ℝ) * N * 2 ^ m ≤ j := by nlinarith
    exact_mod_cast he
  · apply (div_lt_iff₀ h4N).mpr
    have h := (div_lt_iff₀ h2N).mp hhi
    rw [pow_succ] at h
    nlinarith

theorem dyadic_smoothing_log_inv (j : ℕ) :
    Real.log (1 / (1 / 4 : ℝ) ^ j) = (j : ℝ) * Real.log 4 := by
  have he : 1 / (1 / 4 : ℝ) ^ j = (4 : ℝ) ^ j := by simp [one_div, inv_pow]
  rw [he, Real.log_pow]

theorem dyadic_flattening_threshold_le {N j : ℕ} (hN : 0 < N) {C L : ℝ} (hL : 0 < L)
    (hscale : 4 * (N : ℝ) * C * Real.log 4 ≤ L) :
    C * Real.log (1 / (1 / 4 : ℝ) ^ j) / L ≤ (j : ℝ) / (4 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_div_iff₀ hL (by positivity : (0 : ℝ) < 4 * N)).mpr
  rw [dyadic_smoothing_log_inv]
  have h := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  nlinarith

theorem exists_compatible_dyadic_smoothing_scales (Nmin : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) :
    ∃ N J : ℕ, 0 < N ∧ Nmin ≤ N ∧ 0 < J ∧ ∀ C L : ℝ, 0 < L →
      4 * (N : ℝ) * C * Real.log 4 ≤ L → ∀ j : ℕ, J ≤ j →
      ∃ m : ℕ, 2 * N * 2 ^ m ≤ j ∧
        C * Real.log (1 / (1 / 4 : ℝ) ^ j) / L < (2 : ℝ) ^ m ∧
        A * (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j ≤ r ^ (2 ^ m) / 2 ∧
        (1 / 4 : ℝ) ^ j ≤ 1 / 2 := by
  obtain ⟨N, J, hN, hNmin, hJ, hNJ, herror⟩ := exists_dyadic_smoothing_integer_parameters Nmin hA hr
  refine ⟨N, J, hN, hNmin, hJ, ?_⟩
  intro C L hL hscale j hj
  obtain ⟨m, hm, hlow⟩ := exists_dyadic_length_in_window hN (hNJ.trans hj)
  refine ⟨m, hm, (dyadic_flattening_threshold_le hN hL hscale).trans_lt hlow,
    herror j (2 ^ m) hj hm, ?_⟩
  have hjpos : 0 < j := lt_of_lt_of_le hJ hj
  calc
    (1 / 4 : ℝ) ^ j ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hjpos
    _ ≤ 1 / 2 := by norm_num

theorem exists_small_parameter_log_bound (M : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      0 < Real.log (1 / ε) ∧ M ≤ Real.log (1 / ε) := by
  let t := max M 0 + 1
  have ht : 0 < t := by dsimp [t]; have := le_max_right M 0; linarith
  refine ⟨Real.exp (-t), Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  intro ε hε hεsmall
  have hlog := Real.log_le_log hε hεsmall
  rw [Real.log_exp] at hlog
  rw [one_div, Real.log_inv]
  have hMt : M < t := by dsimp [t]; have := le_max_left M 0; linarith
  constructor <;> linarith

end TransposeFollowup
