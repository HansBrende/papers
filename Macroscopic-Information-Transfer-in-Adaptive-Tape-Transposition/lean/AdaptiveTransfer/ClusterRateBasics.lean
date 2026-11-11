import AdaptiveTransfer.SparseRates
import Mathlib

/-! Exact floor/ceiling fringe costs and dimension-uniform geometric budgets
for coherent clusters. These are numeric estimates, not native replay or
class-count certificates.
-/

namespace AdaptiveTransfer

noncomputable def clusterEpsilon (k a N : ℕ) : ℝ :=
  1 / (128 * (a : ℝ) * k * (N : ℝ) ^ 2)

theorem clusterEpsilon_pos {k a N : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    0 < clusterEpsilon k a N := by unfold clusterEpsilon; positivity

theorem clusterEpsilon_le_one {k a N : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    clusterEpsilon k a N ≤ 1 := by
  have hn : 1 ≤ 128 * a * k * N ^ 2 := by
    have hp : 0 < 128 * a * k * N ^ 2 := by positivity
    omega
  have hd : (1 : ℝ) ≤ 128 * a * k * (N : ℝ) ^ 2 := by exact_mod_cast hn
  unfold clusterEpsilon
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hd)

theorem cluster_fringe_le_length {k a N : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hN : 1 ≤ N) (P : ℕ) :
    ⌈clusterEpsilon k a N * P⌉₊ ≤ P := by
  apply Nat.ceil_le.mpr
  exact (mul_le_mul_of_nonneg_right (clusterEpsilon_le_one hk ha hN) (Nat.cast_nonneg P)).trans_eq
    (one_mul _)

/-- Literal `j=ceil(epsilon P)` and `H=floor(epsilon P)` satisfy the
manuscript's complete window/fringe bill, including the six-symbol constant. -/
theorem cluster_window_budget {k a N : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hN : 1 ≤ N) (P : ℕ) :
    (a : ℝ) * N * k *
      (max (4 * ⌈clusterEpsilon k a N * P⌉₊ + 2) (2 * ⌊clusterEpsilon k a N * P⌋₊ + 1) : ℕ) ≤
      (P : ℝ) / (32 * (N : ℝ)) + 6 * a * N * k := by
  have hε := clusterEpsilon_pos hk ha hN
  have hj := (Nat.ceil_lt_add_one (show 0 ≤ clusterEpsilon k a N * (P : ℝ) by positivity)).le
  have hH := Nat.floor_le (show 0 ≤ clusterEpsilon k a N * (P : ℝ) by positivity)
  have hleft : ((4 * ⌈clusterEpsilon k a N * P⌉₊ + 2 : ℕ) : ℝ) ≤
      4 * (clusterEpsilon k a N * P) + 6 := by push_cast; linarith
  have hright : ((2 * ⌊clusterEpsilon k a N * P⌋₊ + 1 : ℕ) : ℝ) ≤
      4 * (clusterEpsilon k a N * P) + 6 := by
    push_cast
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) P)]
  have hmax : ((max (4 * ⌈clusterEpsilon k a N * P⌉₊ + 2)
      (2 * ⌊clusterEpsilon k a N * P⌋₊ + 1) : ℕ) : ℝ) ≤
      4 * (clusterEpsilon k a N * P) + 6 := by
    rw [Nat.cast_max]
    exact max_le hleft hright
  calc
    _ ≤ (a : ℝ) * N * k * (4 * (clusterEpsilon k a N * P) + 6) := by gcongr
    _ = _ := by
      have han : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
      have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have hNn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      unfold clusterEpsilon
      field_simp
      ring

/-- An explicit dimension threshold pays the stripe term simultaneously
for every positive entry width. -/
theorem cluster_geometry_budget {F N d b : ℕ} (hF : 1 ≤ F) (hN : 1 ≤ N)
    (hd : 3 * F * N ^ 2 ≤ d) :
    3 * (N : ℝ) * d * b ≤ (d * d * b : ℕ) / ((F : ℝ) * N) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < F * N)).mpr
  have hr : 3 * (F : ℝ) * (N : ℝ) ^ 2 ≤ d := by exact_mod_cast hd
  have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ (d : ℝ) * b by positivity)
  push_cast
  nlinarith

theorem cluster_constant_budget {F N K d b : ℕ} (hF : 1 ≤ F) (hN : 1 ≤ N)
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hK : F * N * K ≤ d) :
    (K : ℝ) ≤ (d * d * b : ℕ) / ((F : ℝ) * N) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < F * N)).mpr
  have hdP : d ≤ d * d * b := by nlinarith
  have hh : (F : ℝ) * N * K ≤ (d * d * b : ℕ) := by exact_mod_cast hK.trans hdP
  nlinarith

end AdaptiveTransfer
