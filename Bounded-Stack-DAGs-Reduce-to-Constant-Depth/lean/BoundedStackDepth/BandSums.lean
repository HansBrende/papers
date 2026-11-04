import BoundedStackDepth.Basic

/-!
# Band sums

The exact sum of band differences, where `band M = ⌊log₂ M⌋` for `M ≥ 1` and
`band 0 = 0`. All subtractions are truncated subtractions of natural numbers.

* `sum_band_add_pow`: the exact sum `∑_{x=1}^{N} band x + 2^{L+1} = N L + L + 2` with
  `L = band N` (by induction on `N`; the band rises only at powers of two, `band_succ`).
* `sum_band_sub_eq` (Lemma E): `∑_{x=1}^{N} (band N − band x) = 2^{L+1} − L − 2` with `L = band N`.
-/

namespace BoundedStackDepth

open Finset

/-! ### Basic facts about `band` -/

/-- `band` is monotone. -/
theorem band_mono {m n : ℕ} (h : m ≤ n) : band m ≤ band n :=
  Nat.log_mono_right h

/-- `band 0 = 0`. -/
@[simp] theorem band_zero : band 0 = 0 :=
  Nat.log_zero_right 2

/-- `2 ^ band M ≤ M` for `M ≥ 1`. -/
theorem pow_band_le {M : ℕ} (hM : M ≠ 0) : 2 ^ band M ≤ M :=
  Nat.pow_log_le_self 2 hM

/-- `M < 2 ^ (band M + 1)`. -/
theorem lt_pow_band_succ (M : ℕ) : M < 2 ^ (band M + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) M

/-- From `N` to `N + 1` the band either stays, or rises by one and `N + 1` is a power of two. -/
theorem band_succ (N : ℕ) :
    band (N + 1) = band N ∨ (band (N + 1) = band N + 1 ∧ 2 ^ band (N + 1) = N + 1) := by
  rcases (band_mono (show N ≤ N + 1 by omega)).lt_or_eq with hlt | heq
  · right
    have hN : N ≠ 0 := by
      rintro rfl
      simp [band] at hlt
    have hpow : 2 ^ band (N + 1) = N + 1 := (Nat.log_lt_log_succ_iff (by norm_num) hN).1 hlt
    have hle : band (N + 1) ≤ band N + 1 := by
      have h1 : N + 1 ≤ 2 ^ (band N + 1) := lt_pow_band_succ N
      have h2 : 2 ^ band (N + 1) ≤ 2 ^ (band N + 1) := by rw [hpow]; exact h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    exact ⟨by omega, hpow⟩
  · exact Or.inl heq.symm

/-! ### Lemma E -/

/-- The exact band sum: `∑_{x=1}^{N} band x + 2^{band N + 1} = N · band N + band N + 2`. -/
theorem sum_band_add_pow (N : ℕ) :
    ∑ x ∈ Icc 1 N, band x + 2 ^ (band N + 1) = N * band N + band N + 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    rcases band_succ N with h | ⟨h1, h2⟩
    · rw [h]
      linarith
    · have h3 : 2 ^ (band N + 1) = N + 1 := h1 ▸ h2
      rw [pow_succ, h2, h1]
      linarith

/-- Lemma E, exact form: `∑_{x=1}^{N} (band N − band x) + band N + 2 = 2^{band N + 1}`, that is,
the sum is `2^{L+1} − L − 2` with `L = band N`. -/
theorem sum_band_sub_eq (N : ℕ) :
    ∑ x ∈ Icc 1 N, (band N - band x) + band N + 2 = 2 ^ (band N + 1) := by
  have h1 : ∑ x ∈ Icc 1 N, (band N - band x) + ∑ x ∈ Icc 1 N, band x = N * band N := by
    rw [← sum_add_distrib,
      sum_congr rfl fun x hx => Nat.sub_add_cancel (band_mono (mem_Icc.1 hx).2)]
    simp
  have h2 := sum_band_add_pow N
  omega

/-! ### The general block sum -/

/-! ### Lemma S -/

/-! ### Sums over `range` -/

/-! ### Squares of bands -/

end BoundedStackDepth
