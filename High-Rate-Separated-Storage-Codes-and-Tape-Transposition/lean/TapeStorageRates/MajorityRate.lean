import TapeStorageRates.MajorityCounting
import LeanMachine.BinomialTail

/-! # Quantitative majority-good dimension counts

Exact finite counts are normalized by the alphabet cardinality, and the
finite binomial lower-tail estimate supplies the exponential error term.
-/

namespace TapeStorageRates.Majority

open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

private theorem binomial_monomial_normalize (k n m a : ℕ)
    (hkn : k ≤ n) (hn : 0 < n) (ha : a ≤ m) :
    ((m.choose a * k ^ a * (n - k) ^ (m - a) : ℕ) : ℝ) =
      (n : ℝ) ^ m * ((m.choose a : ℝ) * ((k : ℝ) / n) ^ a *
        (1 - (k : ℝ) / n) ^ (m - a)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hdiff : 1 - (k : ℝ) / n = ((n : ℝ) - k) / n := by
    field_simp
  have hpow : (n : ℝ) ^ m = (n : ℝ) ^ a * (n : ℝ) ^ (m - a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hkn]
  rw [hdiff, div_pow, div_pow, hpow]
  field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact majority count as a normalized finite binomial sum. -/
theorem goodIndices_card_normalized (P : Finset ι) (m : ℕ)
    (hn : 0 < Fintype.card ι) :
    ((goodIndices P m).card : ℝ) = (Fintype.card ι : ℝ) ^ m *
      ∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a),
        (m.choose a : ℝ) * ((P.card : ℝ) / Fintype.card ι) ^ a *
          (1 - (P.card : ℝ) / Fintype.card ι) ^ (m - a) := by
  rw [goodIndices_card_eq_binomial_sum, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro a ha
  exact binomial_monomial_normalize _ _ _ _ (card_le_univ P) hn
    (by have := (mem_range.mp (mem_filter.mp ha).1); omega)

/-- A fixed success margin above one half gives an exponentially small
fraction of missing basis indices. Empty alphabets are excluded explicitly. -/
theorem goodIndices_card_ge_exp (P : Finset ι) (m : ℕ)
    (hn : 0 < Fintype.card ι) {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (hr : ρ ≤ (P.card : ℝ) / Fintype.card ι) :
    (1 - Real.exp (-LeanMachine.BinomialTail.decay ρ * m)) *
      (Fintype.card ι : ℝ) ^ m ≤ (goodIndices P m).card := by
  let r : ℝ := (P.card : ℝ) / Fintype.card ι
  let f (a : ℕ) : ℝ := (m.choose a : ℝ) * r ^ a * (1 - r) ^ (m - a)
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hr1 : r ≤ 1 := by
    exact (div_le_one hnR).mpr (by exact_mod_cast card_le_univ P)
  have htail := LeanMachine.BinomialTail.half_sum_le_exp hρ hρ1 hr hr1 m
  have hsplit := sum_filter_add_sum_filter_not (range (m + 1)) (fun a => m < 2 * a) f
  simp only [not_lt] at hsplit
  have hfull : ∑ a ∈ range (m + 1), f a = 1 := by
    have h := add_pow r (1 - r) m
    rw [add_sub_cancel, one_pow] at h
    simpa only [f, mul_comm, mul_left_comm, mul_assoc] using h.symm
  rw [hfull] at hsplit
  have hgood : 1 - Real.exp (-LeanMachine.BinomialTail.decay ρ * m) ≤
      ∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a), f a := by
    change (∑ a ∈ (range (m + 1)).filter (fun a => 2 * a ≤ m), f a) ≤ _ at htail
    linarith
  calc
    _ ≤ (∑ a ∈ (range (m + 1)).filter (fun a => m < 2 * a), f a) *
        (Fintype.card ι : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hgood (pow_nonneg hnR.le _)
    _ = _ := by rw [mul_comm]; exact (goodIndices_card_normalized P m hn).symm

end
end TapeStorageRates.Majority
