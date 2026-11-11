import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Uniform finite small-density bounds for joint sparse support/value menus.
The generating-function proof includes the zero-support case and needs no
independence of record coordinates. -/

namespace LeanMachine

open Finset
open scoped BigOperators

theorem sparseMenu_truncate (n J A : ℕ) :
    (∑ j ∈ range (J + 1), n.choose j * A ^ j) =
      ∑ j ∈ range (min n J + 1), n.choose j * A ^ j := by
  symm
  apply sum_subset (range_mono (by omega))
  intro j hj hjnot
  have hjJ := mem_range.mp hj
  have hjmin : min n J + 1 ≤ j := by simpa only [mem_range, not_lt] using hjnot
  have hnj : n < j := by omega
  rw [Nat.choose_eq_zero_of_lt hnj, zero_mul]

noncomputable def weightedSparseMenu (n J : ℕ) (A : ℝ) : ℝ :=
  ∑ j ∈ range (min n J + 1), (n.choose j : ℝ) * A ^ j

theorem one_le_weightedSparseMenu (n J : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    1 ≤ weightedSparseMenu n J A := by
  have h := single_le_sum (f := fun j => (n.choose j : ℝ) * A ^ j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA _))
    (show 0 ∈ range (min n J + 1) by simp)
  simpa only [weightedSparseMenu, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] using h

/-- One common generating parameter charges the whole support/value menu. -/
theorem weightedSparseMenu_generating (n J : ℕ) {A x : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ J * weightedSparseMenu n J A ≤ (1 + A * x) ^ n := by
  calc
    _ = ∑ j ∈ range (min n J + 1), x ^ J * ((n.choose j : ℝ) * A ^ j) :=
      mul_sum _ _ _
    _ ≤ ∑ j ∈ range (min n J + 1), (n.choose j : ℝ) * (A * x) ^ j := by
      apply sum_le_sum
      intro j hj
      have hjJ : j ≤ J := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_right _ _)
      calc
        _ ≤ x ^ j * ((n.choose j : ℝ) * A ^ j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx hx1 hjJ) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    _ ≤ ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (A * x) ^ j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        (fun _ _ _ => by positivity)
    _ = (1 + A * x) ^ n := by
      simpa only [one_pow, mul_one, mul_comm, add_comm] using (add_pow (A * x) 1 n).symm

theorem weightedSparseMenu_log_le (n J : ℕ) {A x : ℝ}
    (hA : 0 ≤ A) (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log (weightedSparseMenu n J A) ≤
      (n : ℝ) * Real.log (1 + A * x) - (J : ℝ) * Real.log x := by
  have hS : 0 < weightedSparseMenu n J A :=
    lt_of_lt_of_le zero_lt_one (one_le_weightedSparseMenu n J hA)
  have hh := Real.log_le_log (mul_pos (pow_pos hx J) hS)
    (weightedSparseMenu_generating n J hA hx.le hx1)
  rw [Real.log_mul (ne_of_gt (pow_pos hx J)) (ne_of_gt hS),
    Real.log_pow, Real.log_pow] at hh
  linarith

/-- Uniform finite form of the sublinear sparse-menu estimate. For fixed
linear slot budget and fixed alphabet, arbitrarily small support density
costs arbitrarily small information per source bit. -/
theorem weightedSparseMenu_log_small_density {C A ε : ℝ}
    (hC : 0 < C) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n J : ℕ) (P : ℝ), 0 ≤ P →
      (n : ℝ) ≤ C * P → (J : ℝ) ≤ δ * P →
      Real.log (weightedSparseMenu n J A) ≤ ε * P := by
  let x := min 1 (ε / (2 * C * (A + 1)))
  have hd : 0 < 2 * C * (A + 1) := by positivity
  have hx : 0 < x := lt_min zero_lt_one (div_pos hε hd)
  have hx1 : x ≤ 1 := min_le_left _ _
  have hxlim : x ≤ ε / (2 * C * (A + 1)) := min_le_right _ _
  have hAx : C * (A * x) ≤ ε / 2 := by
    have hh := (le_div_iff₀ hd).mp hxlim
    nlinarith
  let α := -Real.log x
  have hα : 0 ≤ α := neg_nonneg.mpr (Real.log_nonpos hx.le hx1)
  let δ := ε / (2 * (α + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδα : δ * α ≤ ε / 2 := by
    have hh : δ * (2 * (α + 1)) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro n J P hP hn hJ
  have hlog : Real.log (1 + A * x) ≤ A * x := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + A * x by positivity)
    linarith
  have hterm₁ : (n : ℝ) * Real.log (1 + A * x) ≤ ε / 2 * P := by
    calc
      _ ≤ (n : ℝ) * (A * x) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ ≤ (C * P) * (A * x) := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (C * (A * x)) * P := by ring
      _ ≤ ε / 2 * P := mul_le_mul_of_nonneg_right hAx hP
  have hterm₂ : (J : ℝ) * α ≤ ε / 2 * P := by
    calc
      _ ≤ (δ * P) * α := mul_le_mul_of_nonneg_right hJ hα
      _ = (δ * α) * P := by ring
      _ ≤ ε / 2 * P := mul_le_mul_of_nonneg_right hδα hP
  have hh := weightedSparseMenu_log_le n J hA hx hx1
  dsimp [α] at hterm₂
  linarith

/-- Natural-cardinality spelling, matching exact support/value record counts. -/
theorem sparseMenu_log_small_density {C ε : ℝ} (A : ℕ)
    (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n J : ℕ) (P : ℝ), 0 ≤ P →
      (n : ℝ) ≤ C * P → (J : ℝ) ≤ δ * P →
      Real.log ((∑ j ∈ range (min n J + 1), n.choose j * A ^ j : ℕ) : ℝ) ≤ ε * P := by
  obtain ⟨δ, hδ, hh⟩ := weightedSparseMenu_log_small_density hC (Nat.cast_nonneg A) hε
  refine ⟨δ, hδ, ?_⟩
  intro n J P hP hn hJ
  simpa only [weightedSparseMenu, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using hh n J P hP hn hJ

/-- The sparse support/value menu has sublinear logarithm when the slot count
is linearly bounded and support density tends to zero. -/
theorem sparseMenu_log_div_tendsto_zero (A : ℕ) {C : ℝ} (hC : 0 < C)
    (n J : ℕ → ℕ)
    (hn : ∀ᶠ N in Filter.atTop, (n N : ℝ) ≤ C * N)
    (hJ : Filter.Tendsto (fun N => (J N : ℝ) / N) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun N => Real.log ((∑ j ∈ range (min (n N) (J N) + 1),
        (n N).choose j * A ^ j : ℕ) : ℝ) / N) Filter.atTop (nhds 0) := by
  have hnonneg (N : ℕ) : 0 ≤ Real.log ((∑ j ∈ range (min (n N) (J N) + 1),
      (n N).choose j * A ^ j : ℕ) : ℝ) / N := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Real.log_nonneg
    simpa only [weightedSparseMenu, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using
      one_le_weightedSparseMenu (n N) (J N) (Nat.cast_nonneg A)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun N => ha.trans_le (hnonneg N)
  · intro ε hε
    obtain ⟨δ, hδ, hdensity⟩ := sparseMenu_log_small_density A hC (half_pos hε)
    filter_upwards [hn, hJ.eventually (gt_mem_nhds hδ), Filter.eventually_gt_atTop 0]
      with N hnN hJN hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hJN' : (J N : ℝ) ≤ δ * N := ((div_lt_iff₀ hNr).mp hJN).le
    have hh := hdensity (n N) (J N) N hNr.le hnN hJN'
    have hh' := (div_le_iff₀ hNr).mpr hh
    exact hh'.trans_lt (half_lt_self hε)

end LeanMachine
