import TransposeFollowup.ShortWordBicommutator
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Every fixed positive power of the inverse dyadic radius eventually
beats the quadratic exceptional count for words of length at most2j. -/
namespace TransposeFollowup.FreeWordFamily
open Classical Filter
open scoped Topology commutatorElement
set_option autoImplicit false

universe u

theorem exists_short_word_count_threshold {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ L : ℕ, L ≤ 2 * j →
      (((8 * L + 1) * (4 * L + 1) : ℕ) : ℝ) < ((1 / 4 : ℝ) ^ j) ^ (-τ) := by
  let R : ℝ := (1 / 4 : ℝ) ^ (-τ)
  have hR : 1 < R := Real.one_lt_rpow_of_pos_of_lt_one_of_neg
    (by norm_num) (by norm_num) (neg_neg_of_pos hτ)
  have hev : ∀ᶠ j : ℕ in atTop, (j : ℝ) ^ 2 / R ^ j < 1 / 153 :=
    (tendsto_pow_const_div_const_pow_of_one_lt 2 hR).eventually_lt_const (by norm_num)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hev
  refine ⟨max J 1, ?_⟩
  intro j hj L hL
  have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
  have hjs : (j : ℝ) ^ 2 / R ^ j < 1 / 153 := hJ j ((le_max_left _ _).trans hj)
  have hpow : 0 < R ^ j := pow_pos (zero_lt_one.trans hR) j
  have hbound : 153 * (j : ℝ) ^ 2 < R ^ j := by
    have hh := (div_lt_iff₀ hpow).mp hjs
    linarith
  have hpoly : (((8 * L + 1) * (4 * L + 1) : ℕ) : ℝ) ≤ 153 * (j : ℝ) ^ 2 := by
    have h₁ : (L : ℝ) ≤ 2 * j := by exact_mod_cast hL
    have h₂ : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    push_cast
    have ha : 8 * (L : ℝ) + 1 ≤ 17 * j := by linarith
    have hb : 4 * (L : ℝ) + 1 ≤ 9 * j := by linarith
    have hh := mul_le_mul ha hb (by positivity) (by positivity)
    nlinarith only [hh]
  exact hpoly.trans_lt (hbound.trans_eq (Real.rpow_pow_comm (by norm_num) (-τ) j))

theorem exists_short_word_bicommutator_threshold {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ {α : Type u} [DecidableEq α]
      (F : Finset (FreeGroup α)) (L : ℕ), L ≤ 2 * j →
      (∀ x ∈ F, FreeGroup.norm x ≤ L) →
      ((1 / 4 : ℝ) ^ j) ^ (-τ) ≤ (F.card : ℝ) →
      ∃ a ∈ F, ∃ x ∈ F, ∃ y ∈ F, ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1 ∧
        FreeGroup.norm ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≤ 16 * L := by
  obtain ⟨J, hJ⟩ := exists_short_word_count_threshold hτ
  refine ⟨J, ?_⟩
  intro j hj α _ F L hLj hL hcard
  apply exists_nontrivial_bicommutator F L hL
  exact_mod_cast (hJ j hj L hLj).trans_le hcard

end TransposeFollowup.FreeWordFamily
