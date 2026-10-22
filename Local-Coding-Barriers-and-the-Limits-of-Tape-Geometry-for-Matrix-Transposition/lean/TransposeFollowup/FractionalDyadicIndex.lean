import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! A fixed fractional dyadic index, with all integer rounding and
radius comparisons explicit. The threshold precedes every later index. -/
namespace TransposeFollowup
set_option autoImplicit false

theorem quarter_scale_le_of_index_ge {j v : ℕ} {θ : ℝ}
    (hv : θ * (j : ℝ) ≤ (v : ℝ)) : (1 / 4 : ℝ) ^ v ≤ ((1 / 4 : ℝ) ^ j) ^ θ := by
  calc
    _ = (1 / 4 : ℝ) ^ (v : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (1 / 4 : ℝ) ^ ((j : ℝ) * θ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by nlinarith)
    _ = _ := by rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

theorem exists_fractional_dyadic_index_threshold {θ : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) (J : ℕ) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j → ∃ v : ℕ,
      J ≤ v ∧ v ≤ j ∧ θ * (j : ℝ) ≤ v ∧ (v : ℝ) ≤ 2 * θ * j ∧
        (1 / 4 : ℝ) ^ v ≤ ((1 / 4 : ℝ) ^ j) ^ θ := by
  obtain ⟨J₀, hJ₀⟩ := exists_nat_ge (max (J : ℝ) 1 / θ)
  refine ⟨J₀, ?_⟩
  intro j hj
  have hlarge : max (J : ℝ) 1 ≤ θ * (j : ℝ) := by
    have hh := (div_le_iff₀ hθ).mp hJ₀
    have hj' : (J₀ : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith [mul_le_mul_of_nonneg_left hj' hθ.le]
  let v := ⌈θ * (j : ℝ)⌉₊
  have hvlo : θ * (j : ℝ) ≤ (v : ℝ) := Nat.le_ceil _
  have hvhi : (v : ℝ) ≤ 2 * θ * j := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg hθ.le (Nat.cast_nonneg j))
    have hlarge' : 1 ≤ θ * (j : ℝ) := (le_max_right _ _).trans hlarge
    dsimp only [v]
    linarith
  have hJv : J ≤ v := by exact_mod_cast (le_max_left (J : ℝ) 1).trans (hlarge.trans hvlo)
  have hvj : v ≤ j := by
    have hh : (v : ℝ) ≤ j := by
      nlinarith [mul_le_mul_of_nonneg_right hθhalf (Nat.cast_nonneg j)]
    exact_mod_cast hh
  exact ⟨v, hJv, hvj, hvlo, hvhi, quarter_scale_le_of_index_ge hvlo⟩

end TransposeFollowup
