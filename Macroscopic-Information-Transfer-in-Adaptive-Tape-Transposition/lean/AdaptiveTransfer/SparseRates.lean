import LeanMachine.SparseBinomial

/-! Uniform sparse-record rates for a native linear-time horizon, together
with the all-positive-width transfer of a finite length threshold. -/

namespace AdaptiveTransfer

open Finset LeanMachine
open scoped BigOperators

theorem runtime_sparse_menu_small_density (k A : ℕ) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (P T J : ℕ), 1 ≤ P →
      (T : ℝ) ≤ C * (P + 1) → (J : ℝ) ≤ γ * P →
      Real.log ((∑ j ∈ range (min (k * T) J + 1), (k * T).choose j * A ^ j : ℕ) : ℝ) ≤
        ε * P := by
  obtain ⟨γ, hγ, hh⟩ := sparseMenu_log_small_density A
    (show 0 < 2 * ((k : ℝ) + 1) * C by positivity) hε
  refine ⟨γ, hγ, ?_⟩
  intro P T J hP hT hJ
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hslots : ((k * T : ℕ) : ℝ) ≤ (2 * ((k : ℝ) + 1) * C) * P := by
    push_cast
    calc
      (k : ℝ) * T ≤ k * (C * (P + 1)) :=
        mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)
      _ ≤ k * (C * (2 * P)) := by gcongr; linarith
      _ ≤ (2 * ((k : ℝ) + 1) * C) * P := by nlinarith
  exact hh (k * T) J P (Nat.cast_nonneg P) hslots hJ

/-- A length threshold works simultaneously for every positive bit width. -/
theorem uniform_positive_width_threshold (property : ℕ → Prop)
    (P₀ : ℕ) (h : ∀ P, P₀ ≤ P → property P) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → property (d * d * b) := by
  refine ⟨max 1 P₀, ?_⟩
  intro d hd b hb
  apply h
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdP : P₀ ≤ d := (le_max_right _ _).trans hd
  nlinarith

theorem bit_plane_error_ratio {d b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) :
    ((d * b : ℕ) : ℝ) / (d * d * b : ℕ) = 1 / (d : ℝ) := by
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hbn : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  push_cast
  field_simp

end AdaptiveTransfer
