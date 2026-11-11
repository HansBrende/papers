import LeanMachine.FiniteSourceEscape
import AdaptiveTransfer.SparseRates

/-! One uniform dimension threshold absorbs any fixed additive exponent
overhead in a native thin-source counting theorem. -/

namespace AdaptiveTransfer

theorem source_exponent_gap_all_widths {η : ℝ} (hη : 0 < η) (κ : ℝ) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ b, 1 ≤ b → κ + 1 ≤ η * (d * d * b : ℕ) / 2 := by
  apply uniform_positive_width_threshold
    (fun P => κ + 1 ≤ η * (P : ℝ) / 2) ⌈2 * (κ + 1) / η⌉₊
  intro P hP
  have hle : 2 * (κ + 1) / η ≤ (P : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hP)
  have hh := (div_le_iff₀ hη).mp hle
  linarith

end AdaptiveTransfer
