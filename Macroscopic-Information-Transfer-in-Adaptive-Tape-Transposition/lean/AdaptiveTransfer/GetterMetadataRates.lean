import AdaptiveTransfer.GetterMetadata
import AdaptiveTransfer.MetadataRates

/-! Uniform finite information budgets for actual multiport geometry.
The fixed number of ports changes only the polynomial degree, and the
threshold in input length works simultaneously for every positive width. -/

namespace AdaptiveTransfer.Getter
open LeanMachine

theorem portMetadataSize_pos {k p T W N : ℕ} (hk : 1 ≤ k) :
    0 < portMetadataSize k p T W N := by
  unfold portMetadataSize
  positivity

/-- A common polynomial envelope includes the actual past-visit intervals
of every noncarrier work head. No interval is charged when k=1. -/
theorem portMetadata_polynomial_bound {k p T W N K P : ℕ}
    (hT : T ≤ K * (P + 1)) (hW : W ≤ P + 1) :
    portMetadataSize k p T W N ≤
      k * (N + 1) * ((2 * K + 3) * (P + 1)) ^
        (3 + (4 + k + 3 * p + 2 * (k - 1)) * N) := by
  let Z := (2 * K + 3) * (P + 1)
  have ht : T + 1 ≤ Z := by dsimp [Z]; nlinarith
  have hw : 2 * T + W + 2 ≤ Z := by dsimp [Z]; nlinarith
  have hc : 2 * T + 1 ≤ Z := by dsimp [Z]; nlinarith
  have hcp : 2 * T + 2 ≤ Z := by dsimp [Z]; nlinarith
  have hinterval : 1 + (2 * T + 1) ^ 2 ≤ Z ^ 2 := by
    calc
      _ ≤ (2 * T + 2) ^ 2 := by nlinarith
      _ ≤ _ := Nat.pow_le_pow_left hcp 2
  calc
    _ ≤ k * (N + 1) * Z * Z ^ 2 *
        (Z ^ 4 * Z ^ (k + 3 * p) * (Z ^ 2) ^ (k - 1)) ^ N := by
      unfold portMetadataSize
      gcongr
    _ = _ := by
      change _ = k * (N + 1) * Z ^ (3 + (4 + k + 3 * p + 2 * (k - 1)) * N)
      have hh : Z ^ 4 * Z ^ (k + 3 * p) * (Z ^ 2) ^ (k - 1) =
          Z ^ (4 + k + 3 * p + 2 * (k - 1)) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
      rw [hh, pow_add Z 3 ((4 + k + 3 * p + 2 * (k - 1)) * N),
        pow_mul Z (4 + k + 3 * p + 2 * (k - 1)) N]
      ring

/-- A single length threshold controls all time and width bounds in the
finite native getter argument, including the enlarged one-work-head model. -/
theorem port_metadata_logb_small (k p N K : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P T W, P₀ ≤ P → T ≤ K * (P + 1) → W ≤ P + 1 →
      Real.logb 2 (portMetadataSize k p T W N : ℕ) ≤ ε * P := by
  obtain ⟨P₀, hh⟩ := polynomial_menu_logb_small
    (show 1 ≤ k * (N + 1) by nlinarith)
    (show 1 ≤ 2 * K + 3 by omega)
    (e := 3 + (4 + k + 3 * p + 2 * (k - 1)) * N) hε
  refine ⟨P₀, fun P T W hP hT hW => hh P hP _ (portMetadataSize_pos hk) ?_⟩
  exact portMetadata_polynomial_bound hT hW

end AdaptiveTransfer.Getter
