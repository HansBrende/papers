import AdaptiveTransfer.NativeReturnCounting
import AdaptiveTransfer.SparseRates
import LeanMachine.PolynomialMenus

/-! Uniform finite logarithmic budgets for the actual native metadata menu.
Both time and slab width are bounded before applying the shared polynomial
estimate. The resulting threshold is in input length, hence applies to all
positive entry widths simultaneously. -/

namespace AdaptiveTransfer
open Finset LeanMachine

/-- A polynomial envelope for the exact actual-geometry menu. -/
theorem replayMetadata_polynomial_bound {k T W N K P : ℕ}
    (hT : T ≤ K * (P + 1)) (hW : W ≤ P + 1) :
    replayMetadataSize k T W N ≤
      k * (N + 1) * ((2 * K + 3) * (P + 1)) ^ (3 + (k + 7) * N) := by
  let Z := (2 * K + 3) * (P + 1)
  have ht : T + 1 ≤ Z := by dsimp [Z]; nlinarith
  have hw : 2 * T + W + 2 ≤ Z := by dsimp [Z]; nlinarith
  have hc : 2 * T + 1 ≤ Z := by dsimp [Z]; nlinarith
  calc
    _ ≤ k * (N + 1) * Z * Z ^ 2 * (Z ^ 4 * Z ^ (k + 3)) ^ N := by
      unfold replayMetadataSize
      gcongr
    _ = _ := by
      change _ = k * (N + 1) * Z ^ (3 + (k + 7) * N)
      have hh : Z ^ 4 * Z ^ (k + 3) = Z ^ (k + 7) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hh, pow_add Z 3 ((k + 7) * N), pow_mul Z (k + 7) N]
      ring

theorem returnTime_le_integer_linear {P : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    returnTime P c ≤ ⌈c⌉₊ * (P + 1) := by
  have hh : (returnTime P c : ℝ) ≤ c * ((P : ℝ) + 1) := Nat.floor_le (by positivity)
  have hh' := hh.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (by positivity : 0 ≤ (P : ℝ) + 1))
  exact_mod_cast hh'

theorem slabWidth_le_length_add_one {P a : ℕ} {c : ℝ} (ha : 1 ≤ a) (hc : 1 ≤ c) :
    slabWidth P a c ≤ P + 1 := by
  apply Nat.ceil_le.mpr
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hden : 1 ≤ 80 * (a : ℝ) * c := by nlinarith
  have hh := div_le_self (Nat.cast_nonneg P) hden
  norm_cast at *
  exact hh.trans (by simp)

/-- Metadata costs at most `ε P` bits beyond a fixed length threshold, for
every P and with exactly the time/slab parameters in the native theorem. -/
theorem native_metadata_logb_small (k N a : ℕ) {c ε : ℝ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 1 ≤ c) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P →
      Real.logb 2 (replayMetadataSize k (returnTime P c) (slabWidth P a c) N : ℕ) ≤ ε * P := by
  obtain ⟨P₀, hh⟩ := polynomial_menu_logb_small
    (show 1 ≤ k * (N + 1) by nlinarith)
    (show 1 ≤ 2 * ⌈c⌉₊ + 3 by omega) (e := 3 + (k + 7) * N) hε
  refine ⟨P₀, fun P hP => hh P hP _ (replayMetadataSize_pos hk) ?_⟩
  exact replayMetadata_polynomial_bound (returnTime_le_integer_linear (by linarith))
    (slabWidth_le_length_add_one ha hc)

theorem returnSparseMenu_mono_alphabet {k T J A B : ℕ} (hAB : A ≤ B) :
    returnSparseMenu k T J A ≤ returnSparseMenu k T J B := by
  exact sum_le_sum fun _j _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAB _)

/-- One density controls the joint sparse record for every alphabet below a
fixed bound and every native C(P+1)-time horizon. The logarithm is in bits. -/
theorem native_sparse_logb_small (k A : ℕ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (P J B : ℕ), 1 ≤ P → B ≤ A → (J : ℝ) ≤ γ * P →
      Real.logb 2 (returnSparseMenu k (returnTime P c) J B : ℕ) ≤ ε * P := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨γ, hγ, hh⟩ := runtime_sparse_menu_small_density k A hc (mul_pos hε hlog2)
  refine ⟨γ, hγ, fun P J B hP hB hJ => ?_⟩
  have htime : (returnTime P c : ℝ) ≤ c * ((P : ℝ) + 1) := Nat.floor_le (by positivity)
  have hbound := hh P (returnTime P c) J hP htime hJ
  have hmono : Real.log (returnSparseMenu k (returnTime P c) J B : ℕ) ≤
      Real.log (returnSparseMenu k (returnTime P c) J A : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast returnSparseMenu_pos k (returnTime P c) J B
    · exact_mod_cast returnSparseMenu_mono_alphabet (k := k) (T := returnTime P c) (J := J) hB
  rw [Real.logb, div_le_iff₀ hlog2]
  have hb := hmono.trans hbound
  convert hb using 1; ring

end AdaptiveTransfer
