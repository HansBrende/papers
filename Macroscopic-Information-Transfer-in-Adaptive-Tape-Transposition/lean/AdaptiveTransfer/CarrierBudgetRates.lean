import AdaptiveTransfer.LinearHashing
import AdaptiveTransfer.SparseRates
import LeanMachine.BinaryBudgets

/-! Literal sparse-hash and state-menu budgets for the dynamic carrier.
The actual transition table and physical handoff invariant remain separate.
No final simulator state-bit bound is assumed in these estimates. -/

namespace AdaptiveTransfer

open LeanMachine Finset

def carrierOverhead (k T : ℕ) : ℕ :=
  let n := 2 * T + 1
  k * (T + 1) * n ^ (k + 1) * (n + 1) ^ k * (4 * T + 1) * (1 + n ^ 2)

theorem carrierOverhead_pos {k : ℕ} (hk : 1 ≤ k) (T : ℕ) : 1 ≤ carrierOverhead k T := by
  dsimp only [carrierOverhead]
  have hk' : 0 < k := by omega
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

theorem carrierOverhead_polynomial (k K P T : ℕ) (hT : T ≤ K * (P + 1)) :
    carrierOverhead k T ≤ k * ((4 * K + 4) * (P + 1)) ^ (2 * k + 5) := by
  let B := (4 * K + 4) * (P + 1)
  have ht : T + 1 ≤ B := by dsimp [B]; nlinarith
  have hn : 2 * T + 1 ≤ B := by dsimp [B]; nlinarith
  have hn' : 2 * T + 1 + 1 ≤ B := by dsimp [B]; nlinarith
  have h4 : 4 * T + 1 ≤ B := by dsimp [B]; nlinarith
  have hs : 1 + (2 * T + 1) ^ 2 ≤ B ^ 2 := by nlinarith
  dsimp only [carrierOverhead]
  calc
    _ ≤ k * B * B ^ (k + 1) * B ^ k * B * B ^ 2 := by gcongr
    _ = k * B ^ (2 * k + 5) := by
      simp only [two_mul, pow_succ, pow_add]
      ring

theorem carrierOverhead_bits_small {k : ℕ} (hk : 1 ≤ k) {C ε : ℝ}
    (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      (Nat.clog 2 (carrierOverhead k T) : ℝ) ≤ ε * P := by
  obtain ⟨P₀, hr⟩ := polynomial_menu_clog_small hk
    (show 1 ≤ 4 * ⌈C⌉₊ + 4 by omega) hε
  refine ⟨P₀, ?_⟩
  intro P hP T hT
  apply hr P hP (carrierOverhead k T) (carrierOverhead_pos hk T)
  apply carrierOverhead_polynomial
  have hTC : (T : ℝ) ≤ (⌈C⌉₊ : ℝ) * (P + 1) :=
    hT.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity))
  exact_mod_cast hTC

theorem blockSparseMenu_pos (n a s : ℕ) : 1 ≤ blockSparseMenu n a s := by
  have h := one_le_weightedSparseMenu n s (Nat.cast_nonneg (2 ^ a - 1))
  exact_mod_cast (by
    simpa only [weightedSparseMenu, blockSparseMenu, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
      using h : (1 : ℝ) ≤ blockSparseMenu n a s)

/-- A positive sparse density has an arbitrarily small complete syndrome
budget, with the literal doubled support plus two cells and ceiling. -/
theorem carrier_hash_bits_small (a : ℕ) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ P₀ : ℕ, ∀ P, P₀ ≤ P →
      ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
        (Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)) : ℝ) ≤ ε * P := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨δ₀, hδ₀, hr⟩ := sparseMenu_log_small_density (2 ^ a - 1)
    (show 0 < 4 * C + 1 by linarith) (mul_pos (half_pos hε) hlog)
  let δ := min (δ₀ / 4) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  let P₀ := max 1 (max ⌈1 / δ⌉₊ ⌈2 / ε⌉₊)
  refine ⟨δ, hδ, min_le_right _ _, P₀, ?_⟩
  intro P hP T hT
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (le_max_left 1 _).trans hP
  have hδP : 1 ≤ δ * P := by
    have hh : 1 / δ ≤ (P : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_left ⌈1 / δ⌉₊ _).trans ((le_max_right 1 _).trans hP))
    have hmul := (div_le_iff₀ hδ).mp hh
    linarith
  have hεP : 2 ≤ ε * P := by
    have hh : 2 / ε ≤ (P : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right ⌈1 / δ⌉₊ _).trans ((le_max_right 1 _).trans hP))
    have hmul := (div_le_iff₀ hε).mp hh
    linarith
  have hn : ((2 * T + 1 : ℕ) : ℝ) ≤ (4 * C + 1) * P := by push_cast; nlinarith
  have hs : ((2 * ⌊δ * P⌋₊ + 2 : ℕ) : ℝ) ≤ δ₀ * P := by
    have hf := Nat.floor_le (show 0 ≤ δ * (P : ℝ) by positivity)
    have hδle : δ ≤ δ₀ / 4 := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg (α := ℝ) P)
    push_cast
    nlinarith
  have hl := hr (2 * T + 1) (2 * ⌊δ * P⌋₊ + 2) P (Nat.cast_nonneg _) hn hs
  have hbits : Real.logb 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)) ≤ ε / 2 * P := by
    dsimp only [blockSparseMenu]
    rw [Real.logb, div_le_iff₀ hlog]
    convert hl using 1
    ring
  have hc := clog_two_le_logb_add_one (blockSparseMenu_pos (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2))
  linarith

def carrierStateBound (k a Q T m : ℕ) : ℕ :=
  1 + Q * carrierOverhead k T *
    2 ^ ((k + 1) * Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * m + 2)))

/-- The exact finite state bill fits the one-head budget after paying the
source controller, every syndrome, polynomial metadata and the default state.
The source controller may itself grow linearly with the input length. -/
theorem carrier_state_bits_small (k a : ℕ) (hk : 1 ≤ k) {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ P₀ : ℕ, ∀ P, P₀ ≤ P →
      ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) → ∀ Q q : ℕ,
        Q ≤ 2 ^ q → (q : ℝ) ≤ ρ * P / 2 →
        (Nat.clog 2 (carrierStateBound k a Q T ⌊δ * P⌋₊) : ℝ) ≤ ρ * P := by
  have hkpos : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨δ, hδ, hδcap, P₁, hhash⟩ := carrier_hash_bits_small a hC
    (show 0 < ρ / (8 * ((k : ℝ) + 1)) by positivity)
  obtain ⟨P₂, hmenu⟩ := carrierOverhead_bits_small (C := C) hk
    (show 0 < ρ / 8 by positivity)
  refine ⟨δ, hδ, hδcap, max P₁ (max P₂ ⌈8 / ρ⌉₊), ?_⟩
  intro P hP T hT Q q hQ hq
  have hr := hhash P ((le_max_left _ _).trans hP) T hT
  have hm := hmenu P ((le_max_left _ _).trans ((le_max_right _ _).trans hP)) T hT
  have hlarge : 8 / ρ ≤ (P : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right P₂ ⌈8 / ρ⌉₊).trans ((le_max_right P₁ _).trans hP))
  have hconst : 1 ≤ ρ * P / 8 := by
    have hh := (div_le_iff₀ hρ).mp hlarge
    linarith
  have hsyndrome : ((k + 1 : ℕ) : ℝ) *
      (Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)) : ℝ) ≤ ρ * P / 8 := by
    have hh := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) (k + 1))
    have he : ((k + 1 : ℕ) : ℝ) * (ρ / (8 * ((k : ℝ) + 1)) * P) = ρ * P / 8 := by
      push_cast
      field_simp
    exact he ▸ hh
  have hb := clog_state_product hQ (carrierOverhead k T)
    ((k + 1) * Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)))
  have hbr : (Nat.clog 2 (carrierStateBound k a Q T ⌊δ * P⌋₊) : ℝ) ≤
      1 + (q : ℝ) + (Nat.clog 2 (carrierOverhead k T) : ℝ) +
        ((k + 1 : ℕ) : ℝ) *
          (Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)) : ℝ) := by
    exact_mod_cast hb
  nlinarith [mul_nonneg hρ.le (Nat.cast_nonneg (α := ℝ) P)]

end AdaptiveTransfer
