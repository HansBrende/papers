import Transpose.Tape.PPrime
import Transpose.Tape.Witnesses
import Transpose.Tape.WitnessDD

/-!
# Theorem P′: examples and corollaries

* `tr2dd_transposes`, `tr2dd_hrun`, `tr2dd_not_oblivious`: the hypotheses of Theorem P′ hold for a
  machine whose running time depends on the input.
* `theoremPprime_no_five_pass`: the conclusion is a real constraint. With one work tape, at most
  `2^8` states and `4` work symbols, halting within `2^30 ≥ L` steps on `1024 × 1024` inputs with
  `10`-bit entries, `5` passes are impossible (an `example` checks that the same bound does not
  exclude `6`).
* `theoremPprime_ratio`: the ratio form `𝓗 ≥ n / (2 + (σ + γ + 1)/b)` for `b ≥ 1` (every `n`), from
  the per-`n` form and `structBits_le`.
* `theoremPprime_linearTime`: Theorem P′ for a machine satisfying the frozen `TransposesWithin`
  with a linear time bound.
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### A data-dependent witness -/

theorem tr2dd_halts : ∀ a b c d : Bool,
    HaltsAt Witness.tr2dd [a, b, c, d] (if a then 6 else 5) := by
  intro a b c d
  refine ⟨?_, ?_⟩
  · revert a b c d; decide
  · revert a b c d; decide

theorem tr2dd_output : ∀ a b c d : Bool,
    (run Witness.tr2dd [a, b, c, d] (if a then 6 else 5)).outRev.reverse = [a, c, b, d] := by
  decide

theorem tr2dd_mono : ∀ a b c d : Bool, ∀ τ < 6,
    (run Witness.tr2dd [a, b, c, d] τ).inPos ≤ (run Witness.tr2dd [a, b, c, d] (τ + 1)).inPos := by
  decide

theorem tr2dd_transposes : Transposes Witness.tr2dd 2 1 := by
  intro A
  refine ⟨6, (computesWithin_iff _ _).2 ⟨if A 0 0 0 then 6 else 5, ?_, ?_, ?_⟩⟩
  · split <;> omega
  · rw [tr2_encode]; exact tr2dd_halts _ _ _ _
  · rw [tr2_encode, tr2_encode, tr2dd_output]
    rfl

theorem tr2dd_hrun : ∀ w ∈ matrixInputs 2 1, ∃ T' ≤ 6, ∃ p,
    HaltsAt Witness.tr2dd w T' ∧ PassPartition Witness.tr2dd w T' 1 p := by
  intro w hw
  rw [matrixInputs_eq] at hw
  obtain ⟨a, b, c, d, rfl⟩ := length_four hw
  refine ⟨if a then 6 else 5, by split <;> omega,
    fun i => if i = 0 then 0 else (if a then 6 else 5), tr2dd_halts a b c d, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst this; simp
  · intro i hi
    have : i = 0 := by omega
    subst this
    refine ⟨Or.inl ?_, fun t => t.elim0⟩
    intro τ _ hτ
    simp only [inTraj]
    exact tr2dd_mono a b c d τ (by split at hτ <;> simp at hτ <;> omega)

theorem tr2dd_not_oblivious : ∀ T, ¬ ObliviousOn Witness.tr2dd (matrixInputs 2 1) T := by
  intro T h
  have h1 := h.1 [true, false, false, false] (by rw [matrixInputs_eq]; rfl)
  have h2 := h.1 [false, false, false, false] (by rw [matrixInputs_eq]; rfl)
  have e1 := haltsAt_unique h1 (tr2dd_halts true false false false)
  have e2 := haltsAt_unique h2 (tr2dd_halts false false false false)
  simp at e1 e2
  omega

/-! ### Non-triviality -/

/-- **Five passes are impossible** for a machine with one work tape, at most `2^8` states and at
most `4` work symbols that halts within `2^30` steps on every `1024 × 1024` input with `10`-bit
entries (here `L = 10 · 2^20 < 2^30`). -/
theorem theoremPprime_no_five_pass (M : TM) (hk : M.k = 1) (hq : M.q + 1 ≤ 2 ^ 8)
    (hg : M.g + 1 ≤ 2 ^ 2) (hcorr : Transposes M 1024 10)
    (hrun : ∀ w ∈ matrixInputs 1024 10, ∃ T' ≤ 2 ^ 30, ∃ p,
      HaltsAt M w T' ∧ PassPartition M w T' 5 p) : False := by
  have h := theoremPprime_div hcorr hrun
  have h1 : Nat.clog 2 (M.q + 1) ≤ 8 := Nat.clog_le_of_le_pow hq
  have h2 : Nat.clog 2 (M.g + 1) ≤ 2 := Nat.clog_le_of_le_pow hg
  have h3 : Nat.clog 2 (2 * 2 ^ 30 + 1) ≤ 32 := Nat.clog_le_of_le_pow (by norm_num)
  have hA : addrCount M.k 5 = 31 := by rw [hk]; decide
  rw [hA, hk] at h
  omega

-- The same bound does not exclude `6` passes, so the cut-off above is real.
example : ¬ (1024 * 10 > addrCount 1 6 * (2 * 10 + (8 + 1 * 2 + (1 + 4) * 32))) := by
  decide

/-! ### The ratio form and the frozen statement -/

/-- **Theorem P′ in ratio form** `𝓗 ≥ n / (2 + (σ + γ + 1)/b)`, for every `n` (`b ≥ 1`):
from the per-`n` form `n b ≤ 𝓗 (2b + σ + (k+4)⌈log₂(2T+1)⌉)` and `structBits_le`. -/
theorem theoremPprime_ratio {M : TM} {n b T r : ℕ} (hb : 1 ≤ b)
    (hcorr : Transposes M n b)
    (hrun : ∀ w ∈ matrixInputs n b, ∃ T' ≤ T, ∃ p, HaltsAt M w T' ∧ PassPartition M w T' r p) :
    ((n : ℝ) / (2 + (((Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) : ℕ) : ℝ) +
        ((Nat.clog 2 r + 2 * (M.k + 2) * Nat.clog 2 (2 * T + 3) : ℕ) : ℝ) + 1) / b))
      ≤ (addrCount M.k r : ℝ) := by
  set σ : ℕ := Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)
  set γ : ℕ := Nat.clog 2 r + 2 * (M.k + 2) * Nat.clog 2 (2 * T + 3)
  have h : n * b ≤ addrCount M.k r * (2 * b + σ + γ + 1) :=
    (theoremPprime_div hcorr hrun).trans
      (Nat.mul_le_mul_left _ (by have := structBits_le M.k T r; omega))
  have hR : (n : ℝ) * b ≤ addrCount M.k r * (2 * b + σ + γ + 1) := by exact_mod_cast h
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ (by positivity), ← mul_le_mul_iff_left₀ hbR]
  calc (n : ℝ) * b ≤ _ := hR
    _ = _ := by field_simp; ring

/-- **Theorem P′ for the frozen statement**, for every `n` (at `n = 0` the left side is `0`). A
machine that transposes within `c (L + 1)` steps (`TransposesWithin`), and whose runs on `n × n`
inputs have greedy pass counts at most `r`, satisfies the P′ bound with `T = c (L + 1)`. -/
theorem theoremPprime_linearTime {M : TM} {c : ℕ} (h : TransposesWithin M (fun L => c * (L + 1)))
    {n r : ℕ}
    (hr : ∀ w ∈ matrixInputs n (entryBits n), ∀ T', HaltsAt M w T' → greedyPasses M w T' ≤ r) :
    n * n * entryBits n ≤ addrCount M.k r * (n * (2 * entryBits n +
      (Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1) +
        (M.k + 4) * Nat.clog 2 (2 * (c * (inputLength n + 1)) + 1)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  apply theoremPprime_greedy (transposes_of_transposesWithin h n hn)
  rintro w ⟨A, rfl⟩
  obtain ⟨T', hT', hh, -⟩ := (computesWithin_iff _ _).1 (h n hn A)
  exact ⟨T', hT', hh, hr _ ⟨A, rfl⟩ T' hh⟩

end Transpose.Tape.Impl
