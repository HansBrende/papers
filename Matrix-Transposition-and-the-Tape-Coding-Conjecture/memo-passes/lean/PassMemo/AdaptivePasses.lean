import PassMemo.RunLength
import Transpose.Tape.PPrime

/-! Time-free consequences of the original adaptive information theorem. -/

namespace PassMemo

open Transpose Transpose.Tape Transpose.Tape.Impl

def stateBits (M : TM) : ℕ := Nat.clog 2 (M.q + 1) + M.k * Nat.clog 2 (M.g + 1)

def adaptiveCost (M : TM) (L r : ℕ) : ℕ :=
  stateBits M + (M.k + 4) * (2 + Nat.clog 2 (L + 1) + r * Nat.clog 2 (passFactor M))

def passConstant (M : TM) : ℕ :=
  2 + stateBits M + (M.k + 4) * (5 + Nat.clog 2 (passFactor M))

theorem bounded_runs {M : TM} {d b r : ℕ}
    (hrun : ∀ w ∈ matrixInputs d b, ∃ T p, HaltsAt M w T ∧ PassPartition M w T r p) :
    ∀ w ∈ matrixInputs d b, ∃ T ≤ timeBound M (d * d * b) r, ∃ p,
      HaltsAt M w T ∧ PassPartition M w T r p := by
  intro w hw
  obtain ⟨T, p, hh, hp⟩ := hrun w hw
  have hlen : w.length = d * d * b := by
    rw [matrixInputs_eq] at hw
    exact hw
  exact ⟨T, hlen ▸ halting_time_le hh hp, p, hh, hp⟩

/-- Grouped adaptive information bound, with no supplied runtime bound. -/
theorem time_free_grouped {M : TM} {d b r γ : ℕ} (hcorr : Transposes M d b)
    (hrun : ∀ w ∈ matrixInputs d b, ∃ T p, HaltsAt M w T ∧ PassPartition M w T r p)
    (hγ : 1 ≤ γ) :
    d * d * b ≤ addrCount M.k r * ((γ + 1) * d * b + numGroups d γ *
      adaptiveCost M (d * d * b) r) := by
  have h := theoremPprime_grouped_bits hcorr (bounded_runs hrun) hγ
  apply h.trans
  unfold adaptiveCost stateBits
  gcongr
  exact timeBound_log M _ _

/-- Correctness and halting may be restricted to the specified set of inputs.
The co-entropy payment is still made once per column group. -/
theorem time_free_grouped_on {M : TM} {d b r γ m : ℕ} {W : Set (List Bool)}
    (hrun : ∀ w ∈ W, ∃ T p, HaltsAt M w T ∧ PassPartition M w T r p ∧
      ∃ A : Transpose.Matrix, w = encode d b A ∧
        (run M w T).outRev.reverse = encode d b (transpose A))
    (hγ : 1 ≤ γ) (hco : 2 ^ (d * d * b) ≤ 2 ^ m * W.ncard) :
    d * d * b ≤ numGroups d γ * m + addrCount M.k r *
      ((γ + 1) * d * b + numGroups d γ * adaptiveCost M (d * d * b) r) := by
  have hb : ∀ w ∈ W, ∃ T ≤ timeBound M (d * d * b) r, ∃ p,
      PassPartition M w T r p ∧ ∃ A : Transpose.Matrix, w = encode d b A ∧
        (run M w T).outRev.reverse = encode d b (transpose A) := by
    intro w hw
    obtain ⟨T, p, hh, hp, A, heq, hout⟩ := hrun w hw
    have hlen : w.length = d * d * b := by rw [heq, length_encode]
    exact ⟨T, hlen ▸ halting_time_le hh hp, p, hp, A, heq, hout⟩
  have h := theoremPprime_grouped_on_bits hb hγ hco
  apply h.trans
  unfold adaptiveCost stateBits
  gcongr
  exact timeBound_log M _ _

theorem time_free_div {M : TM} {d b r : ℕ} (hcorr : Transposes M d b)
    (hrun : ∀ w ∈ matrixInputs d b, ∃ T p, HaltsAt M w T ∧ PassPartition M w T r p) :
    d * b ≤ addrCount M.k r * (2 * b + adaptiveCost M (d * d * b) r) := by
  have h := theoremPprime_div hcorr (bounded_runs hrun)
  apply h.trans
  unfold adaptiveCost stateBits
  gcongr
  exact timeBound_log M _ _

theorem input_log_le {d b : ℕ} (hd : d ≤ 2 ^ b) :
    Nat.clog 2 (d * d * b + 1) ≤ 3 * b := by
  have hb : b < 2 ^ b := Nat.lt_two_pow_self
  have h1 : d * d * b ≤ (2 ^ b * 2 ^ b) * b :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hd hd)
  have h2 : (2 ^ b * 2 ^ b) * b < (2 ^ b * 2 ^ b) * 2 ^ b :=
    Nat.mul_lt_mul_of_pos_left hb (by positivity)
  have hp : 2 ^ (3 * b) = (2 ^ b * 2 ^ b) * 2 ^ b := by ring
  apply Nat.clog_le_of_le_pow
  rw [hp]
  omega

theorem small_pass_cost {M : TM} {d b r : ℕ} (hb : 1 ≤ b)
    (hd : d ≤ 2 ^ b) (hr : r ≤ b) :
    2 * b + adaptiveCost M (d * d * b) r ≤ passConstant M * b := by
  have hlog := input_log_le hd
  have hr' := Nat.mul_le_mul_right (Nat.clog 2 (passFactor M)) hr
  have hstate := Nat.mul_le_mul_left (stateBits M) hb
  have hcost : 2 + Nat.clog 2 (d * d * b + 1) + r * Nat.clog 2 (passFactor M) ≤
      (5 + Nat.clog 2 (passFactor M)) * b := by nlinarith
  have hmul := Nat.mul_le_mul_left (M.k + 4) hcost
  unfold adaptiveCost passConstant
  nlinarith

/-- Multiplicative form of `r ≥ log_(k+1) d - O_M(1)`, valid for every
positive width with `d ≤ 2^b`, without a time hypothesis. -/
theorem logarithmic_pass_power {M : TM} {d b r : ℕ} (hk : 1 ≤ M.k)
    (hb : 1 ≤ b) (hd : d ≤ 2 ^ b) (hcorr : Transposes M d b)
    (hrun : ∀ w ∈ matrixInputs d b, ∃ T p, HaltsAt M w T ∧ PassPartition M w T r p) :
    M.k * d ≤ passConstant M * (M.k + 1) ^ r := by
  by_cases hr : r ≤ b
  · have h := time_free_div hcorr hrun
    have hc := Nat.mul_le_mul_left (addrCount M.k r) (small_pass_cost (M := M) hb hd hr)
    have hdH : d ≤ addrCount M.k r * passConstant M := by nlinarith
    have hkm := Nat.mul_le_mul_left M.k hdH
    have haddr := addrCount_mul M.k r
    nlinarith
  · have hd' : d ≤ (M.k + 1) ^ r := calc
      d ≤ 2 ^ b := hd
      _ ≤ (M.k + 1) ^ b := Nat.pow_le_pow_left (by omega) b
      _ ≤ (M.k + 1) ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have hA : M.k ≤ passConstant M := by unfold passConstant; nlinarith
    exact (Nat.mul_le_mul_left M.k hd').trans (Nat.mul_le_mul_right _ hA)

/-- The canonical width of the original frozen statement is included. -/
theorem canonical_pass_power {M : TM} {d r : ℕ} (hk : 1 ≤ M.k)
    (hcorr : Transposes M d (entryBits d))
    (hrun : ∀ w ∈ matrixInputs d (entryBits d), ∃ T p,
      HaltsAt M w T ∧ PassPartition M w T r p) :
    M.k * d ≤ passConstant M * (M.k + 1) ^ r := by
  apply logarithmic_pass_power hk (by unfold entryBits; omega) ?_ hcorr hrun
  unfold entryBits
  have := Nat.lt_log2_self (n := d - 1)
  omega

/-- Explicit real-logarithm version of the canonical-width conclusion. -/
theorem canonical_logarithmic_passes {M : TM} {d r : ℕ} (hk : 1 ≤ M.k) (hd : 1 ≤ d)
    (hcorr : Transposes M d (entryBits d))
    (hrun : ∀ w ∈ matrixInputs d (entryBits d), ∃ T p,
      HaltsAt M w T ∧ PassPartition M w T r p) :
    Real.logb (M.k + 1) d -
      (Real.logb (M.k + 1) (passConstant M) - Real.logb (M.k + 1) M.k) ≤ r := by
  have hkpos : (0 : ℝ) < M.k := by exact_mod_cast hk
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : (1 : ℝ) < M.k + 1 := by linarith
  have hApos : (0 : ℝ) < passConstant M := by
    exact_mod_cast (show 0 < passConstant M by unfold passConstant; omega)
  have hpow : (M.k : ℝ) * d ≤ (passConstant M : ℝ) * ((M.k : ℝ) + 1) ^ r := by
    exact_mod_cast canonical_pass_power hk hcorr hrun
  have hl := Real.logb_le_logb_of_le hbase (by positivity) hpow
  rw [Real.logb_mul (ne_of_gt hkpos) (ne_of_gt hdpos),
    Real.logb_mul (ne_of_gt hApos) (by positivity),
    Real.logb_pow, Real.logb_self_eq_one hbase, mul_one] at hl
  linarith

/-- In particular the previous bounded-runtime consequence follows by dropping
its runtime premise; neither the finite-time P-prime inequality nor its
nonhalting-prefix version is being replaced. -/
theorem bounded_runtime_corollary {M : TM} {d r T₀ : ℕ} (hk : 1 ≤ M.k)
    (hcorr : Transposes M d (entryBits d))
    (hrun : ∀ w ∈ matrixInputs d (entryBits d), ∃ T ≤ T₀, ∃ p,
      HaltsAt M w T ∧ PassPartition M w T r p) :
    M.k * d ≤ passConstant M * (M.k + 1) ^ r := by
  apply canonical_pass_power hk hcorr
  intro w hw
  obtain ⟨T, _, p, hh, hp⟩ := hrun w hw
  exact ⟨T, p, hh, hp⟩

end PassMemo
