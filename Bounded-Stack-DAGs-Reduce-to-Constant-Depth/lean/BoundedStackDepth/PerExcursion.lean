import BoundedStackDepth.BandSums

/-!
# The per-excursion ladder sum

The arithmetic of Theorem A: the ladder hops of an excursion of height `H ≥ 1` cost at most `6H` in
total. Write `B = band H`. Level `0` costs at most `B`, and level `d ∈ [1, H)` costs at most
`(B − band (d − 1)) + (B − uband H d)`, its p-side and u-side band deficits. All subtractions are
truncated subtractions of natural numbers. Both sides are computed exactly.

* `uband H d`: the u-side band at level `d`. With `e = ⌈log₂ d⌉`, it is `band (2^e − d)` below the
  top passage (`2^e ≤ H − 1`) and `band (H − 1)` above it.
* `sum_range_two_pow_sub_band`: a dyadic block of the u-side, exactly:
  `∑_{w < 2^e} (C − band w) + 2 = 2^e (C + 2 − e)` for `e ≤ C + 1`.
* `sum_sub_band_two_pow_clog`: the u-side up to a passage, exactly:
  `∑_{d=1}^{2^e} (C − band (2^{⌈log₂ d⌉} − d)) + 2e + 4 = 2^e (C + 4 − e)` for `e ≤ C + 1`; the
  levels `d ∈ (2^e, 2^{e+1}]` reindex by `w = 2^{e+1} − d` to the block `w < 2^e`.
* `ladder_sum_le_six`: the total is at most `6H`. With `e = band (H − 1)`, so that `2^e ≤ H − 1`
  and `B ∈ {e, e + 1}`, the p-side is at most `2^{B+1} − 2` (`sum_band_sub_eq`), the u-side up to
  the top passage `2^e` is `2^e (B + 4 − e) − 2e − 4`, and each level above it costs at most `1`.
  The two cases `B = e` and `B = e + 1` (then `H = 2^{e+1}`) give at most `6H`.
* `sum_range_le_six_of_ladder`: the same for level costs `c d` bounded by the terms of the sum.
-/

namespace BoundedStackDepth

open Finset

/-- The u-side band at level `d`: below the top passage, `d` lies in the block of the least power
`2^e ≥ d`, and the band is `band (2^e - d)`; above it, `band (H - 1)`. -/
def uband (H d : ℕ) : ℕ :=
  if 2 ^ Nat.clog 2 d ≤ H - 1 then band (2 ^ Nat.clog 2 d - d) else band (H - 1)

/-! ### Dyadic blocks -/

/-- On the dyadic block `[2^e, 2^{e+1})` the band is `e`. -/
theorem band_eq_of_mem_Ico {e w : ℕ} (h : w ∈ Ico (2 ^ e) (2 ^ (e + 1))) : band w = e :=
  Nat.log_eq_of_pow_le_of_lt_pow (mem_Ico.1 h).1 (mem_Ico.1 h).2

/-- On `(2^e, 2^{e+1}]` the least power of two at least `d` is `2^{e+1}`: `⌈log₂ d⌉ = e + 1`. -/
theorem clog_eq_of_lt_of_le {e d : ℕ} (h₁ : 2 ^ e < d) (h₂ : d ≤ 2 ^ (e + 1)) :
    Nat.clog 2 d = e + 1 :=
  le_antisymm (Nat.clog_le_of_le_pow h₂) ((Nat.lt_clog_iff_pow_lt (by norm_num)).2 h₁)

/-- **A dyadic block.** `∑_{w < 2^e} (C − band w) + 2 = 2^e (C + 2 − e)` for `e ≤ C + 1`: the
levels `w ∈ [2^e, 2^{e+1})` add `2^e (C − e)` (induction on `e`). -/
theorem sum_range_two_pow_sub_band (C : ℕ) : ∀ {e : ℕ}, e ≤ C + 1 →
    ∑ w ∈ range (2 ^ e), (C - band w) + 2 = 2 ^ e * (C + 2 - e)
  | 0, _ => by simp
  | e + 1, he => by
    have ih := sum_range_two_pow_sub_band C (e := e) (by omega)
    have hterm : ∀ w ∈ Ico (2 ^ e) (2 ^ (e + 1)), C - band w = C - e := fun w hw => by
      rw [band_eq_of_mem_Ico hw]
    have hblk : ∑ w ∈ Ico (2 ^ e) (2 ^ (e + 1)), (C - band w) = 2 ^ e * (C - e) := by
      rw [sum_congr rfl hterm, sum_const, Nat.card_Ico, smul_eq_mul, pow_succ,
        show 2 ^ e * 2 - 2 ^ e = 2 ^ e by omega]
    rw [← sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ e)), hblk,
      pow_succ]
    obtain ⟨m, rfl⟩ : ∃ m, C = e + m := ⟨C - e, by omega⟩
    rw [show e + m + 2 - e = m + 2 by omega] at ih
    rw [show e + m - e = m by omega, show e + m + 2 - (e + 1) = m + 1 by omega]
    linarith

/-- **The u-side up to a passage.** For `e ≤ C + 1`,
`∑_{d=1}^{2^e} (C − band (2^{⌈log₂ d⌉} − d)) + 2e + 4 = 2^e (C + 4 − e)`. The levels
`d ∈ (2^e, 2^{e+1}]` reindex by `w = 2^{e+1} − d` to the block `w < 2^e`
(`sum_range_two_pow_sub_band`). -/
theorem sum_sub_band_two_pow_clog (C : ℕ) : ∀ {e : ℕ}, e ≤ C + 1 →
    ∑ d ∈ Ico 1 (2 ^ e + 1), (C - band (2 ^ Nat.clog 2 d - d)) + 2 * e + 4 =
      2 ^ e * (C + 4 - e)
  | 0, _ => by simp [Nat.clog_one_right]
  | e + 1, he => by
    have ih := sum_sub_band_two_pow_clog C (e := e) (by omega)
    have hb := sum_range_two_pow_sub_band C (e := e) (by omega)
    have hp : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
    have hpos : 0 < 2 ^ e := Nat.two_pow_pos e
    have hblk : ∑ d ∈ Ico (2 ^ e + 1) (2 ^ (e + 1) + 1), (C - band (2 ^ Nat.clog 2 d - d)) =
        ∑ w ∈ range (2 ^ e), (C - band w) := by
      refine sum_nbij' (fun d => 2 ^ (e + 1) - d) (fun w => 2 ^ (e + 1) - w) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [mem_Ico, mem_range] at hd ⊢
        omega
      · intro w hw
        simp only [mem_Ico, mem_range] at hw ⊢
        omega
      · intro d hd
        simp only [mem_Ico] at hd
        omega
      · intro w hw
        simp only [mem_range] at hw
        omega
      · intro d hd
        simp only [mem_Ico] at hd
        rw [clog_eq_of_lt_of_le (e := e) (by omega) (by omega)]
    rw [← sum_Ico_consecutive _ (by omega : 1 ≤ 2 ^ e + 1)
      (by omega : 2 ^ e + 1 ≤ 2 ^ (e + 1) + 1), hblk]
    obtain ⟨m, rfl⟩ : ∃ m, C = e + m := ⟨C - e, by omega⟩
    rw [show e + m + 4 - e = m + 4 by omega] at ih
    rw [show e + m + 2 - e = m + 2 by omega] at hb
    rw [show e + m + 4 - (e + 1) = m + 3 by omega, hp]
    linarith

/-! ### The ladder sum -/

/-- **The ladder sum, constant `6`.**
`band H + ∑_{d=1}^{H−1} ((band H − band (d − 1)) + (band H − uband H d)) ≤ 6H`. -/
theorem ladder_sum_le_six (H : ℕ) :
    band H + ∑ d ∈ Ico 1 H, ((band H - band (d - 1)) + (band H - uband H d)) ≤ 6 * H := by
  rcases Nat.lt_or_ge H 2 with hH | hH
  · interval_cases H <;> simp [band]
  have h4 := sum_band_sub_eq H
  set B := band H
  set e := band (H - 1) with he
  have h2e : 2 ^ e ≤ H - 1 := pow_band_le (by omega)
  have h2B : 2 ^ B ≤ H := pow_band_le (by omega)
  have hlt : H - 1 < 2 ^ (e + 1) := lt_pow_band_succ (H - 1)
  have hBe : B ≤ e + 1 := by
    have h := band_succ (H - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ H)] at h
    omega
  have heB : e ≤ B := band_mono (by omega)
  -- The p-side, exactly (`sum_band_sub_eq`): at most `2^{B+1} − 2`.
  have hP : ∑ d ∈ Ico 1 H, (B - band (d - 1)) + 2 ≤ 2 ^ (B + 1) := by
    have h1 : ∑ d ∈ Ico 1 H, (B - band (d - 1)) ≤ ∑ j ∈ range H, (B - band j) := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      exact sum_le_sum_of_subset (range_subset_range.2 (Nat.sub_le H 1))
    have h2 : ∑ j ∈ range H, (B - band j) = B + ∑ j ∈ Ico 1 H, (B - band j) := by
      rw [sum_range_eq_add_Ico _ (by omega : 0 < H), band_zero, Nat.sub_zero]
    have h3 : ∑ j ∈ Ico 1 H, (B - band j) ≤ ∑ j ∈ Icc 1 H, (B - band j) :=
      sum_le_sum_of_subset Ico_subset_Icc_self
    omega
  -- The u-side up to the top passage `2^e`.
  have hU₁ : ∑ d ∈ Ico 1 (2 ^ e + 1), (B - uband H d) + 2 * e + 4 = 2 ^ e * (B + 4 - e) := by
    have hterm : ∀ d ∈ Ico 1 (2 ^ e + 1), B - uband H d = B - band (2 ^ Nat.clog 2 d - d) :=
      fun d hd => by
        have hc : Nat.clog 2 d ≤ e := Nat.clog_le_of_le_pow (by simp only [mem_Ico] at hd; omega)
        have h' : 2 ^ Nat.clog 2 d ≤ H - 1 := (Nat.pow_le_pow_right (by norm_num) hc).trans h2e
        rw [uband, ite_eq_left h']
    rw [sum_congr rfl hterm]
    exact sum_sub_band_two_pow_clog B (by omega)
  -- The u-side above the top passage: each level costs `B − band (H − 1) ≤ 1`.
  have hU₂ : ∑ d ∈ Ico (2 ^ e + 1) H, (B - uband H d) ≤ H - (2 ^ e + 1) := by
    have hterm : ∀ d ∈ Ico (2 ^ e + 1) H, B - uband H d ≤ 1 := fun d hd => by
      have hc : e < Nat.clog 2 d :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by simp only [mem_Ico] at hd; omega)
      have h' : 2 ^ (e + 1) ≤ 2 ^ Nat.clog 2 d := Nat.pow_le_pow_right (by norm_num) hc
      rw [uband, ite_eq_right (by omega)]
      omega
    calc ∑ d ∈ Ico (2 ^ e + 1) H, (B - uband H d) ≤ ∑ _d ∈ Ico (2 ^ e + 1) H, 1 :=
          sum_le_sum hterm
      _ = H - (2 ^ e + 1) := by simp
  have hsplit : ∑ d ∈ Ico 1 H, (B - uband H d) =
      ∑ d ∈ Ico 1 (2 ^ e + 1), (B - uband H d) + ∑ d ∈ Ico (2 ^ e + 1) H, (B - uband H d) :=
    (sum_Ico_consecutive _ (by omega) (by omega)).symm
  rw [sum_add_distrib, hsplit]
  rw [pow_succ] at hlt
  -- `B = e`, or `B = e + 1` and `H = 2^{e+1}`
  rcases (show B = e ∨ B = e + 1 by omega) with hB | hB
  · rw [show B + 4 - e = 4 by omega] at hU₁
    rw [show B + 1 = e + 1 by omega, pow_succ] at hP
    omega
  · rw [show B + 4 - e = 5 by omega] at hU₁
    rw [show B + 1 = e + 1 + 1 by omega, pow_succ, pow_succ] at hP
    rw [hB, pow_succ] at h2B
    omega

/-- **Level costs, constant `6`.** If `c 0 ≤ band H` and
`c d ≤ (band H − band (d − 1)) + (band H − uband H d)` for `1 ≤ d < H`, then `∑_{d<H} c d ≤ 6H`. -/
theorem sum_range_le_six_of_ladder {H : ℕ} (c : ℕ → ℕ) (h₀ : c 0 ≤ band H)
    (hc : ∀ d, 1 ≤ d → d < H → c d ≤ (band H - band (d - 1)) + (band H - uband H d)) :
    ∑ d ∈ range H, c d ≤ 6 * H := by
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  rw [sum_range_eq_add_Ico _ hH]
  exact (add_le_add h₀ (sum_le_sum fun d hd => hc d (mem_Ico.1 hd).1 (mem_Ico.1 hd).2)).trans
    (ladder_sum_le_six H)

end BoundedStackDepth
