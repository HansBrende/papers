import BoundedNesting.MAverage
import BoundedNesting.TheoremF

/-!
# Theorem M: one arbitrary head

Let `x0` be any walk (its long hops are the *chords*) and `H'` a set of long hops of walks `xs i`,
`i < k`, of owner-load at most `ℓ` for owners `own` strictly inside the hops, with the families of
`Families.lean` and `N = 2kℓ` virtual heads. The DAG `G` has the vertices `[0, T)`, the state edges
`t → t - 1`, and the hop edges `u → p` for the chords `(p, u) ∈ hops x0 T` and for the hop pairs of
`H'`. Pauses are allowed.

`theoremM`: let `q ≥ 1`, `h ≥ 0` and `β_0 < … < β_(q-1)`, and suppose that the band `λ(d_F)` of every
family lies in a window `[β_j, β_j + h]`. For `0 < ε ≤ 1` put `w = 2^⌈log₂(8(4+2k)/ε)⌉` (`mw`),
`K₀ = ⌈8(w+1)/ε⌉` (`mK0`) and `K = ⌈(8/ε)(q + qN + 64q²N²2^h/ε + qwN + N²2^(h+1))⌉` (`mK`). Then `G`
has a cut of at most `εT` edges such that every path avoiding it carries fewer than
`DM = K₀ K^(2q)` hop edges.

The cut is that of the strip label (`cutSM`, `cutHM`) at a residue `ρ < W q` and offsets `ω` whose
cost is at most the average (`sum_cut_le`), for the widths `W 0 = w` and
`W (j+1) = 2^max(log₂ w, clog₂ ⌈64qN2^(β_j+h)/ε⌉)` (`mwidth`); `costB_le` is the arithmetic.

`theoremM_owner`: the same for the owners of the paper (`hopOwner`).
-/

namespace BoundedNesting

open Finset

/-! ### Parameters -/

/-- `2^(clog₂ n) ≤ 2n` for `n ≥ 1`. -/
theorem two_pow_clog_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · simp [Nat.clog_one_right]
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn2
    have h2 := Nat.clog_pos (b := 2) (by norm_num) hn2
    have h3 : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel h2]
    omega

/-- The exponent `⌈log₂(8(4+2k)/ε)⌉` of `w`. -/
noncomputable def mExp (k : ℕ) (ε : ℝ) : ℕ := ⌈Real.logb 2 (8 * (4 + 2 * (k : ℝ)) / ε)⌉₊

/-- The level-`0` width `w = 2^⌈log₂(8(4+2k)/ε)⌉`. -/
noncomputable def mw (k : ℕ) (ε : ℝ) : ℕ := 2 ^ mExp k ε

/-- The radix `K₀ = ⌈8(w+1)/ε⌉` of the level-`0` digit. -/
noncomputable def mK0 (k : ℕ) (ε : ℝ) : ℕ := ⌈8 * ((mw k ε : ℝ) + 1) / ε⌉₊

/-- The radix `K = ⌈(8/ε)(q + qN + 64q²N²2^h/ε + qwN + N²2^(h+1))⌉` of the other digits, where
`N = 2kℓ`. -/
noncomputable def mK (k ℓ q h : ℕ) (ε : ℝ) : ℕ :=
  ⌈8 / ε * ((q : ℝ) + q * ((2 * k * ℓ : ℕ) : ℝ) +
    64 * (q : ℝ) ^ 2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ h / ε +
    q * (mw k ε : ℝ) * ((2 * k * ℓ : ℕ) : ℝ) + ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ (h + 1))⌉₊

/-- The depth bound `D_M(k, ℓ, q, h, ε) = K₀ K^(2q)` of Theorem M. -/
noncomputable def DM (k ℓ q h : ℕ) (ε : ℝ) : ℕ := mK0 k ε * mK k ℓ q h ε ^ (2 * q)

theorem one_le_mExp {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ mExp k ε := by
  unfold mExp
  refine Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr
    (Real.logb_pos (by norm_num) ?_)))
  rw [lt_div_iff₀ hε]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem le_mw {k : ℕ} {ε : ℝ} (hε : 0 < ε) : 8 * (4 + 2 * (k : ℝ)) / ε ≤ mw k ε := by
  have hx : 0 < 8 * (4 + 2 * (k : ℝ)) / ε := by positivity
  calc 8 * (4 + 2 * (k : ℝ)) / ε ≤ ⌈8 * (4 + 2 * (k : ℝ)) / ε⌉₊ := Nat.le_ceil _
    _ ≤ (mw k ε : ℝ) := by
        unfold mw mExp
        exact_mod_cast ceil_le_two_pow_clog hx

theorem mK0_pos {k : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < mK0 k ε := Nat.ceil_pos.mpr (by positivity)

theorem mK_pos {k ℓ q h : ℕ} {ε : ℝ} (hε : 0 < ε) (hq : 1 ≤ q) : 0 < mK k ℓ q h ε := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine Nat.ceil_pos.mpr (mul_pos (by positivity) ?_)
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hq' (by positivity)) (by positivity)) (by positivity)) (by positivity)

/-! ### The widths -/

/-- The exponent of the width of level `i`: `m` at level `0`, and at level `j + 1` the larger of `m`
and `clog₂ ⌈64 q N 2^(β_j + h)/ε⌉` (with `j` clamped to `q - 1`). -/
noncomputable def wexp (m q N h : ℕ) (β : Fin q → ℕ) (ε : ℝ) (hq : 1 ≤ q) (i : ℕ) : ℕ :=
  if i = 0 then m else
    max m (Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β ⟨min (i - 1) (q - 1), by omega⟩ + h) / ε⌉₊)

/-- The level widths `W i = 2^(wexp i)`. -/
noncomputable def mwidth (m q N h : ℕ) (β : Fin q → ℕ) (ε : ℝ) (hq : 1 ≤ q) (i : ℕ) : ℕ :=
  2 ^ wexp m q N h β ε hq i

section Widths

variable {m q N h : ℕ} {β : Fin q → ℕ} {ε : ℝ} {hq : 1 ≤ q}

theorem wexp_mono (hβ : StrictMono β) (hε : 0 < ε) {i j : ℕ} (hij : i ≤ j) :
    wexp m q N h β ε hq i ≤ wexp m q N h β ε hq j := by
  unfold wexp
  by_cases hi : i = 0
  · simp only [hi, ↓reduceIte]
    split_ifs <;> simp
  · have hj : j ≠ 0 := by omega
    simp only [hi, hj, ↓reduceIte]
    refine max_le_max le_rfl (Nat.clog_mono_right _ (Nat.ceil_mono ?_))
    have hb : β ⟨min (i - 1) (q - 1), by omega⟩ ≤ β ⟨min (j - 1) (q - 1), by omega⟩ :=
      hβ.monotone (Fin.mk_le_mk.mpr (by omega))
    have : (2 : ℝ) ^ (β ⟨min (i - 1) (q - 1), by omega⟩ + h) ≤
        (2 : ℝ) ^ (β ⟨min (j - 1) (q - 1), by omega⟩ + h) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr

theorem le_wexp (i : ℕ) : m ≤ wexp m q N h β ε hq i := by
  unfold wexp
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem two_le_mwidth (hm : 1 ≤ m) (i : ℕ) : 2 ≤ mwidth m q N h β ε hq i :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    _ ≤ mwidth m q N h β ε hq i := Nat.pow_le_pow_right (by norm_num) (le_wexp i)

theorem mwidth_dvd (hβ : StrictMono β) (hε : 0 < ε) {i j : ℕ} (hij : i ≤ j) :
    mwidth m q N h β ε hq i ∣ mwidth m q N h β ε hq j :=
  pow_dvd_pow 2 (wexp_mono hβ hε hij)

theorem mwidth_zero : mwidth m q N h β ε hq 0 = 2 ^ m := by simp [mwidth, wexp]

theorem wexp_succ (j : Fin q) : wexp m q N h β ε hq (j.val + 1) =
    max m (Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊) := by
  unfold wexp
  have e : (⟨min (j.val + 1 - 1) (q - 1), by omega⟩ : Fin q) = j := Fin.ext (by simp only; omega)
  simp only [Nat.add_one_ne_zero, ↓reduceIte, e]

/-- The width of level `j + 1` is at least `64 q N 2^(β_j + h)/ε`. -/
theorem lo_le_mwidth (j : Fin q) :
    64 * (q : ℝ) * N * 2 ^ (β j + h) / ε ≤ mwidth m q N h β ε hq (j.val + 1) := by
  unfold mwidth
  rw [wexp_succ]
  calc 64 * (q : ℝ) * N * 2 ^ (β j + h) / ε ≤ ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊ := Nat.le_ceil _
    _ ≤ ((2 ^ Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_pow_clog (by norm_num) _
    _ ≤ ((2 ^ max m (Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊) : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

/-- The width of level `j + 1` is at most `2^m + 2 (64 q N 2^(β_j + h)/ε) + 2`. -/
theorem mwidth_le (hε : 0 < ε) (j : Fin q) :
    (mwidth m q N h β ε hq (j.val + 1) : ℝ) ≤
      2 ^ m + 2 * (64 * (q : ℝ) * N * 2 ^ (β j + h) / ε) + 2 := by
  unfold mwidth
  rw [wexp_succ]
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Nat.ceil_zero, Nat.clog_zero_right,
      zero_le, max_eq_left]
    push_cast
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : 0 < 64 * (q : ℝ) * N * 2 ^ (β j + h) / ε :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hqR) hNR) (by positivity)) hε
  have hn : 1 ≤ ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hlo))
  have h1 : 2 ^ max m (Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊) ≤
      2 ^ m + 2 * ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊ := by
    rcases le_total m (Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊) with hc | hc
    · rw [max_eq_right hc]
      exact (two_pow_clog_le hn).trans (Nat.le_add_left _ _)
    · rw [max_eq_left hc]
      exact Nat.le_add_right _ _
  have h2 : (⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊ : ℝ) < 64 * (q : ℝ) * N * 2 ^ (β j + h) / ε + 1 :=
    Nat.ceil_lt_add_one hlo.le
  have h3 : ((2 ^ max m (Nat.clog 2 ⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊) : ℕ) : ℝ) ≤
      2 ^ m + 2 * (⌈64 * (q : ℝ) * N * 2 ^ (β j + h) / ε⌉₊ : ℝ) := by exact_mod_cast h1
  linarith

end Widths

/-! ### The arithmetic -/

/-- The arithmetic of the parameters, over the reals. -/
theorem costM_arith {K K₀ w Wq T ε N k q h2 Sev SWev SD SL : ℝ}
    (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (hw : 1 ≤ w) (hWq : 0 ≤ Wq) (hT : 0 ≤ T) (hε : 0 < ε) (hN : 0 ≤ N)
    (hq : 0 ≤ q) (hh2 : 0 ≤ h2)
    (hwε : 8 * (4 + 2 * k) ≤ w * ε) (hK₀ε : 8 * (w + 1) ≤ K₀ * ε)
    (hKε : 8 * (q + q * N + 64 * q ^ 2 * N ^ 2 * h2 / ε + q * w * N + N ^ 2 * (2 * h2)) ≤ K * ε)
    (hSev : Sev ≤ q * N * T / 2)
    (hSWev : SWev ≤ q * (w + 2) * N * T / 2 + 64 * q ^ 2 * N ^ 2 * h2 * T / ε)
    (hSD : 2 * SD ≤ N * T) (hSL : N * SL ≤ Wq * ε / 32) :
    K * K₀ * (4 + 2 * k) * (T * (Wq / w)) + Wq * (K * T) + Wq * (K₀ * Sev) + Wq * (K * (w - 1) * T) +
      K₀ * (q * (T * Wq)) + Wq * (K₀ * SWev) + K * K₀ * N * (T * SL) +
      Wq * (K₀ * N * (4 * h2) * SD) ≤ K * Wq * K₀ * (ε * T) := by
  have hw0 : 0 < w := by linarith
  have t1 : K * K₀ * (4 + 2 * k) * (T * (Wq / w)) ≤ K * K₀ * T * Wq * (ε / 8) := by
    have h1 : (4 + 2 * k) / w ≤ ε / 8 := by
      rw [div_le_div_iff₀ hw0 (by norm_num)]
      linarith
    calc K * K₀ * (4 + 2 * k) * (T * (Wq / w)) = K * K₀ * T * Wq * ((4 + 2 * k) / w) := by
          field_simp
      _ ≤ K * K₀ * T * Wq * (ε / 8) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have t2 : Wq * (K * T) + Wq * (K * (w - 1) * T) ≤ Wq * K * T * (K₀ * ε / 8) := by
    have h1 : w ≤ K₀ * ε / 8 := by linarith
    calc Wq * (K * T) + Wq * (K * (w - 1) * T) = Wq * K * T * w := by ring
      _ ≤ Wq * K * T * (K₀ * ε / 8) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have t3 : Sev + q * T + SWev + 4 * N * h2 * SD ≤ T * (K * ε / 8) := by
    have h1 : 4 * N * h2 * SD ≤ 2 * N * h2 * (N * T) := by
      have := mul_le_mul_of_nonneg_left hSD (show 0 ≤ 2 * N * h2 by positivity)
      linarith
    have h2' : 0 ≤ T * q * N * (w - 1) := by
      have := sub_nonneg.mpr hw
      positivity
    have h3 : q + q * N + 64 * q ^ 2 * N ^ 2 * h2 / ε + q * w * N + N ^ 2 * (2 * h2) ≤ K * ε / 8 := by
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hT
    have e : 64 * q ^ 2 * N ^ 2 * h2 * T / ε = T * (64 * q ^ 2 * N ^ 2 * h2 / ε) := by ring
    nlinarith
  have t4 : K * K₀ * N * (T * SL) ≤ K * K₀ * T * (Wq * ε / 32) := by
    calc K * K₀ * N * (T * SL) = K * K₀ * T * (N * SL) := by ring
      _ ≤ K * K₀ * T * (Wq * ε / 32) := mul_le_mul_of_nonneg_left hSL (by positivity)
  have t3' : Wq * K₀ * (Sev + q * T + SWev + 4 * N * h2 * SD) ≤ Wq * K₀ * (T * (K * ε / 8)) :=
    mul_le_mul_of_nonneg_left t3 (by positivity)
  have hpos : 0 ≤ K * Wq * K₀ * (ε * T) := by positivity
  nlinarith

/-- The bound `costB` of `sum_cut_le`, over the reals. -/
theorem costB_le {K K₀ k T Wq W0 q N h Sev SWev SL SD : ℕ} {ε : ℝ} (hε : 0 < ε) (hW0 : 1 ≤ W0)
    (hdvd : W0 ∣ Wq) (hwε : 8 * (4 + 2 * (k : ℝ)) ≤ W0 * ε) (hK₀ε : 8 * ((W0 : ℝ) + 1) ≤ K₀ * ε)
    (hKε : 8 * ((q : ℝ) + q * N + 64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h / ε + q * W0 * N +
      (N : ℝ) ^ 2 * (2 * 2 ^ h)) ≤ K * ε)
    (hSev : (Sev : ℝ) ≤ q * N * T / 2)
    (hSWev : (SWev : ℝ) ≤ q * ((W0 : ℝ) + 2) * N * T / 2 + 64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h * T / ε)
    (hSD : 2 * (SD : ℝ) ≤ N * T) (hSL : (N : ℝ) * SL ≤ Wq * ε / 32) :
    (costB K K₀ k T Wq W0 q N h Sev SWev SL SD : ℝ) ≤ K * Wq * K₀ * (ε * T) := by
  have e0 : ((Wq / W0 : ℕ) : ℝ) = (Wq : ℝ) / W0 := Nat.cast_div_charZero hdvd
  have e1 : ((W0 - 1 : ℕ) : ℝ) = (W0 : ℝ) - 1 := by rw [Nat.cast_sub hW0, Nat.cast_one]
  have hw : (1 : ℝ) ≤ W0 := by exact_mod_cast hW0
  have key := costM_arith (K := K) (K₀ := K₀) (w := W0) (Wq := Wq) (T := T) (ε := ε) (N := N)
    (k := k) (q := q) (h2 := 2 ^ h) (Sev := Sev) (SWev := SWev) (SD := SD) (SL := SL)
    (by positivity) (by positivity) hw (by positivity) (by positivity) hε (by positivity)
    (by positivity) (by positivity) hwε hK₀ε hKε hSev hSWev hSD hSL
  unfold costB
  push_cast [e0, e1]
  refine Eq.trans_le ?_ key
  ring

/-- The events weighted by the widths. -/
theorem sum_swev_le {q : ℕ} {N T ε w : ℝ} (h : ℕ) (ev Wj b : Fin q → ℕ) (hε : 0 < ε) (hN : 0 ≤ N)
    (hw : 0 ≤ w) (hev : ∀ j, 2 * ((2 : ℝ) ^ b j * ev j) ≤ N * T)
    (hW : ∀ j, (Wj j : ℝ) ≤ w + 2 * (64 * q * N * 2 ^ (b j + h) / ε) + 2) :
    ∑ j, ((Wj j - 1 : ℕ) : ℝ) * ev j ≤
      q * (w + 2) * N * T / 2 + 64 * (q : ℝ) ^ 2 * N ^ 2 * 2 ^ h * T / ε := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hj : ∀ j, ((Wj j - 1 : ℕ) : ℝ) * ev j ≤
      (w + 2) * N * T / 2 + 64 * q * N ^ 2 * 2 ^ h * T / ε := by
    intro j
    have hev0 : (0 : ℝ) ≤ ev j := Nat.cast_nonneg _
    have hb1 : (1 : ℝ) ≤ 2 ^ b j := one_le_pow₀ (by norm_num)
    have h1 : ((Wj j - 1 : ℕ) : ℝ) ≤ Wj j := by exact_mod_cast Nat.sub_le _ _
    have h2 : (ev j : ℝ) ≤ 2 ^ b j * ev j := le_mul_of_one_le_left hev0 hb1
    have h3 : 64 * q * N * 2 ^ h / ε * (2 * (2 ^ b j * ev j)) ≤ 64 * q * N * 2 ^ h / ε * (N * T) :=
      mul_le_mul_of_nonneg_left (hev j) (by positivity)
    have h4 : (w + 2) * ev j ≤ (w + 2) * (N * T / 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hev j]) (by linarith)
    calc ((Wj j - 1 : ℕ) : ℝ) * ev j ≤ (w + 2 * (64 * q * N * 2 ^ (b j + h) / ε) + 2) * ev j :=
          mul_le_mul_of_nonneg_right (h1.trans (hW j)) hev0
      _ = (w + 2) * ev j + 64 * q * N * 2 ^ h / ε * (2 * (2 ^ b j * ev j)) := by
          rw [pow_add]
          ring
      _ ≤ (w + 2) * (N * T / 2) + 64 * q * N * 2 ^ h / ε * (N * T) := by linarith
      _ = (w + 2) * N * T / 2 + 64 * q * N ^ 2 * 2 ^ h * T / ε := by ring
  calc ∑ j, ((Wj j - 1 : ℕ) : ℝ) * ev j
      ≤ ∑ _j : Fin q, ((w + 2) * N * T / 2 + 64 * q * N ^ 2 * 2 ^ h * T / ε) :=
        sum_le_sum fun j _ => hj j
    _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The line visits weighted by the overlap bound. -/
theorem sum_sl_le {q : ℕ} {N ε : ℝ} (h Wq : ℕ) (Wj b : Fin q → ℕ) (hε : 0 < ε)
    (hdvd : ∀ j, Wj j ∣ Wq) (hpos : ∀ j, 0 < Wj j)
    (hlo : ∀ j, 64 * (q : ℝ) * N * 2 ^ (b j + h) / ε ≤ Wj j) :
    N * ∑ j, ((Wq / Wj j : ℕ) : ℝ) * 2 ^ (b j + h + 1) ≤ Wq * ε / 32 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp only [univ_eq_empty, sum_empty, mul_zero]
    positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hj : ∀ j, N * (((Wq / Wj j : ℕ) : ℝ) * 2 ^ (b j + h + 1)) ≤ Wq * ε / (32 * q) := by
    intro j
    have hW : (0 : ℝ) < Wj j := by exact_mod_cast hpos j
    have e0 : ((Wq / Wj j : ℕ) : ℝ) = Wq / Wj j := Nat.cast_div_charZero (hdvd j)
    have h1 : N * 2 ^ (b j + h) ≤ Wj j * ε / (64 * q) := by
      have := hlo j
      rw [div_le_iff₀ hε] at this
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [e0, pow_succ]
    calc N * ((Wq : ℝ) / Wj j * (2 ^ (b j + h) * 2)) = 2 * (Wq / Wj j) * (N * 2 ^ (b j + h)) := by ring
      _ ≤ 2 * (Wq / Wj j) * (Wj j * ε / (64 * q)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Wq * ε / (32 * q) := by
          field_simp
          ring
  rw [mul_sum]
  calc ∑ j, N * (((Wq / Wj j : ℕ) : ℝ) * 2 ^ (b j + h + 1)) ≤ ∑ _j : Fin q, Wq * ε / (32 * q) :=
        sum_le_sum fun j _ => hj j
    _ = Wq * ε / 32 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-! ### The hops of the bounded walks -/

section Pairs

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} {H' : Finset (Fin k × ℕ × ℕ)} {own : Fin k × ℕ × ℕ → ℕ}

/-- The hop pairs of the family data are those of `H'`. -/
theorem famData_pairs {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (famData xs H' own ℓ hℓ).H.image (fun x => x.2) = hopPairs H' := by
  ext e
  simp only [mem_image, hopPairs]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨η, hη, h1, h2⟩ := mem_famData_H.mp hx
    exact ⟨η, (mem_fam.mp hη).1, by rw [h1, h2]⟩
  · rintro ⟨η, hη, rfl⟩
    exact ⟨(⟨key xs own η, mem_image_of_mem _ hη⟩, η.2.1, η.2.2),
      mem_famData_H.mpr ⟨η, mem_filter.mpr ⟨hη, rfl⟩, rfl, rfl⟩, rfl⟩

/-- At every time at most `2k` hop pairs of `H'` start or end: one start and one end per head. -/
theorem card_hopPairs_at_le {T : ℕ} (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2) (t : ℕ) :
    ((hopPairs H').filter fun e => e.1 = t ∨ e.2 = t).card ≤ 2 * k := by
  have key : ∀ S ⊆ H', (∀ η ∈ S, ∀ η' ∈ S, η.1 = η'.1 → η = η') →
      (S.image fun η => (η.2.1, η.2.2)).card ≤ k := by
    intro S _ hinj
    calc (S.image fun η => (η.2.1, η.2.2)).card ≤ S.card := card_image_le
      _ = (S.image fun η => η.1).card :=
          (card_image_of_injOn fun η hη η' hη' he => hinj η hη η' hη' he).symm
      _ ≤ k := (card_le_univ _).trans (by simp)
  have hs : ((hopPairs H').filter fun e => e.1 = t) ⊆
      (H'.filter fun η => η.2.1 = t).image fun η => (η.2.1, η.2.2) := by
    intro e he
    obtain ⟨he1, he2⟩ := mem_filter.mp he
    obtain ⟨η, hη, rfl⟩ := mem_image.mp he1
    exact mem_image.mpr ⟨η, mem_filter.mpr ⟨hη, he2⟩, rfl⟩
  have hs' : ((hopPairs H').filter fun e => e.2 = t) ⊆
      (H'.filter fun η => η.2.2 = t).image fun η => (η.2.1, η.2.2) := by
    intro e he
    obtain ⟨he1, he2⟩ := mem_filter.mp he
    obtain ⟨η, hη, rfl⟩ := mem_image.mp he1
    exact mem_image.mpr ⟨η, mem_filter.mpr ⟨hη, he2⟩, rfl⟩
  have h1 := key (H'.filter fun η => η.2.1 = t) (filter_subset _ _) fun η hη η' hη' he => by
    obtain ⟨hη1, hη2⟩ := mem_filter.mp hη
    obtain ⟨hη1', hη2'⟩ := mem_filter.mp hη'
    have hh := hH η hη1
    have hh' := hH η' hη1'
    rw [he, hη2] at hh
    rw [hη2'] at hh'
    exact Prod.ext he (Prod.ext (hη2.trans hη2'.symm) (hop_start_unique hh hh'))
  have h2 := key (H'.filter fun η => η.2.2 = t) (filter_subset _ _) fun η hη η' hη' he => by
    obtain ⟨hη1, hη2⟩ := mem_filter.mp hη
    obtain ⟨hη1', hη2'⟩ := mem_filter.mp hη'
    have hh := hH η hη1
    have hh' := hH η' hη1'
    rw [he, hη2] at hh
    rw [hη2'] at hh'
    exact Prod.ext he (Prod.ext (hop_end_unique hh hh') (hη2.trans hη2'.symm))
  rw [filter_or]
  have := card_union_le ((hopPairs H').filter fun e => e.1 = t) ((hopPairs H').filter fun e => e.2 = t)
  have := card_le_card hs
  have := card_le_card hs'
  omega

end Pairs

/-! ### Theorem M -/

/-- **Theorem M** (for any owners strictly inside the hops). -/
theorem theoremM {k ℓ T q h : ℕ} (hℓ : 1 ≤ ℓ) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x0 : ℕ → ℤ) (hx0 : IsWalk x0) (xs : Fin k → ℕ → ℤ) (hx : ∀ i, IsWalk (xs i))
    (H' : Finset (Fin k × ℕ × ℕ)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (own : Fin k × ℕ × ℕ → ℕ) (hown : ∀ η ∈ H', η.2.1 < own η ∧ own η < η.2.2)
    (hload : OwnerLoadLE xs H' own ℓ) (β : Fin q → ℕ) (hβ : StrictMono β)
    (hwin : ∀ F : Keys xs H' own, ∃ j : Fin q,
      β j ≤ lam (famd xs H' own F) ∧ lam (famd xs H' own F) ≤ β j + h) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hops x0 T ∪ hopPairs H' ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card <
          DM k ℓ q h ε := by
  classical
  -- the parameters
  set N := 2 * k * ℓ with hN
  set m := mExp k ε with hm_def
  set K₀ := mK0 k ε with hK₀_def
  set K := mK k ℓ q h ε with hK_def
  have hm : 1 ≤ m := one_le_mExp hε hε1
  have hK₀ : 0 < K₀ := mK0_pos hε
  have hK : 0 < K := mK_pos hε hq
  set W := mwidth m q N h β ε hq with hW_def
  have hW2 : ∀ i, 2 ≤ W i := two_le_mwidth hm
  have hdiv : ∀ i j, i ≤ j → W i ∣ W j := fun i j hij => mwidth_dvd hβ hε hij
  have hW0 : (W 0 : ℝ) = mw k ε := by
    rw [hW_def, mwidth_zero]
    unfold mw
    push_cast
    rfl
  -- the families
  set A := famData xs H' own ℓ (by omega) with hA_def
  have hA : A.Valid T := famData_valid hx hH hown (by omega) hload
  choose win hwin1 hwin2 using hwin
  have hdegA : ∀ t, ((A.H.image fun η => η.2).filter fun e => e.1 = t ∨ e.2 = t).card ≤ 2 * k := by
    intro t
    rw [hA_def, famData_pairs]
    exact card_hopPairs_at_le hH t
  have hsum := sum_cut_le (A := A) (β := β) (W := W) (T := T) hx0 hW2 hdiv hq hK₀ hK hA hβ win
    hwin1 hwin2 hdegA
  -- the events and the heights
  have hSD : 2 * ∑ F, A.d F ≤ N * T := hA.sum_d_all
  have hev : ∀ j : Fin q, 2 * (2 ^ β j * (univ.filter fun F => β j ≤ lam (A.d F)).card) ≤ N * T := by
    intro j
    refine le_trans (Nat.mul_le_mul_left 2 ?_) hSD
    calc 2 ^ β j * (univ.filter fun F => β j ≤ lam (A.d F)).card
        = ∑ F ∈ univ.filter (fun F => β j ≤ lam (A.d F)), 2 ^ β j := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ F ∈ univ.filter (fun F => β j ≤ lam (A.d F)), A.d F := by
          refine sum_le_sum fun F hF => ?_
          calc 2 ^ β j ≤ 2 ^ lam (A.d F) := Nat.pow_le_pow_right (by norm_num) (mem_filter.mp hF).2
            _ ≤ A.d F := Nat.pow_log_le_self 2 (by have := hA.d_pos F; omega)
      _ ≤ ∑ F, A.d F := sum_le_sum_of_subset (filter_subset _ _)
  -- the real bounds
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hTR : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hwε : 8 * (4 + 2 * (k : ℝ)) ≤ (W 0 : ℝ) * ε := by
    rw [hW0]
    have := le_mw (k := k) hε
    rwa [div_le_iff₀ hε] at this
  have hK₀ε : 8 * ((W 0 : ℝ) + 1) ≤ K₀ * ε := by
    rw [hW0]
    have : 8 * ((mw k ε : ℝ) + 1) / ε ≤ K₀ := Nat.le_ceil _
    rwa [div_le_iff₀ hε] at this
  have hKε : 8 * ((q : ℝ) + q * N + 64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h / ε + q * (W 0 : ℝ) * N +
      (N : ℝ) ^ 2 * (2 * 2 ^ h)) ≤ K * ε := by
    rw [hW0]
    have : 8 / ε * ((q : ℝ) + q * (N : ℝ) + 64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h / ε +
        q * (mw k ε : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 * 2 ^ (h + 1)) ≤ K := Nat.le_ceil _
    rw [pow_succ] at this
    have e : 8 / ε * ((q : ℝ) + q * (N : ℝ) + 64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h / ε +
        q * (mw k ε : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 * (2 ^ h * 2)) * ε = 8 * ((q : ℝ) + q * N +
          64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h / ε + q * (mw k ε : ℝ) * N + (N : ℝ) ^ 2 * (2 * 2 ^ h)) := by
      field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_right this hε.le
  have hevR : ∀ j : Fin q, 2 * ((2 : ℝ) ^ β j * ((univ.filter fun F => β j ≤ lam (A.d F)).card : ℕ)) ≤
      N * T := fun j => by exact_mod_cast hev j
  have hSev : ((∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card : ℕ) : ℝ) ≤ q * N * T / 2 := by
    have h1 : 2 * ∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card ≤ q * (N * T) := by
      rw [mul_sum]
      calc ∑ j : Fin q, 2 * (univ.filter fun F => β j ≤ lam (A.d F)).card ≤ ∑ _j : Fin q, N * T := by
            refine sum_le_sum fun j _ => le_trans (Nat.mul_le_mul_left 2 ?_) (hev j)
            exact Nat.le_mul_of_pos_left _ (by positivity)
        _ = q * (N * T) := by simp
    have h2 : (2 : ℝ) * ((∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card : ℕ) : ℝ) ≤
        q * (N * T) := by exact_mod_cast h1
    linarith
  have hWj : ∀ j : Fin q, (W (j.val + 1) : ℝ) ≤
      (W 0 : ℝ) + 2 * (64 * q * N * 2 ^ (β j + h) / ε) + 2 := by
    intro j
    have := mwidth_le (m := m) (N := N) (h := h) (β := β) (hq := hq) hε j
    have e : (W 0 : ℝ) = (2 : ℝ) ^ m := by
      rw [hW_def, mwidth_zero]
      push_cast
      rfl
    rw [e]
    exact this
  have hSWev : ((∑ j : Fin q, (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card : ℕ) : ℝ) ≤
      q * ((W 0 : ℝ) + 2) * N * T / 2 + 64 * (q : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 ^ h * T / ε := by
    push_cast
    exact sum_swev_le h (fun j => (univ.filter fun F => β j ≤ lam (A.d F)).card) (fun j => W (j.val + 1)) β
      hε hNR (Nat.cast_nonneg _) hevR hWj
  have hSDR : 2 * ((∑ F, A.d F : ℕ) : ℝ) ≤ N * T := by exact_mod_cast hSD
  have hSL : (N : ℝ) * ((∑ j : Fin q, W q / W (j.val + 1) * 2 ^ (β j + h + 1) : ℕ) : ℝ) ≤
      W q * ε / 32 := by
    push_cast
    exact sum_sl_le h (W q) (fun j => W (j.val + 1)) β hε (fun j => hdiv _ _ (by omega))
      (fun j => by have := hW2 (j.val + 1); omega) (fun j => lo_le_mwidth (hq := hq) j)
  have hB := costB_le hε (by have := hW2 0; omega) (hdiv 0 q (Nat.zero_le _)) hwε hK₀ε hKε hSev
    hSWev hSDR hSL
  -- the average
  have hS : ((∑ ρ ∈ range (W q), ∑ ω ∈ offsets K₀ K q,
      ((cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card) : ℕ) : ℝ) ≤
      (W q : ℝ) * (K₀ * (K ^ q * K ^ q)) * (ε * T) := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have h1 := Nat.cast_le (α := ℝ) |>.mpr hsum
    push_cast at h1
    refine le_of_mul_le_mul_left ?_ hKR
    calc (K : ℝ) * ((∑ ρ ∈ range (W q), ∑ ω ∈ offsets K₀ K q,
          ((cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card) : ℕ) : ℝ)
        ≤ (K : ℝ) ^ q * K ^ q * (costB K K₀ k T (W q) (W 0) q N h
          (∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card)
          (∑ j : Fin q, (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card)
          (∑ j : Fin q, W q / W (j.val + 1) * 2 ^ (β j + h + 1)) (∑ F, A.d F) : ℝ) := by
          push_cast
          exact h1
      _ ≤ (K : ℝ) ^ q * K ^ q * (K * W q * K₀ * (ε * T)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = K * ((W q : ℝ) * (K₀ * (K ^ q * K ^ q)) * (ε * T)) := by ring
  have hne : (range (W q) ×ˢ offsets K₀ K q).Nonempty := by
    refine ⟨(0, 0, fun _ => 0, fun _ => 0), mem_product.mpr ⟨mem_range.mpr (by have := hW2 q; omega), ?_⟩⟩
    simp only [offsets, mem_product, mem_range, Fintype.mem_piFinset]
    exact ⟨hK₀, fun _ => hK, fun _ => hK⟩
  obtain ⟨⟨ρ, ω⟩, -, hcut⟩ := exists_le_of_sum_le hne
    (f := fun x => (((cutSM x0 W x.1 A T β K₀ K x.2).card + (cutHM x0 W x.1 A T β K₀ K x.2).card : ℕ) : ℝ))
    (g := fun _ => ε * T) (by
      rw [sum_product, sum_const, card_product, card_range, card_offsets, nsmul_eq_mul]
      push_cast at hS ⊢
      linarith)
  -- the cut
  have hE : Eall x0 A T = hops x0 T ∪ hopPairs H' := by
    unfold Eall
    rw [hA_def, famData_pairs]
  have hElong : ∀ e ∈ hops x0 T ∪ hopPairs H', e.1 + 2 ≤ e.2 := by
    intro e he
    rcases mem_union.mp he with hc | ha
    · exact (mem_hops.mp hc).1
    · obtain ⟨η, hη, rfl⟩ := mem_image.mp ha
      exact (hH η hη).1
  refine ⟨cutSM x0 W ρ A T β K₀ K ω, cutHM x0 W ρ A T β K₀ K ω, filter_subset _ _, ?_, hcut, ?_⟩
  · rw [← hE]
    exact filter_subset _ _
  · intro f n hpath
    have hdl := depth_le_of_mixedRadix (mradix K₀ K) (fun t => mdig x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t)
      (fun t p => mdig_lt x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 hK₀ hK t p) f n
      (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H') (fun i hi => ?_) (fun i hi hm => ?_)
    · rw [prod_mradix] at hdl
      have hpos : 0 < K₀ * K ^ (2 * q) := Nat.mul_pos hK₀ (pow_pos hK _)
      calc ((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card
          ≤ K₀ * K ^ (2 * q) - 1 := hdl
        _ < K₀ * K ^ (2 * q) := Nat.sub_lt hpos one_pos
        _ = DM k ℓ q h ε := rfl
    · rcases hpath i hi with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · have hnot : ¬ (f i ∈ Zt x0 W ρ T ∨ f i - 1 ∈ Zt x0 W ρ T ∨
            mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (f i) < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (f i - 1)) :=
          fun hc => h4 (mem_filter.mpr ⟨mem_Ico.mpr ⟨h2, h3⟩, hc⟩)
        rw [show f (i + 1) = f i - 1 by omega]
        exact not_lt.mp fun hc => hnot (Or.inr (Or.inr hc))
      · have hnot : ¬ ((f (i + 1), f i).1 ∈ Zt x0 W ρ T ∨ (f (i + 1), f i).2 ∈ Zt x0 W ρ T ∨
            mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (f (i + 1), f i).2 ≤
              mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (f (i + 1), f i).1) :=
          fun hc => h2 (mem_filter.mpr ⟨by rw [hE]; exact h1, hc⟩)
        exact (not_le.mp fun hc => hnot (Or.inr (Or.inr hc))).le
    · rcases hpath i hi with ⟨h1, -, -, -⟩ | ⟨h1, h2⟩
      · have := hElong _ hm
        simp only at this
        omega
      · have hnot : ¬ ((f (i + 1), f i).1 ∈ Zt x0 W ρ T ∨ (f (i + 1), f i).2 ∈ Zt x0 W ρ T ∨
            mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (f (i + 1), f i).2 ≤
              mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (f (i + 1), f i).1) :=
          fun hc => h2 (mem_filter.mpr ⟨by rw [hE]; exact h1, hc⟩)
        exact not_le.mp fun hc => hnot (Or.inr (Or.inr hc))

/-- **Theorem M**, for the owners of the paper. -/
theorem theoremM_owner {k ℓ T q h : ℕ} (hℓ : 1 ≤ ℓ) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x0 : ℕ → ℤ) (hx0 : IsWalk x0) (xs : Fin k → ℕ → ℤ) (hx : ∀ i, IsWalk (xs i))
    (H' : Finset (Fin k × ℕ × ℕ)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (hload : OwnerLoadLE xs H' (fun η => hopOwner (xs η.1) η.2.1 η.2.2) ℓ) (β : Fin q → ℕ)
    (hβ : StrictMono β)
    (hwin : ∀ F : Keys xs H' (fun η => hopOwner (xs η.1) η.2.1 η.2.2), ∃ j : Fin q,
      β j ≤ lam (famd xs H' (fun η => hopOwner (xs η.1) η.2.1 η.2.2) F) ∧
        lam (famd xs H' (fun η => hopOwner (xs η.1) η.2.1 η.2.2) F) ≤ β j + h) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hops x0 T ∪ hopPairs H' ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card <
          DM k ℓ q h ε :=
  theoremM hℓ hq hε hε1 x0 hx0 xs hx H' hH _
    (fun η hη => ⟨(hopOwner_spec _ (hH η hη).1).1, (hopOwner_spec _ (hH η hη).1).2.1⟩) hload β hβ hwin

end BoundedNesting
