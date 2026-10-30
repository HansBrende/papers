import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

set_option autoImplicit false

/-!
# Covering lemmas: van der Corput rows and dyadic offsets

Self-contained number theory over `ℚ` for the gap-area memo. `W = 2^m` throughout.

* `vdC` is the base-2 bit reversal. Any `W` consecutive indices hit every dyadic interval
  `[a/W, (a+1)/W)` (`vdC_dyadic`), hence every `[u, u + 2/W] ⊆ [0,1]` (`vdC_hits`).
* With `ℓ = ⌊log₂ k⌋`, `w k = 2^{-(2ℓ+2)}` and `t k = (2^{ℓ+1} - k)·2^{-(2ℓ+1)} + 2^{-(ℓ+1)}`,
  the offsets `t k - θ w k`, `t k - (2-θ) w k` (`1 ≤ k ≤ D`) are `8 r²`-dense above every
  `r ∈ [t D, 1/2]` (`offsets_dense`, `κ = 8`).
* Points `vdC k ± c·o` meet every `[v, v + δ] ⊆ [0,1]` with `δ ≥ κ (a+2)²/(cW²)` when
  `r₀ ≤ a/(cW)`, `2(a+2) ≤ cW`, `δ + 2(a+2)/W ≤ 1` (`row_cover`; at `c = 1/4`, `m ≥ 7`:
  `row_cover_quarter`, `δ = 64κ/(cW²)`).
* Combined (`rowPoints_dense`): for `m ≥ 6`, `θ ∈ [0,1]`, `t D ≤ 16/W` (e.g. `W ≤ 16 D`), the
  points `vdC k ± o/4` meet every `[x, y] ⊆ [0,1]` with `y - x ≥ 1152/W²`.
-/

namespace SourceCovers.Covering

/-! ## The base-2 van der Corput sequence -/

/-- The base-2 van der Corput sequence (bit reversal): `vdC (2j + b) = (b + vdC j)/2`. -/
def vdC : ℕ → ℚ
  | 0 => 0
  | n + 1 => (((n + 1) % 2 : ℕ) + vdC ((n + 1) / 2)) / 2
decreasing_by omega

theorem vdC_zero : vdC 0 = 0 := by rw [vdC]

/-- The defining recursion, valid for every `n` (including `0`). -/
theorem vdC_eq (n : ℕ) : vdC n = ((n % 2 : ℕ) + vdC (n / 2)) / 2 := by
  cases n with
  | zero => simp [vdC_zero]
  | succ n => rw [vdC]

/-- The lowest bit of the index becomes the leading binary digit. -/
theorem vdC_two_mul_add (j b : ℕ) (hb : b < 2) : vdC (2 * j + b) = (b + vdC j) / 2 := by
  have h1 : (2 * j + b) % 2 = b := by omega
  have h2 : (2 * j + b) / 2 = j := by omega
  rw [vdC_eq, h1, h2]

/-- `0 ≤ vdC n < 1`. -/
theorem vdC_mem (n : ℕ) : 0 ≤ vdC n ∧ vdC n < 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vdC_zero]
    · obtain ⟨h0, h1⟩ := ih (n / 2) (by omega)
      rw [vdC_eq]
      have hb : ((n % 2 : ℕ) : ℚ) ≤ 1 := by exact_mod_cast (by omega : n % 2 ≤ 1)
      have hb0 : (0 : ℚ) ≤ ((n % 2 : ℕ) : ℚ) := Nat.cast_nonneg _
      constructor <;> linarith

theorem vdC_nonneg (n : ℕ) : 0 ≤ vdC n := (vdC_mem n).1

theorem vdC_lt_one (n : ℕ) : vdC n < 1 := (vdC_mem n).2

/-- Sanity check: `6 = 110₂` reverses to `0.011₂ = 3/8`. -/
example : vdC 6 = 3 / 8 := by
  rw [show (6 : ℕ) = 2 * 3 + 0 by rfl, vdC_two_mul_add _ _ (by norm_num),
    show (3 : ℕ) = 2 * 1 + 1 by rfl, vdC_two_mul_add _ _ (by norm_num),
    show (1 : ℕ) = 2 * 0 + 1 by rfl, vdC_two_mul_add _ _ (by norm_num), vdC_zero]
  norm_num

/-- (vdC-dyadic) Any `2^m` consecutive indices `[k₀, k₀ + 2^m)` contain a `k` with
`vdC k` in the dyadic interval `[a/2^m, (a+1)/2^m)`, for every `a < 2^m`. -/
theorem vdC_dyadic (m : ℕ) : ∀ (k₀ a : ℕ), a < 2 ^ m →
    ∃ k, k₀ ≤ k ∧ k < k₀ + 2 ^ m ∧ (a : ℚ) / 2 ^ m ≤ vdC k ∧ vdC k < (a + 1) / 2 ^ m := by
  induction m with
  | zero =>
    intro k₀ a ha
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨k₀, le_rfl, by simp, by simpa using vdC_nonneg k₀, by simpa using vdC_lt_one k₀⟩
  | succ m ih =>
    intro k₀ a ha
    have hP : 0 < 2 ^ m := by positivity
    have hb : a / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul hP]; rw [pow_succ] at ha; linarith
    have ha' : a % 2 ^ m < 2 ^ m := Nat.mod_lt _ hP
    have hdecomp : 2 ^ m * (a / 2 ^ m) + a % 2 ^ m = a := Nat.div_add_mod a (2 ^ m)
    -- the leading digit of `vdC k` is the parity of `k`; recurse on `k / 2`
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih ((k₀ + 1 - a / 2 ^ m) / 2) (a % 2 ^ m) ha'
    have hPq : (0 : ℚ) < 2 ^ m := by positivity
    have hcast : (a : ℚ) = 2 ^ m * ((a / 2 ^ m : ℕ) : ℚ) + ((a % 2 ^ m : ℕ) : ℚ) := by
      exact_mod_cast hdecomp.symm
    refine ⟨2 * j + a / 2 ^ m, by omega, ?_, ?_, ?_⟩
    · rw [pow_succ]; omega
    · rw [vdC_two_mul_add j _ hb]
      rw [div_le_iff₀ hPq] at hj3
      rw [div_le_iff₀ (by positivity), hcast, pow_succ]
      nlinarith
    · rw [vdC_two_mul_add j _ hb]
      rw [lt_div_iff₀ hPq] at hj4
      rw [lt_div_iff₀ (by positivity), hcast, pow_succ]
      nlinarith

/-- Every interval `[u, u + 2/2^m] ⊆ [0,1]` contains `vdC k` for some `k ∈ [k₀, k₀ + 2^m)`. -/
theorem vdC_hits (m k₀ : ℕ) {u : ℚ} (hu : 0 ≤ u) (hu1 : u + 2 / 2 ^ m ≤ 1) :
    ∃ k, k₀ ≤ k ∧ k < k₀ + 2 ^ m ∧ u ≤ vdC k ∧ vdC k ≤ u + 2 / 2 ^ m := by
  have hP : (0 : ℚ) < 2 ^ m := by positivity
  have h0 : 0 ≤ u * 2 ^ m := by positivity
  have h1 : u * 2 ^ m ≤ (⌈u * 2 ^ m⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : (⌈u * 2 ^ m⌉₊ : ℚ) < u * 2 ^ m + 1 := Nat.ceil_lt_add_one h0
  have h3 : u * 2 ^ m + 2 ≤ 2 ^ m := by
    have := mul_le_mul_of_nonneg_right hu1 hP.le
    rwa [add_mul, div_mul_cancel₀ _ hP.ne', one_mul] at this
  have ha : ⌈u * 2 ^ m⌉₊ < 2 ^ m := by
    have : (⌈u * 2 ^ m⌉₊ : ℚ) < (2 : ℚ) ^ m := by linarith
    exact_mod_cast this
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := vdC_dyadic m k₀ _ ha
  refine ⟨k, hk1, hk2, ?_, ?_⟩
  · rw [div_le_iff₀ hP] at hk3
    rw [← mul_le_mul_iff_of_pos_right hP]
    linarith
  · rw [lt_div_iff₀ hP] at hk4
    rw [← mul_le_mul_iff_of_pos_right hP, add_mul, div_mul_cancel₀ _ hP.ne']
    linarith

/-! ## Dyadic offsets -/

/-- The weight `w k = 2^{-(2ℓ+2)}`, `ℓ = ⌊log₂ k⌋`. -/
def w (k : ℕ) : ℚ := 1 / 2 ^ (2 * Nat.log 2 k + 2)

/-- The tail `t k = (2^{ℓ+1} - k)·2^{-(2ℓ+1)} + 2^{-(ℓ+1)}`, `ℓ = ⌊log₂ k⌋`
(informally `t k = 2 ∑_{i ≥ k} w i`). -/
def t (k : ℕ) : ℚ :=
  (2 ^ (Nat.log 2 k + 1) - k) / 2 ^ (2 * Nat.log 2 k + 1) + 1 / 2 ^ (Nat.log 2 k + 1)

theorem w_pos (k : ℕ) : 0 < w k := by unfold w; positivity

/-- `t 1 = 1`. -/
theorem t_one : t 1 = 1 := by norm_num [t]

/-- `t (2^ℓ) = 2^{-ℓ}`. -/
theorem t_two_pow (ℓ : ℕ) : t (2 ^ ℓ) = 1 / 2 ^ ℓ := by
  have hl : Nat.log 2 (2 ^ ℓ) = ℓ := Nat.log_pow (by norm_num) ℓ
  rw [t, hl]; push_cast
  field_simp; ring

/-- `t k - t (k+1) = 2 w k` for `k ≥ 1`. -/
theorem t_sub_succ {k : ℕ} (hk : 1 ≤ k) : t k - t (k + 1) = 2 * w k := by
  set ℓ := Nat.log 2 k with hℓ
  have h1 : 2 ^ ℓ ≤ k := Nat.pow_log_le_self 2 (by omega)
  have h2 : k < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  rcases Nat.lt_or_ge (k + 1) (2 ^ (ℓ + 1)) with h3 | h3
  · -- `k + 1` stays in the block `[2^ℓ, 2^{ℓ+1})`
    have hl : Nat.log 2 (k + 1) = ℓ := Nat.log_eq_of_pow_le_of_lt_pow (by omega) h3
    simp only [t, w, hl, ← hℓ]
    push_cast
    rw [pow_succ (2 : ℚ) (2 * ℓ + 1)]
    field_simp
    ring
  · -- `k + 1 = 2^{ℓ+1}` starts the next block
    have h4 : k + 1 = 2 ^ (ℓ + 1) := by omega
    have hl : Nat.log 2 (k + 1) = ℓ + 1 := by rw [h4, Nat.log_pow (by norm_num)]
    have hk' : (k : ℚ) = 2 ^ (ℓ + 1) - 1 := by
      have : ((k + 1 : ℕ) : ℚ) = ((2 ^ (ℓ + 1) : ℕ) : ℚ) := by rw [h4]
      push_cast at this; linarith
    simp only [t, w, hl, ← hℓ]
    push_cast
    rw [hk']
    field_simp
    ring

/-- `t` is antitone on `k ≥ 1`. -/
theorem t_anti {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : t j ≤ t i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := t_sub_succ (le_trans hi hij)
    have := w_pos j
    linarith

/-- `t (k+1) ≥ 2^{-(ℓ+1)}` for `k ≥ 1`, `ℓ = ⌊log₂ k⌋`. -/
theorem inv_pow_le_t_succ {k : ℕ} (hk : 1 ≤ k) : 1 / 2 ^ (Nat.log 2 k + 1) ≤ t (k + 1) := by
  have h2 : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  rw [← t_two_pow]
  exact t_anti (by omega) (by omega)

theorem t_pos {k : ℕ} (hk : 1 ≤ k) : 0 < t k := by
  have h := inv_pow_le_t_succ hk
  have : (0 : ℚ) < 1 / 2 ^ (Nat.log 2 k + 1) := by positivity
  have := t_sub_succ hk
  have := w_pos k
  linarith

theorem t_le_one {k : ℕ} (hk : 1 ≤ k) : t k ≤ 1 := t_one ▸ t_anti le_rfl hk

/-- `t D ≤ 16 / 2^m` as soon as `2^m ≤ 16 D`. -/
theorem t_le_of_pow_le {m D : ℕ} (h : 2 ^ m ≤ 16 * D) : t D ≤ 16 / 2 ^ m := by
  have hD : 1 ≤ D := by have := Nat.one_le_two_pow (n := m); omega
  set ℓ := Nat.log 2 D
  have h1 : 2 ^ ℓ ≤ D := Nat.pow_log_le_self 2 (by omega)
  have h2 : D < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have hm : m ≤ ℓ + 4 := by
    have : 2 ^ m < 2 ^ (ℓ + 5) := by rw [pow_add 2 ℓ 5, pow_succ] at *; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  have hmq : (2 : ℚ) ^ m ≤ 16 * 2 ^ ℓ := by
    calc (2 : ℚ) ^ m ≤ 2 ^ (ℓ + 4) := pow_le_pow_right₀ (by norm_num) hm
      _ = 16 * 2 ^ ℓ := by ring
  calc t D ≤ t (2 ^ ℓ) := t_anti (Nat.one_le_two_pow) h1
    _ = 1 / 2 ^ ℓ := t_two_pow ℓ
    _ = 16 / (16 * 2 ^ ℓ) := by field_simp
    _ ≤ 16 / 2 ^ m := div_le_div_of_nonneg_left (by norm_num) (by positivity) hmq

/-- `w k ≤ r²` whenever `t (k+1) ≤ r`. -/
theorem w_le_sq {k : ℕ} {r : ℚ} (hk : 1 ≤ k) (hr : t (k + 1) ≤ r) : w k ≤ r ^ 2 := by
  have h := inv_pow_le_t_succ hk
  have hw : w k = (1 / 2 ^ (Nat.log 2 k + 1)) ^ 2 := by
    unfold w; rw [div_pow, one_pow, ← pow_mul]; ring_nf
  rw [hw]
  exact pow_le_pow_left₀ (by positivity) (h.trans hr) 2

/-- `w (k-1) ≤ 4 w k` for `k ≥ 2`. -/
theorem w_pred_le {k : ℕ} (hk : 2 ≤ k) : w (k - 1) ≤ 4 * w k := by
  have hl : Nat.log 2 k ≤ Nat.log 2 (k - 1) + 1 := by
    calc Nat.log 2 k ≤ Nat.log 2 ((k - 1) * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 (k - 1) + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have h4 : (4 : ℚ) * w k = 1 / 2 ^ (2 * Nat.log 2 k) := by
    unfold w; rw [pow_add]; field_simp; norm_num
  rw [h4]
  unfold w
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- The offsets `O D θ = {t k - θ w k, t k - (2-θ) w k : 1 ≤ k ≤ D}`. -/
def offsets (D : ℕ) (θ : ℚ) : Finset ℚ :=
  (Finset.Icc 1 D).image (fun k => t k - θ * w k) ∪
    (Finset.Icc 1 D).image (fun k => t k - (2 - θ) * w k)

/-- (offsets-dense, `κ = 8`) For `θ ∈ [0,1]` and `t D ≤ r ≤ 1/2` some offset lies in
`[r, r + 8 r²]`. -/
theorem offsets_dense {D : ℕ} {θ r : ℚ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : t D ≤ r)
    (hr : r ≤ 1 / 2) : ∃ o ∈ offsets D θ, r ≤ o ∧ o ≤ r + 8 * r ^ 2 := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    norm_num [t] at hD
    linarith
  -- `k` is the first index with `t (k+1) ≤ r`, so `t (k+1) ≤ r < t k`
  have hex : ∃ j, t (j + 1) ≤ r := ⟨D - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
  set k := Nat.find hex
  have hk : t (k + 1) ≤ r := Nat.find_spec hex
  have hkD : k + 1 ≤ D := by
    have := Nat.find_min' hex (show t (D - 1 + 1) ≤ r by rwa [Nat.sub_add_cancel (by omega)])
    omega
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [h0, zero_add, t_one] at hk
    linarith
  have htk : r < t k := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    rw [Nat.sub_add_cancel hk1] at this
    exact lt_of_not_ge this
  have hstep := t_sub_succ hk1
  have hwk := w_le_sq hk1 hk
  have hwpos := w_pos k
  by_cases hcase : r ≤ t k - θ * w k
  · -- the upper offset of block `k` is above `r`
    refine ⟨t k - θ * w k, ?_, hcase, ?_⟩
    · simp only [offsets, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
      exact Or.inl ⟨k, ⟨hk1, by omega⟩, rfl⟩
    · have : 0 ≤ θ * w k := mul_nonneg hθ0 hwpos.le
      nlinarith
  · -- otherwise use the lower offset `t k + θ w (k-1)` of block `k - 1`
    rw [not_le] at hcase
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1 : k = 1 := by omega
      rw [h1, t_one] at hcase
      have : w 1 = 1 / 4 := by norm_num [w]
      rw [this] at hcase
      linarith
    have hstep' := t_sub_succ (k := k - 1) (by omega)
    rw [Nat.sub_add_cancel hk1] at hstep'
    have hwp := w_pred_le hk2
    have hwp0 := w_pos (k - 1)
    refine ⟨t (k - 1) - (2 - θ) * w (k - 1), ?_, ?_, ?_⟩
    · simp only [offsets, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
      exact Or.inr ⟨k - 1, ⟨by omega, by omega⟩, rfl⟩
    · have : 0 ≤ θ * w (k - 1) := mul_nonneg hθ0 hwp0.le
      nlinarith
    · have h1 : θ * w (k - 1) ≤ w (k - 1) := by nlinarith
      have h2 : θ * w k ≤ w k := by nlinarith
      nlinarith

/-! ## Row covering -/

/-- The row points `vdC k ± c·o` with `k₀ ≤ k < k₀ + 2^m` and `o ∈ O`. -/
def rowSet (c : ℚ) (O : Set ℚ) (k₀ m : ℕ) : Set ℚ :=
  {p | ∃ k, k₀ ≤ k ∧ k < k₀ + 2 ^ m ∧ ∃ o ∈ O, p = vdC k - c * o ∨ p = vdC k + c * o}

/-- (Row covering, general form) Let `W = 2^m`. If `O` is `κ r²`-dense above every
`r ∈ [r₀, 1/2]`, `r₀ ≤ a/(cW)`, `2(a+2) ≤ cW`, `κ (a+2)²/(c W²) ≤ δ` and
`δ + 2(a+2)/W ≤ 1`, then every `[v, v + δ] ⊆ [0,1]` meets `rowSet c O k₀ m`. -/
theorem row_cover {c κ r₀ a δ v : ℚ} {m : ℕ} (k₀ : ℕ) {O : Set ℚ}
    (hc : 0 < c) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hO : ∀ r, r₀ ≤ r → r ≤ 1 / 2 → ∃ o ∈ O, r ≤ o ∧ o ≤ r + κ * r ^ 2)
    (hr₀ : r₀ ≤ a / (c * 2 ^ m)) (hW : 2 * (a + 2) ≤ c * 2 ^ m)
    (hδ : κ * (a + 2) ^ 2 / (c * (2 ^ m) ^ 2) ≤ δ) (hδ1 : δ + 2 * (a + 2) / 2 ^ m ≤ 1)
    (hv : 0 ≤ v) (hvδ : v + δ ≤ 1) :
    ∃ p ∈ rowSet c O k₀ m, v ≤ p ∧ p ≤ v + δ := by
  have hWpos : (0 : ℚ) < 2 ^ m := by positivity
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
  have he : (a + 2) / 2 ^ m = a / 2 ^ m + 2 / 2 ^ m := add_div _ _ _
  have he2 : 2 * (a + 2) / 2 ^ m = 2 * (a / 2 ^ m) + 2 * (2 / 2 ^ m) := by ring
  have hpos0 : 0 ≤ a / (2 : ℚ) ^ m := by positivity
  have hpos2 : 0 < 2 / (2 : ℚ) ^ m := by positivity
  -- a displacement `d ∈ [a/W, (a+2)/W]` gives an admissible radius `r = d/c`
  -- whose error `c κ r² = κ d²/c` is at most `δ`
  have key : ∀ d, a / 2 ^ m ≤ d → d ≤ (a + 2) / 2 ^ m →
      r₀ ≤ d / c ∧ d / c ≤ 1 / 2 ∧ c * (d / c) = d ∧ c * (κ * (d / c) ^ 2) ≤ δ := by
    intro d hd1 hd2
    have hd0 : 0 ≤ d := le_trans hpos0 hd1
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc r₀ ≤ a / (c * 2 ^ m) := hr₀
        _ = a / 2 ^ m / c := by rw [div_div, mul_comm]
        _ ≤ d / c := div_le_div_of_nonneg_right hd1 hc.le
    · rw [div_le_iff₀ hc]
      have : (a + 2) / 2 ^ m ≤ 1 / 2 * c := by
        rw [div_le_iff₀ hWpos]; linarith
      linarith
    · field_simp
    · have hsq : d ^ 2 ≤ ((a + 2) / 2 ^ m) ^ 2 := pow_le_pow_left₀ hd0 hd2 2
      calc c * (κ * (d / c) ^ 2) = κ * d ^ 2 / c := by field_simp
        _ ≤ κ * ((a + 2) / 2 ^ m) ^ 2 / c := by gcongr
        _ = κ * (a + 2) ^ 2 / (c * (2 ^ m) ^ 2) := by field_simp
        _ ≤ δ := hδ
  by_cases hcase : v + δ + (a + 2) / 2 ^ m ≤ 1
  · -- room on the right: `l = vdC k ∈ [v + δ + a/W, v + δ + (a+2)/W]`, point `l - c·o`
    obtain ⟨k, hk1, hk2, hl1, hl2⟩ :=
      vdC_hits m k₀ (u := v + δ + a / 2 ^ m) (by linarith) (by linarith)
    obtain ⟨hr1, hr2, hcr, hcκ⟩ := key (vdC k - (v + δ)) (by linarith) (by linarith)
    obtain ⟨o, hoO, ho1, ho2⟩ := hO _ hr1 hr2
    have hlow := mul_le_mul_of_nonneg_left ho1 hc.le
    have hup := mul_le_mul_of_nonneg_left ho2 hc.le
    rw [mul_add] at hup
    exact ⟨vdC k - c * o, ⟨k, hk1, hk2, o, hoO, Or.inl rfl⟩, by linarith, by linarith⟩
  · -- otherwise `v` is far from `0`: `l ∈ [v - (a+2)/W, v - a/W]`, point `l + c·o`
    rw [not_le] at hcase
    obtain ⟨k, hk1, hk2, hl1, hl2⟩ :=
      vdC_hits m k₀ (u := v - (a + 2) / 2 ^ m) (by linarith) (by linarith)
    obtain ⟨hr1, hr2, hcr, hcκ⟩ := key (v - vdC k) (by linarith) (by linarith)
    obtain ⟨o, hoO, ho1, ho2⟩ := hO _ hr1 hr2
    have hlow := mul_le_mul_of_nonneg_left ho1 hc.le
    have hup := mul_le_mul_of_nonneg_left ho2 hc.le
    rw [mul_add] at hup
    exact ⟨vdC k + c * o, ⟨k, hk1, hk2, o, hoO, Or.inr rfl⟩, by linarith, by linarith⟩

/-- (Row covering at `c = 1/4`, `m ≥ 7`) With `δ = 256 κ / W² = 64 κ/(c W²)`,
`r₀ ≤ 16/W = 4/(cW)` and `δ + 16/W ≤ 1/2`, every `[v, v + δ] ⊆ [0,1]` contains a point
`vdC k ± o/4` (`k₀ ≤ k < k₀ + W`, `o ∈ O`), and that point lies in `[0,1]`. -/
theorem row_cover_quarter {κ r₀ v : ℚ} {m : ℕ} (k₀ : ℕ) {O : Set ℚ} (hm : 7 ≤ m)
    (hκ : 0 ≤ κ) (hO : ∀ r, r₀ ≤ r → r ≤ 1 / 2 → ∃ o ∈ O, r ≤ o ∧ o ≤ r + κ * r ^ 2)
    (hr₀ : r₀ ≤ 16 / 2 ^ m) (hδ1 : 256 * κ / (2 ^ m) ^ 2 + 16 / 2 ^ m ≤ 1 / 2)
    (hv : 0 ≤ v) (hvδ : v + 256 * κ / (2 ^ m) ^ 2 ≤ 1) :
    ∃ p ∈ rowSet (1 / 4) O k₀ m,
      v ≤ p ∧ p ≤ v + 256 * κ / (2 ^ m) ^ 2 ∧ 0 ≤ p ∧ p ≤ 1 := by
  have hWpos : (0 : ℚ) < 2 ^ m := by positivity
  have hW : (128 : ℚ) ≤ 2 ^ m := by
    calc (128 : ℚ) = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hδ0 : 0 ≤ 256 * κ / ((2 : ℚ) ^ m) ^ 2 := by positivity
  obtain ⟨p, hp, hp1, hp2⟩ := row_cover (c := 1 / 4) (a := 4) k₀ (by norm_num) (by norm_num) hκ
    hO (by rw [show (4 : ℚ) / (1 / 4 * 2 ^ m) = 16 / 2 ^ m by field_simp; norm_num]; exact hr₀)
    (by linarith)
    (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ κ * ((2 : ℚ) ^ m) ^ 2 := by positivity
      nlinarith)
    (by
      have : (2 * (4 + 2) : ℚ) / 2 ^ m ≤ 16 / 2 ^ m :=
        div_le_div_of_nonneg_right (by norm_num) hWpos.le
      have : (16 : ℚ) / 2 ^ m ≤ 1 / 8 := by rw [div_le_iff₀ hWpos]; linarith
      linarith)
    hv hvδ
  exact ⟨p, hp, hp1, hp2, by linarith, by linarith⟩

/-! ## The combined statement -/

/-- The row points `vdC k ± o/4`, `k₀ ≤ k < k₀ + 2^m`, `o ∈ offsets D θ`. -/
abbrev rowPoints (k₀ m D : ℕ) (θ : ℚ) : Set ℚ := rowSet (1 / 4) ↑(offsets D θ) k₀ m

/-- (Combined, `C = 1152`) For `m ≥ 6`, `W = 2^m`, `θ ∈ [0,1]` and `t D ≤ 16/W = 4/(cW)`,
the row points meet every interval `[x, y] ⊆ [0,1]` of length at least `1152 / W²`. -/
theorem rowPoints_dense {k₀ m D : ℕ} {θ x y : ℚ} (hm : 6 ≤ m) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hD : t D ≤ 16 / 2 ^ m) (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x + 1152 / (2 ^ m) ^ 2 ≤ y) :
    ∃ p ∈ rowPoints k₀ m D θ, x ≤ p ∧ p ≤ y := by
  have hWpos : (0 : ℚ) < 2 ^ m := by positivity
  have hW : (64 : ℚ) ≤ 2 ^ m := by
    calc (64 : ℚ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hO : ∀ r, t D ≤ r → r ≤ 1 / 2 →
      ∃ o ∈ (↑(offsets D θ) : Set ℚ), r ≤ o ∧ o ≤ r + 8 * r ^ 2 := by
    intro r h1 h2
    obtain ⟨o, ho, ho1, ho2⟩ := offsets_dense hθ0 hθ1 h1 h2
    exact ⟨o, Finset.mem_coe.mpr ho, ho1, ho2⟩
  have hδ0 : 0 ≤ 1152 / ((2 : ℚ) ^ m) ^ 2 := by positivity
  obtain ⟨p, hp, hp1, hp2⟩ := row_cover (c := 1 / 4) (a := 4) (δ := 1152 / (2 ^ m) ^ 2) (v := x)
    k₀ (by norm_num) (by norm_num) (by norm_num) hO
    (by rw [show (4 : ℚ) / (1 / 4 * 2 ^ m) = 16 / 2 ^ m by field_simp; norm_num]; exact hD)
    (by linarith)
    (le_of_eq (by field_simp; norm_num))
    (by
      rw [div_add_div _ _ (by positivity) hWpos.ne', div_le_one (by positivity)]
      nlinarith)
    hx (by linarith)
  exact ⟨p, hp, hp1, by linarith⟩

/-- `rowPoints_dense` with the size condition `W ≤ 16 D` in place of `t D ≤ 16/W`. -/
theorem rowPoints_dense_of_le {k₀ m D : ℕ} {θ x y : ℚ} (hm : 6 ≤ m) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hD : 2 ^ m ≤ 16 * D) (hx : 0 ≤ x) (hy : y ≤ 1)
    (hxy : x + 1152 / (2 ^ m) ^ 2 ≤ y) :
    ∃ p ∈ rowPoints k₀ m D θ, x ≤ p ∧ p ≤ y :=
  rowPoints_dense hm hθ0 hθ1 (t_le_of_pow_le hD) hx hy hxy

end SourceCovers.Covering
