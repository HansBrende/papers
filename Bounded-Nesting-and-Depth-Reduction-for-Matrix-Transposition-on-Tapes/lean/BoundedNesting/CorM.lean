import BoundedNesting.TheoremM
import BoundedNesting.Stacks

/-!
# Consequences of Theorem M

* `corM1`: **Corollary M1** (scale-ratio form). If all family heights lie in `[dmin, dmax]`, the DAG
  of Theorem M has a cut of at most `εT` edges whose depth is less than
  `DM k ℓ 1 (λ dmax - λ dmin) ε ≤ 2^29 k (2N² dmax/dmin + kN)²/ε⁶` (`DM_one_le`, `two_pow_lam_sub_le`).
* `corM1_i`: heights at most `dmax`: depth less than `2^29 k (2N² + kN)² dmax²/ε⁶`.
* `corM1_ii`: if all families outside a set of at most `2N` have their band in one window of width
  `h`, the depth is less than `DM k ℓ (1 + 2N) h ε`, a bound in terms of `k`, `ℓ`, `h`, `ε` alone.
* `where_ownerLoad`, `where_windows`, `where_ratio` (**where depth-robustness lives**): a depth-robust
  family (`DepthRobust`) has unbounded owner-load; if in every member all walks but one (`others`)
  have owner-load at most `ℓ`, the number of windows of width `h` covering the family bands of the
  others is unbounded (`BandsCovered`), and so is the ratio of their largest to their smallest family
  height.
-/

namespace BoundedNesting

open Finset

/-! ### The depth bound -/

theorem mK_mono {k ℓ h : ℕ} {ε : ℝ} (hε : 0 < ε) {q q' : ℕ} (hqq : q ≤ q') :
    mK k ℓ q h ε ≤ mK k ℓ q' h ε := by
  unfold mK
  apply Nat.ceil_mono
  have hq : (q : ℝ) ≤ q' := by exact_mod_cast hqq
  have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  gcongr

theorem DM_mono {k ℓ h : ℕ} {ε : ℝ} (hε : 0 < ε) {q q' : ℕ} (hq : 1 ≤ q) (hqq : q ≤ q') :
    DM k ℓ q h ε ≤ DM k ℓ q' h ε := by
  unfold DM
  refine Nat.mul_le_mul_left _ ?_
  have h2 : 1 ≤ mK k ℓ q h ε := mK_pos hε hq
  calc mK k ℓ q h ε ^ (2 * q) ≤ mK k ℓ q h ε ^ (2 * q') := Nat.pow_le_pow_right h2 (by omega)
    _ ≤ mK k ℓ q' h ε ^ (2 * q') := Nat.pow_le_pow_left (mK_mono hε hqq) _

theorem mw_le {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (mw k ε : ℝ) ≤ 2 * (8 * (4 + 2 * (k : ℝ)) / ε) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx1 : 1 ≤ 8 * (4 + 2 * (k : ℝ)) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hlog : 0 ≤ Real.logb 2 (8 * (4 + 2 * (k : ℝ)) / ε) := Real.logb_nonneg (by norm_num) hx1
  have h1 : (mExp k ε : ℝ) < Real.logb 2 (8 * (4 + 2 * (k : ℝ)) / ε) + 1 := Nat.ceil_lt_add_one hlog
  unfold mw
  push_cast
  calc (2 : ℝ) ^ mExp k ε = (2 : ℝ) ^ ((mExp k ε : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
    _ ≤ (2 : ℝ) ^ (Real.logb 2 (8 * (4 + 2 * (k : ℝ)) / ε) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
    _ = 2 * (8 * (4 + 2 * (k : ℝ)) / ε) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
          Real.rpow_one]
        ring

/-- **The depth bound for one window**: `DM k ℓ 1 h ε ≤ 2^29 k (N² 2^h + kN)²/ε⁶`, `N = 2kℓ`. -/
theorem DM_one_le {k ℓ h : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (DM k ℓ 1 h ε : ℝ) ≤
      2 ^ 29 * k * (((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ h + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 / ε ^ 6 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN1 : (1 : ℝ) ≤ ((2 * k * ℓ : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * k * ℓ by nlinarith)
  have hu1 : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hεu : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hh : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hw : (mw k ε : ℝ) ≤ 96 * k * ε⁻¹ := by
    have := mw_le (k := k) hε hε1
    rw [div_eq_mul_inv] at this
    nlinarith
  have hK₀ : (mK0 k ε : ℝ) ≤ 777 * k * ε⁻¹ ^ 2 := by
    have h1 : (mK0 k ε : ℝ) < 8 * ((mw k ε : ℝ) + 1) / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [div_eq_mul_inv] at h1
    have hu2 : ε⁻¹ ≤ ε⁻¹ ^ 2 := by nlinarith
    nlinarith
  have hK : (mK k ℓ 1 h ε : ℝ) ≤ 785 * (((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ h + k * ((2 * k * ℓ : ℕ) : ℝ)) *
      ε⁻¹ ^ 2 := by
    have h1 := Nat.ceil_lt_add_one (R := ℝ) (a := 8 / ε * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) *
      ((2 * k * ℓ : ℕ) : ℝ) + 64 * ((1 : ℕ) : ℝ) ^ 2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ h / ε +
      ((1 : ℕ) : ℝ) * (mw k ε : ℝ) * ((2 * k * ℓ : ℕ) : ℝ) + ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ (h + 1)))
      (by positivity)
    change (mK k ℓ 1 h ε : ℝ) < _ at h1
    simp only [Nat.cast_one, one_mul, one_pow, mul_one] at h1
    rw [show (2 : ℝ) ^ (h + 1) = 2 ^ h * 2 from pow_succ 2 h, div_eq_mul_inv, div_eq_mul_inv] at h1
    set N : ℝ := ((2 * k * ℓ : ℕ) : ℝ)
    set u := ε⁻¹
    have hNk : N ≤ k * N := le_mul_of_one_le_left (by linarith) hk1
    have hb : 1 + N + 64 * N ^ 2 * 2 ^ h * u + (mw k ε : ℝ) * N + N ^ 2 * (2 ^ h * 2) ≤
        98 * (N ^ 2 * 2 ^ h + k * N) * u := by
      have e1 : (mw k ε : ℝ) * N ≤ 96 * k * u * N := mul_le_mul_of_nonneg_right hw (by linarith)
      have e2 : 1 + N ≤ 2 * (k * N) * u := by nlinarith
      have e3 : N ^ 2 * (2 ^ h * 2) ≤ 2 * (N ^ 2 * 2 ^ h) * u := by
        have : 0 ≤ N ^ 2 * 2 ^ h := by positivity
        nlinarith
      nlinarith
    have hY : 1 ≤ N ^ 2 * 2 ^ h + k * N := by nlinarith
    have hu2 : 1 ≤ u ^ 2 := by nlinarith
    refine le_of_lt ?_
    calc (mK k ℓ 1 h ε : ℝ) < 8 * u * (1 + N + 64 * N ^ 2 * 2 ^ h * u + (mw k ε : ℝ) * N +
          N ^ 2 * (2 ^ h * 2)) + 1 := by linarith
      _ ≤ 8 * u * (98 * (N ^ 2 * 2 ^ h + k * N) * u) + 1 :=
          by gcongr
      _ ≤ 785 * (N ^ 2 * 2 ^ h + k * N) * u ^ 2 := by nlinarith
  have eDM : (DM k ℓ 1 h ε : ℝ) = (mK0 k ε : ℝ) * (mK k ℓ 1 h ε : ℝ) ^ (2 * 1) := by
    unfold DM
    push_cast
    ring
  rw [eDM]
  set N : ℝ := ((2 * k * ℓ : ℕ) : ℝ)
  set Y := N ^ 2 * 2 ^ h + k * N
  have hY0 : 0 ≤ Y := by positivity
  have hK0 : (0 : ℝ) ≤ mK k ℓ 1 h ε := Nat.cast_nonneg _
  have hK2 : (mK k ℓ 1 h ε : ℝ) ^ 2 ≤ (785 * Y * ε⁻¹ ^ 2) ^ 2 := pow_le_pow_left₀ hK0 hK _
  calc (mK0 k ε : ℝ) * (mK k ℓ 1 h ε : ℝ) ^ (2 * 1) ≤ (777 * k * ε⁻¹ ^ 2) * (785 * Y * ε⁻¹ ^ 2) ^ 2 := by
        rw [show 2 * 1 = 2 by rfl]
        exact mul_le_mul hK₀ hK2 (by positivity) (by positivity)
    _ = 777 * 785 ^ 2 * k * Y ^ 2 * ε⁻¹ ^ 6 := by ring
    _ ≤ 2 ^ 29 * k * Y ^ 2 * ε⁻¹ ^ 6 := by
        have : (0 : ℝ) ≤ k * Y ^ 2 * ε⁻¹ ^ 6 := by positivity
        nlinarith
    _ = 2 ^ 29 * k * Y ^ 2 / ε ^ 6 := by rw [inv_pow, div_eq_mul_inv]

/-- `2^(λ dmax - λ dmin) ≤ 2 dmax/dmin`. -/
theorem two_pow_lam_sub_le {dmin dmax : ℕ} (hd : 1 ≤ dmin) (hle : dmin ≤ dmax) :
    (2 : ℝ) ^ (lam dmax - lam dmin) ≤ 2 * dmax / dmin := by
  have hl : lam dmin ≤ lam dmax := Nat.log_mono_right hle
  have h1 : 2 ^ lam dmax ≤ dmax := Nat.pow_log_le_self 2 (by omega)
  have h2 : dmin < 2 ^ (lam dmin + 1) := Nat.lt_pow_succ_log_self (by norm_num) dmin
  have h3 : 2 ^ (lam dmax - lam dmin) * dmin ≤ 2 * dmax := by
    calc 2 ^ (lam dmax - lam dmin) * dmin ≤ 2 ^ (lam dmax - lam dmin) * 2 ^ (lam dmin + 1) :=
          Nat.mul_le_mul_left _ h2.le
      _ = 2 * 2 ^ lam dmax := by
          rw [← pow_add, show lam dmax - lam dmin + (lam dmin + 1) = lam dmax + 1 by omega, pow_succ]
          ring
      _ ≤ 2 * dmax := Nat.mul_le_mul_left _ h1
  have hd' : (0 : ℝ) < dmin := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast h3

/-! ### Corollary M1 -/

section M1

variable {k ℓ T : ℕ} {x0 : ℕ → ℤ} {xs : Fin k → ℕ → ℤ} {H' : Finset (Fin k × ℕ × ℕ)}
  {own : Fin k × ℕ × ℕ → ℕ}

/-- **Corollary M1** (scale-ratio form): heights in `[dmin, dmax]`, a cut of at most `εT` edges and
depth less than `2^29 k (2N² dmax/dmin + kN)²/ε⁶`. -/
theorem corM1 (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hx0 : IsWalk x0)
    (hx : ∀ i, IsWalk (xs i)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (hown : ∀ η ∈ H', η.2.1 < own η ∧ own η < η.2.2) (hload : OwnerLoadLE xs H' own ℓ)
    {dmin dmax : ℕ} (hdmin : 1 ≤ dmin) (hdle : dmin ≤ dmax)
    (hd : ∀ F : Keys xs H' own, dmin ≤ famd xs H' own F ∧ famd xs H' own F ≤ dmax) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hops x0 T ∪ hopPairs H' ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card <
          DM k ℓ 1 (lam dmax - lam dmin) ε ∧
        (((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card : ℝ) <
          2 ^ 29 * k * (2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * (dmax / dmin) + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 /
            ε ^ 6 := by
  have hl : lam dmin ≤ lam dmax := Nat.log_mono_right hdle
  obtain ⟨cutS, cutH, h1, h2, h3, h4⟩ := theoremM hℓ le_rfl hε hε1 x0 hx0 xs hx H' hH own hown hload
    (fun _ : Fin 1 => lam dmin) (Subsingleton.strictMono _) (h := lam dmax - lam dmin) (fun F =>
      ⟨0, Nat.log_mono_right (hd F).1, by
        have := Nat.log_mono_right (b := 2) (hd F).2
        simp only [lam] at this ⊢
        omega⟩)
  refine ⟨cutS, cutH, h1, h2, h3, fun f n hp => ⟨h4 f n hp, ?_⟩⟩
  have hc := h4 f n hp
  have hDM := DM_one_le (h := lam dmax - lam dmin) hk hℓ hε hε1
  have h2h := two_pow_lam_sub_le hdmin hdle
  have hN0 : (0 : ℝ) ≤ ((2 * k * ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmono : (((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ (lam dmax - lam dmin) + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 ≤
      (2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * (dmax / dmin) + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    have : ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * 2 ^ (lam dmax - lam dmin) ≤
        ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * (2 * dmax / dmin) := mul_le_mul_of_nonneg_left h2h (by positivity)
    rw [mul_div_assoc] at this
    linarith
  calc (((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card : ℝ)
      < DM k ℓ 1 (lam dmax - lam dmin) ε := by exact_mod_cast hc
    _ ≤ _ := hDM
    _ ≤ _ := by
        have : (0 : ℝ) < ε ^ 6 := by positivity
        gcongr

/-- **Corollary M1 (i)**: heights at most `dmax`, depth less than `2^29 k (2N² + kN)² dmax²/ε⁶`. -/
theorem corM1_i (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hx0 : IsWalk x0)
    (hx : ∀ i, IsWalk (xs i)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (hown : ∀ η ∈ H', η.2.1 < own η ∧ own η < η.2.2) (hload : OwnerLoadLE xs H' own ℓ)
    {dmax : ℕ} (hdmax : 1 ≤ dmax) (hd : ∀ F : Keys xs H' own, famd xs H' own F ≤ dmax) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hops x0 T ∪ hopPairs H' ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        (((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card : ℝ) <
          2 ^ 29 * k * (2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 * dmax ^ 2 /
            ε ^ 6 := by
  have hA := famData_valid (T := T) hx hH hown (by omega : 0 < ℓ) hload
  obtain ⟨cutS, cutH, h1, h2, h3, h4⟩ := corM1 (x0 := x0) hk hℓ hε hε1 hx0 hx hH hown hload le_rfl
    hdmax (fun F => ⟨hA.d_pos F, hd F⟩)
  refine ⟨cutS, cutH, h1, h2, h3, fun f n hp => ?_⟩
  refine (h4 f n hp).2.trans_le ?_
  have hd1 : (1 : ℝ) ≤ dmax := by exact_mod_cast hdmax
  have hN0 : (0 : ℝ) ≤ ((2 * k * ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have : (2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * (dmax / ((1 : ℕ) : ℝ)) + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 ≤
      (2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 * dmax ^ 2 := by
    rw [Nat.cast_one, div_one, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hk0 hN0) (sub_nonneg.mpr hd1)]
  have hε6 : (0 : ℝ) < ε ^ 6 := by positivity
  calc 2 ^ 29 * k * (2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 * (dmax / ((1 : ℕ) : ℝ)) + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 /
        ε ^ 6 ≤ 2 ^ 29 * k * ((2 * ((2 * k * ℓ : ℕ) : ℝ) ^ 2 + k * ((2 * k * ℓ : ℕ) : ℝ)) ^ 2 * dmax ^ 2) /
          ε ^ 6 := by gcongr
    _ = _ := by ring

/-- **Corollary M1 (ii)**: if all families outside a set of at most `2N` have their band in one
window `[β₀, β₀ + h]`, the depth is less than `DM k ℓ (1 + 2N) h ε`, which depends on `k`, `ℓ`, `h`
and `ε` alone. -/
theorem corM1_ii (hℓ : 1 ≤ ℓ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hx0 : IsWalk x0)
    (hx : ∀ i, IsWalk (xs i)) (hH : ∀ η ∈ H', IsHop (xs η.1) T η.2.1 η.2.2)
    (hown : ∀ η ∈ H', η.2.1 < own η ∧ own η < η.2.2) (hload : OwnerLoadLE xs H' own ℓ)
    {h β₀ : ℕ} (Exc : Finset (Keys xs H' own)) (hExc : Exc.card ≤ 2 * (2 * k * ℓ))
    (hband : ∀ F, F ∉ Exc → β₀ ≤ lam (famd xs H' own F) ∧ lam (famd xs H' own F) ≤ β₀ + h) :
    ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 T ∧
      cutH ⊆ hops x0 T ∪ hopPairs H' ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * T ∧
      ∀ (f : ℕ → ℕ) (n : ℕ),
        (∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < T ∧ f i ∉ cutS) ∨
          ((f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H' ∧ (f (i + 1), f i) ∉ cutH)) →
        ((range n).filter (fun i => (f (i + 1), f i) ∈ hops x0 T ∪ hopPairs H')).card <
          DM k ℓ (1 + 2 * (2 * k * ℓ)) h ε := by
  classical
  set B : Finset ℕ := insert β₀ (Exc.image fun F => lam (famd xs H' own F)) with hB
  have hB1 : 1 ≤ B.card := card_pos.mpr ⟨β₀, mem_insert_self _ _⟩
  have hBq : B.card ≤ 1 + 2 * (2 * k * ℓ) := by
    rw [hB]
    have := card_image_le (s := Exc) (f := fun F => lam (famd xs H' own F))
    exact (card_insert_le _ _).trans (by omega)
  have hrange : ∀ b ∈ B, ∃ j, B.orderEmbOfFin rfl j = b := by
    intro b hb
    have : b ∈ Set.range (B.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hb
    exact this
  obtain ⟨cutS, cutH, h1, h2, h3, h4⟩ := theoremM hℓ hB1 hε hε1 x0 hx0 xs hx H' hH own hown hload
    (B.orderEmbOfFin rfl) (B.orderEmbOfFin rfl).strictMono (h := h) (fun F => by
      by_cases hF : F ∈ Exc
      · obtain ⟨j, hj⟩ := hrange _ (mem_insert_of_mem (mem_image_of_mem _ hF))
        exact ⟨j, hj.le, by omega⟩
      · obtain ⟨j, hj⟩ := hrange _ (mem_insert_self _ _)
        have := hband F hF
        exact ⟨j, by omega, by omega⟩)
  exact ⟨cutS, cutH, h1, h2, h3, fun f n hp => (h4 f n hp).trans_le (DM_mono hε hB1 hBq)⟩

end M1

/-! ### Where depth-robustness lives -/

section Where

variable {k : ℕ}

/-- TCP for a family `𝒲` of `k`-tuples of walks, each with its length, at `ε` and `D`: the walk DAG of
every member has a cut of at most `εT` edges and depth at most `D`. -/
def FamTCPAt (𝒲 : Set (ℕ × (Fin k → ℕ → ℤ))) (ε : ℝ) (D : ℕ) : Prop :=
  ∀ p ∈ 𝒲, ∃ (cutS : Finset ℕ) (cutH : Finset (ℕ × ℕ)), cutS ⊆ Ico 1 p.1 ∧
    cutH ⊆ hopPairs (allHops p.2 p.1) ∧ ((cutS.card + cutH.card : ℕ) : ℝ) ≤ ε * p.1 ∧
    ∀ f n, AvoidPath p.1 (hopPairs (allHops p.2 p.1)) cutH cutS f n →
      arcCount (hopPairs (allHops p.2 p.1)) f n ≤ D

/-- **TCP holds for the family** `𝒲`: for every `ε > 0` some `D` serves all members. -/
def FamTCP (𝒲 : Set (ℕ × (Fin k → ℕ → ℤ))) : Prop := ∀ ε : ℝ, 0 < ε → ∃ D, FamTCPAt 𝒲 ε D

/-- A family is **depth-robust** if TCP fails for it: for some `ε > 0` no single `D` serves all
members. -/
def DepthRobust (𝒲 : Set (ℕ × (Fin k → ℕ → ℤ))) : Prop := ∃ ε : ℝ, 0 < ε ∧ ∀ D, ¬ FamTCPAt 𝒲 ε D

/-- Depth-robustness is the failure of TCP. -/
theorem depthRobust_iff (𝒲 : Set (ℕ × (Fin k → ℕ → ℤ))) : DepthRobust 𝒲 ↔ ¬ FamTCP 𝒲 := by
  unfold DepthRobust FamTCP
  push Not
  rfl

/-- `TCP(k)` is TCP for the family of all `k`-tuples of walks. -/
theorem tcp_iff_famTCP : TCP k ↔ FamTCP {p : ℕ × (Fin k → ℕ → ℤ) | ∀ i, IsWalk (p.2 i)} := by
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    exact ⟨D, fun p hp => hD p.1 p.2 hp⟩
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    exact ⟨D, fun T xs hx => hD (T, xs) hx⟩

/-- The owners of the paper for the hops of `xs`. -/
noncomputable def owners (xs : Fin k → ℕ → ℤ) : Fin k × ℕ × ℕ → ℕ :=
  fun η => hopOwner (xs η.1) η.2.1 η.2.2

/-- The family bands of `xs` (all long hops, the owners of the paper) are covered by at most `q`
windows `[b, b + h]`. -/
def BandsCovered (xs : Fin k → ℕ → ℤ) (T h q : ℕ) : Prop :=
  ∃ B : Finset ℕ, B.card ≤ q ∧ ∀ F : Keys xs (allHops xs T) (owners xs),
    ∃ b ∈ B, b ≤ lam (famd xs (allHops xs T) (owners xs) F) ∧
      lam (famd xs (allHops xs T) (owners xs) F) ≤ b + h

theorem OwnerLoadLE.mono {xs : Fin k → ℕ → ℤ} {H' : Finset (Fin k × ℕ × ℕ)}
    {own : Fin k × ℕ × ℕ → ℕ} {ℓ ℓ' : ℕ} (h : OwnerLoadLE xs H' own ℓ) (hl : ℓ ≤ ℓ') :
    OwnerLoadLE xs H' own ℓ' := fun i σ t => (h i σ t).trans hl

/-- The walks of `xs` other than the `i₀`-th. -/
def others (xs : Fin (k + 1) → ℕ → ℤ) (i₀ : Fin (k + 1)) : Fin k → ℕ → ℤ :=
  fun i => xs (i₀.succAbove i)

/-- The walk DAG of `k + 1` walks: the hops of the `i₀`-th walk and those of the others. -/
theorem hopPairs_allHops_succAbove (xs : Fin (k + 1) → ℕ → ℤ) (i₀ : Fin (k + 1)) (T : ℕ) :
    hopPairs (allHops xs T) = hops (xs i₀) T ∪ hopPairs (allHops (others xs i₀) T) := by
  ext e
  simp only [hopPairs, mem_image, mem_union, mem_allHops, mem_hops]
  constructor
  · rintro ⟨η, hη, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove i₀ η.1 with h0 | ⟨i, hi⟩
    · left
      rw [h0] at hη
      exact hη
    · right
      exact ⟨(i, η.2.1, η.2.2), by rw [hi] at hη; exact hη, rfl⟩
  · rintro (h | ⟨η, hη, rfl⟩)
    · exact ⟨(i₀, e.1, e.2), h, rfl⟩
    · exact ⟨(i₀.succAbove η.1, η.2.1, η.2.2), hη, rfl⟩

/-- **Where depth-robustness lives (1).** A depth-robust family has unbounded owner-load. -/
theorem where_ownerLoad (𝒲 : Set (ℕ × (Fin k → ℕ → ℤ))) (hw : ∀ p ∈ 𝒲, ∀ i, IsWalk (p.2 i))
    (hr : DepthRobust 𝒲) (ℓ : ℕ) :
    ∃ p ∈ 𝒲, ¬ OwnerLoadLE p.2 (allHops p.2 p.1) (owners p.2) ℓ := by
  obtain ⟨ε, hε, hD⟩ := hr
  by_contra hno
  push Not at hno
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    refine hD 0 fun p _ => ⟨∅, ∅, empty_subset _, empty_subset _, ?_, fun f n _ => ?_⟩
    · simp only [card_empty, add_zero, Nat.cast_zero]
      exact mul_nonneg hε.le (Nat.cast_nonneg _)
    · have : allHops p.2 p.1 = ∅ := by
        ext η
        exact η.1.elim0
      simp [this, hopPairs, arcCount]
  · refine hD (DF k (max ℓ 1) ε) fun p hp => ?_
    obtain ⟨cutS, cutH, h1, h2, h3, h4⟩ := theoremF_owner hk (le_max_right ℓ 1) hε p.2 (hw p hp)
      (allHops p.2 p.1) (fun η hη => mem_allHops.mp hη) ((hno p hp).mono (le_max_left _ _))
    exact ⟨cutS, cutH, h1, h2, h3, fun f n hp' => (h4 f n hp').le⟩

/-- **Where depth-robustness lives (2).** If, in every member of a depth-robust family, all walks but
one (the walk `e p`) have owner-load at most `ℓ`, then for every `h` the number of windows of width `h`
needed to cover the family bands of the others is unbounded. -/
theorem where_windows (𝒲 : Set (ℕ × (Fin (k + 1) → ℕ → ℤ))) (hw : ∀ p ∈ 𝒲, ∀ i, IsWalk (p.2 i))
    (hr : DepthRobust 𝒲) {ℓ : ℕ} (e : ℕ × (Fin (k + 1) → ℕ → ℤ) → Fin (k + 1))
    (hbound : ∀ p ∈ 𝒲, OwnerLoadLE (others p.2 (e p)) (allHops (others p.2 (e p)) p.1)
      (owners (others p.2 (e p))) ℓ) (h q : ℕ) :
    ∃ p ∈ 𝒲, ¬ BandsCovered (others p.2 (e p)) p.1 h q := by
  classical
  obtain ⟨ε, hε, hD⟩ := hr
  by_contra hno
  push Not at hno
  set ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε one_pos
  refine hD (DM k (max ℓ 1) (q + 1) h ε') fun p hp => ?_
  obtain ⟨B, hBq, hB⟩ := hno p hp
  set ys : Fin k → ℕ → ℤ := others p.2 (e p)
  set B' := insert 0 B
  have hB1 : 1 ≤ B'.card := card_pos.mpr ⟨0, mem_insert_self _ _⟩
  have hBq' : B'.card ≤ q + 1 := (card_insert_le _ _).trans (by omega)
  have hrange : ∀ b ∈ B', ∃ j, B'.orderEmbOfFin rfl j = b := by
    intro b hb
    have : b ∈ Set.range (B'.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hb
    exact this
  obtain ⟨cutS, cutH, h1, h2, h3, h4⟩ := theoremM_owner (le_max_right ℓ 1) hB1 hε'
    (min_le_right _ _) (p.2 (e p)) (hw p hp (e p)) ys (fun i => hw p hp _) (allHops ys p.1)
    (fun η hη => mem_allHops.mp hη) ((hbound p hp).mono (le_max_left _ _)) (B'.orderEmbOfFin rfl)
    (B'.orderEmbOfFin rfl).strictMono (h := h) (fun F => by
      obtain ⟨b, hb, hb1, hb2⟩ := hB F
      obtain ⟨j, hj⟩ := hrange b (mem_insert_of_mem hb)
      exact ⟨j, by rw [hj]; exact hb1, by rw [hj]; exact hb2⟩)
  have hE := hopPairs_allHops_succAbove p.2 (e p) p.1
  refine ⟨cutS, cutH, h1, by rw [hE]; exact h2, h3.trans ?_, fun f n hp' => ?_⟩
  · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  · have hp'' : ∀ i < n, (f (i + 1) + 1 = f i ∧ 1 ≤ f i ∧ f i < p.1 ∧ f i ∉ cutS) ∨
        ((f (i + 1), f i) ∈ hops (p.2 (e p)) p.1 ∪ hopPairs (allHops ys p.1) ∧
          (f (i + 1), f i) ∉ cutH) := by
      intro i hi
      have := hp' i hi
      rw [hE] at this
      exact this
    have := (h4 f n hp'').trans_le (DM_mono hε' hB1 hBq')
    unfold arcCount
    rw [hE]
    exact this.le

theorem lam_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : lam (a * b) ≤ lam a + lam b + 1 := by
  show Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1
  have h1 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
  have h2 : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by norm_num) b
  have h3 : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
          mul_lt_mul'' h1 h2 (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero ha hb) h3
  omega

/-- **Where depth-robustness lives (3).** In the situation of (2), the ratio of the largest to the
smallest family height of the walks other than `e p` is unbounded. -/
theorem where_ratio (𝒲 : Set (ℕ × (Fin (k + 1) → ℕ → ℤ))) (hw : ∀ p ∈ 𝒲, ∀ i, IsWalk (p.2 i))
    (hr : DepthRobust 𝒲) {ℓ : ℕ} (e : ℕ × (Fin (k + 1) → ℕ → ℤ) → Fin (k + 1))
    (hbound : ∀ p ∈ 𝒲, OwnerLoadLE (others p.2 (e p)) (allHops (others p.2 (e p)) p.1)
      (owners (others p.2 (e p))) ℓ) (R : ℕ) :
    ∃ p ∈ 𝒲, ∃ F F' : Keys (others p.2 (e p)) (allHops (others p.2 (e p)) p.1)
        (owners (others p.2 (e p))),
      R * famd (others p.2 (e p)) (allHops (others p.2 (e p)) p.1) (owners (others p.2 (e p))) F' <
        famd (others p.2 (e p)) (allHops (others p.2 (e p)) p.1) (owners (others p.2 (e p))) F := by
  by_contra hno
  push Not at hno
  obtain ⟨p, hp, hnc⟩ := where_windows 𝒲 hw hr e hbound (2 * (lam R + 1)) 1
  apply hnc
  have hA := famData_valid (T := p.1) (xs := others p.2 (e p))
    (H' := allHops (others p.2 (e p)) p.1) (own := owners (others p.2 (e p)))
    (fun i => hw p hp _) (fun η hη => mem_allHops.mp hη)
    (fun η hη => ⟨(hopOwner_spec _ (mem_allHops.mp hη).1).1, (hopOwner_spec _ (mem_allHops.mp hη).1).2.1⟩)
    (show 0 < max ℓ 1 from lt_max_of_lt_right one_pos) ((hbound p hp).mono (le_max_left _ _))
  by_cases hne : Nonempty (Keys (others p.2 (e p)) (allHops (others p.2 (e p)) p.1)
      (owners (others p.2 (e p))))
  · obtain ⟨F₀⟩ := hne
    refine ⟨{lam (famd (others p.2 (e p)) (allHops (others p.2 (e p)) p.1)
      (owners (others p.2 (e p))) F₀) - (lam R + 1)}, by simp, fun F => ?_⟩
    have hd := hA.d_pos F
    have hd₀ := hA.d_pos F₀
    have h1 := hno p hp F F₀
    have h2 := hno p hp F₀ F
    simp only [famData] at hd hd₀
    have hR : R ≠ 0 := by
      rintro rfl
      simp only [zero_mul] at h1
      omega
    have l1 := (Nat.log_mono_right (b := 2) h1).trans (lam_mul_le hR (by omega))
    have l2 := (Nat.log_mono_right (b := 2) h2).trans (lam_mul_le hR (by omega))
    simp only [lam] at l1 l2 ⊢
    exact ⟨_, mem_singleton_self _, by omega, by omega⟩
  · exact ⟨∅, by simp, fun F => (hne ⟨F⟩).elim⟩

end Where

end BoundedNesting
