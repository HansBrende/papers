import MergeDepth.StraddleResonance

/-!
# Partial results on Conjecture S: fine floors and near semi-local frequencies (Proposition 7.15)

Throughout, `4(j₀ + a) ≤ N` (the size condition) and `κ = κ_a(k)` for `k ∈ 𝒦`.

* `sincBound c t = min(1, (πc|t|)^{-4})`; `summable_sincBound`: `∑_t sb_c(t) ≤ 8/(3πc)`;
  `summable_abs_mul_sincBound`: `∑_t |t| sb_c(t) ≤ 3/(πc)²` (telescoping, no integrals).
* Arithmetic of `κ_a`: `rhoK`, `ellK`, `dRho`, `cancellerBelow_eq`, `nKappa_eq`
  (`n_κ = (a + 1)ℓ_k`), `rho_ell_injective`, `ell_range_card`, `sum_coarse_le_pairs`.
* `sum_cosProd_le`, `sum_slProd_le`: Lemma 7.14(b) for the products of `F(n, D)` and of the
  semi-local terms.
* (a) `sum_fineFloorK_le`: **Proposition 7.15(a)**,
  `∑_{k ∈ 𝒦} F_k ≤ C_a = (a+1)(3(2^{a+4}/π)² + 8·2^{a+4}/(3π))`, so the average is `O_a(1/N)`.
* (b) `semiLocal` `= SL^{[h]}_k`; `sum_semiLocal_le`: **Proposition 7.15(b)**,
  `∑_{k ∈ 𝒦} ∑_{h=2}^{min(H,k)} SL^{[h]}_k ≤ (a+1) 2^{a+H+8}/(3π)` for every `H`.
* (c) `sideband` `= SB_k`, `relVariance_decomp`: `V_k = SB_k + F_k + ∑_{h=2}^{k} SL^{[h]}_k`;
  `nonLocalGen` `= NL_k` for a cut-off `H`; `conjectureS_iff_meanNonLocalGen`:
  **Proposition 7.15(c)**, for every cut-off sequence `H` with `2^H/N → 0`;
  `conjectureS_iff_meanNonLocal`: the case `H = H_N = ⌊¼ log₂ N⌋` (`hN`, `nonLocal`).
-/

namespace MergeDepth

open Finset Real DirectedReciprocity

/-! ### Sums of the sinc bound -/

/-- Telescoping: if `α f(t) ≤ Φ(t) - Φ(t + 1)` and `Φ ≥ 0`, then `α ∑_{t<T} f(t) ≤ Φ(0)`. -/
theorem telescope_le {f Φ : ℕ → ℝ} {α : ℝ} (h : ∀ t, α * f t ≤ Φ t - Φ (t + 1))
    (hΦ : ∀ t, 0 ≤ Φ t) (T : ℕ) : α * ∑ t ∈ range T, f t ≤ Φ 0 := by
  rw [Finset.mul_sum]
  calc ∑ t ∈ range T, α * f t ≤ ∑ t ∈ range T, (Φ t - Φ (t + 1)) := sum_le_sum fun t _ => h t
    _ = Φ 0 - Φ T := sum_range_sub' Φ T
    _ ≤ Φ 0 := by linarith [hΦ T]

/-- `α ∑_{t=1}^{T} min(1, (αt)^{-4}) ≤ 4/3`. -/
theorem sum_min_inv_pow_four_le {α : ℝ} (hα : 0 < α) (T : ℕ) :
    α * ∑ t ∈ range T, min 1 ((α * ((t : ℝ) + 1))⁻¹ ^ 4) ≤ 4 / 3 := by
  let Φ : ℕ → ℝ := fun t => if α * t ≤ 1 then 4 / 3 - α * t else 1 / (3 * (α * t) ^ 3)
  have hΦ0 : Φ 0 = 4 / 3 := by simp [Φ]
  rw [← hΦ0]
  refine telescope_le (fun t => ?_) (fun t => ?_) T
  · set u : ℝ := α * t with hu
    set y : ℝ := α * ((t : ℝ) + 1) with hy
    have hu0 : 0 ≤ u := by positivity
    have hyu : y = u + α := by rw [hy, hu]; ring
    have hy0 : 0 < y := by rw [hyu]; linarith
    have hΦt : Φ t = if u ≤ 1 then 4 / 3 - u else 1 / (3 * u ^ 3) := rfl
    have hΦt1 : Φ (t + 1) = if y ≤ 1 then 4 / 3 - y else 1 / (3 * y ^ 3) := by
      simp only [Φ, hy]; push_cast; rfl
    rw [hΦt, hΦt1]
    split_ifs with hu1 hy1 hy1
    · have : min 1 (y⁻¹ ^ 4) ≤ 1 := min_le_left _ _
      nlinarith
    · have hy1' : 1 < y := not_le.mp hy1
      have hmin : min 1 (y⁻¹ ^ 4) = 1 / y ^ 4 := by
        rw [min_eq_right, inv_pow, one_div]
        rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hy1'.le)
      rw [hmin]
      have key : 4 / 3 - u - 1 / (3 * y ^ 3) - α * (1 / y ^ 4) =
          ((y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) + 3 * (1 - u) * (y ^ 4 - 1)) / (3 * y ^ 4) := by
        rw [hyu]; field_simp; ring
      have hnum : 0 ≤ (y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) + 3 * (1 - u) * (y ^ 4 - 1) := by
        have h1 : 0 ≤ (y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) := by positivity
        have h2 : 1 ≤ y ^ 4 := one_le_pow₀ hy1'.le
        have h3 : 0 ≤ 3 * (1 - u) * (y ^ 4 - 1) := by
          apply mul_nonneg (by linarith) (by linarith)
        linarith
      have : 0 ≤ ((y - 1) ^ 2 * (y ^ 2 + 2 * y + 3) + 3 * (1 - u) * (y ^ 4 - 1)) / (3 * y ^ 4) :=
        div_nonneg hnum (by positivity)
      linarith
    · exfalso; have := not_le.mp hu1; linarith
    · have hu1' : 1 < u := not_le.mp hu1
      have hy1' : 1 < y := not_le.mp hy1
      have hmin : min 1 (y⁻¹ ^ 4) = 1 / y ^ 4 := by
        rw [min_eq_right, inv_pow, one_div]
        rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hy1'.le)
      rw [hmin]
      have hu0' : 0 < u := by linarith
      have key : 1 / (3 * u ^ 3) - 1 / (3 * y ^ 3) - α * (1 / y ^ 4) =
          (y - u) * (y ^ 3 + y ^ 2 * u + y * u ^ 2 - 3 * u ^ 3) / (3 * u ^ 3 * y ^ 4) := by
        rw [hyu]; field_simp; ring
      have hnum : 0 ≤ (y - u) * (y ^ 3 + y ^ 2 * u + y * u ^ 2 - 3 * u ^ 3) := by
        apply mul_nonneg (by linarith)
        have h1 : u ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hu0 (by linarith) 3
        have h2 : u ^ 3 ≤ y ^ 2 * u := by nlinarith
        have h3 : u ^ 3 ≤ y * u ^ 2 := by nlinarith
        linarith
      have : 0 ≤ (y - u) * (y ^ 3 + y ^ 2 * u + y * u ^ 2 - 3 * u ^ 3) / (3 * u ^ 3 * y ^ 4) :=
        div_nonneg hnum (by positivity)
      linarith
  · simp only [Φ]
    split_ifs with h
    · linarith
    · positivity

/-- `α ∑_{t=1}^{T} min(1, (αt)^{-3}) ≤ 3/2`. -/
theorem sum_min_inv_pow_three_le {α : ℝ} (hα : 0 < α) (T : ℕ) :
    α * ∑ t ∈ range T, min 1 ((α * ((t : ℝ) + 1))⁻¹ ^ 3) ≤ 3 / 2 := by
  let Φ : ℕ → ℝ := fun t => if α * t ≤ 1 then 3 / 2 - α * t else 1 / (2 * (α * t) ^ 2)
  have hΦ0 : Φ 0 = 3 / 2 := by simp [Φ]
  rw [← hΦ0]
  refine telescope_le (fun t => ?_) (fun t => ?_) T
  · set u : ℝ := α * t with hu
    set y : ℝ := α * ((t : ℝ) + 1) with hy
    have hu0 : 0 ≤ u := by positivity
    have hyu : y = u + α := by rw [hy, hu]; ring
    have hy0 : 0 < y := by rw [hyu]; linarith
    have hΦt : Φ t = if u ≤ 1 then 3 / 2 - u else 1 / (2 * u ^ 2) := rfl
    have hΦt1 : Φ (t + 1) = if y ≤ 1 then 3 / 2 - y else 1 / (2 * y ^ 2) := by
      simp only [Φ, hy]; push_cast; rfl
    rw [hΦt, hΦt1]
    split_ifs with hu1 hy1 hy1
    · have : min 1 (y⁻¹ ^ 3) ≤ 1 := min_le_left _ _
      nlinarith
    · have hy1' : 1 < y := not_le.mp hy1
      have hmin : min 1 (y⁻¹ ^ 3) = 1 / y ^ 3 := by
        rw [min_eq_right, inv_pow, one_div]
        rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hy1'.le)
      rw [hmin]
      have key : 3 / 2 - u - 1 / (2 * y ^ 2) - α * (1 / y ^ 3) =
          ((y - 1) ^ 2 * (y + 2) + 2 * (1 - u) * (y ^ 3 - 1)) / (2 * y ^ 3) := by
        rw [hyu]; field_simp; ring
      have hnum : 0 ≤ (y - 1) ^ 2 * (y + 2) + 2 * (1 - u) * (y ^ 3 - 1) := by
        have h1 : 0 ≤ (y - 1) ^ 2 * (y + 2) := by positivity
        have h2 : 1 ≤ y ^ 3 := one_le_pow₀ hy1'.le
        have h3 : 0 ≤ 2 * (1 - u) * (y ^ 3 - 1) := by
          apply mul_nonneg (by linarith) (by linarith)
        linarith
      have : 0 ≤ ((y - 1) ^ 2 * (y + 2) + 2 * (1 - u) * (y ^ 3 - 1)) / (2 * y ^ 3) :=
        div_nonneg hnum (by positivity)
      linarith
    · exfalso; have := not_le.mp hu1; linarith
    · have hu1' : 1 < u := not_le.mp hu1
      have hy1' : 1 < y := not_le.mp hy1
      have hmin : min 1 (y⁻¹ ^ 3) = 1 / y ^ 3 := by
        rw [min_eq_right, inv_pow, one_div]
        rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hy1'.le)
      rw [hmin]
      have hu0' : 0 < u := by linarith
      have key : 1 / (2 * u ^ 2) - 1 / (2 * y ^ 2) - α * (1 / y ^ 3) =
          (y - u) ^ 2 * (y + 2 * u) / (2 * u ^ 2 * y ^ 3) := by
        rw [hyu]; field_simp; ring
      have : 0 ≤ (y - u) ^ 2 * (y + 2 * u) / (2 * u ^ 2 * y ^ 3) := by positivity
      linarith
  · simp only [Φ]
    split_ifs with h
    · linarith
    · positivity

/-- Sums over `ℤ` of nonnegative functions vanishing at `0`, from bounds on both half-lines. -/
theorem int_sum_le_of_nat {f : ℤ → ℝ} (hf : ∀ t, 0 ≤ f t) {B₁ B₂ : ℝ}
    (h₁ : ∀ T, ∑ n ∈ range T, f n ≤ B₁) (h₂ : ∀ T, ∑ n ∈ range T, f (-((n : ℤ) + 1)) ≤ B₂) :
    Summable f ∧ ∑' t, f t ≤ B₁ + B₂ := by
  have s₁ : Summable fun n : ℕ => f n := summable_of_sum_range_le (fun n => hf _) h₁
  have s₂ : Summable fun n : ℕ => f (-((n : ℤ) + 1)) := summable_of_sum_range_le (fun n => hf _) h₂
  refine ⟨s₁.of_nat_of_neg_add_one s₂, ?_⟩
  rw [tsum_of_nat_of_neg_add_one s₁ s₂]
  exact add_le_add (Real.tsum_le_of_sum_range_le (fun n => hf _) h₁)
    (Real.tsum_le_of_sum_range_le (fun n => hf _) h₂)

/-- The sinc bound `sb_c(t) = min(1, (πc|t|)^{-4})` (it vanishes at `t = 0`, as `0⁻¹ = 0`). -/
noncomputable def sincBound (c : ℝ) (t : ℤ) : ℝ := min 1 ((π * c * |(t : ℝ)|)⁻¹ ^ 4)

theorem sincBound_nonneg (c : ℝ) (t : ℤ) : 0 ≤ sincBound c t :=
  le_min zero_le_one (by positivity)

theorem sincBound_zero (c : ℝ) : sincBound c 0 = 0 := by simp [sincBound]

theorem sincBound_natCast_succ {c : ℝ} (n : ℕ) :
    sincBound c ((n : ℤ) + 1) = min 1 ((π * c * ((n : ℝ) + 1))⁻¹ ^ 4) := by
  unfold sincBound; push_cast; rw [abs_of_nonneg (by positivity)]

theorem sincBound_neg_succ {c : ℝ} (n : ℕ) :
    sincBound c (-((n : ℤ) + 1)) = min 1 ((π * c * ((n : ℝ) + 1))⁻¹ ^ 4) := by
  unfold sincBound; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]

theorem sum_range_sincBound_le {c : ℝ} (hc : 0 < c) (T : ℕ) :
    ∑ n ∈ range T, sincBound c ((n : ℕ) : ℤ) ≤ 4 / (3 * (π * c)) := by
  have hα : 0 < π * c := mul_pos pi_pos hc
  cases T with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ T =>
    rw [sum_range_succ', Nat.cast_zero, sincBound_zero, add_zero]
    have := sum_min_inv_pow_four_le hα T
    simp only [Nat.cast_add, Nat.cast_one, sincBound_natCast_succ]
    rw [le_div_iff₀ (by positivity)]
    linarith

theorem sum_range_sincBound_neg_le {c : ℝ} (hc : 0 < c) (T : ℕ) :
    ∑ n ∈ range T, sincBound c (-((n : ℤ) + 1)) ≤ 4 / (3 * (π * c)) := by
  have hα : 0 < π * c := mul_pos pi_pos hc
  have := sum_min_inv_pow_four_le hα T
  simp only [sincBound_neg_succ]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `∑_{t ∈ ℤ} sb_c(t) ≤ 8/(3πc)`. -/
theorem summable_sincBound {c : ℝ} (hc : 0 < c) :
    Summable (sincBound c) ∧ ∑' t, sincBound c t ≤ 8 / (3 * (π * c)) := by
  have h := int_sum_le_of_nat (sincBound_nonneg c) (sum_range_sincBound_le hc)
    (sum_range_sincBound_neg_le hc)
  refine ⟨h.1, le_trans h.2 (le_of_eq ?_)⟩
  ring

/-- `|t| sb_c(t) ≤ (πc)^{-1} min(1, (πc|t|)^{-3})`. -/
theorem abs_mul_sincBound_le {c : ℝ} (hc : 0 < c) (t : ℤ) :
    |(t : ℝ)| * sincBound c t ≤ (π * c)⁻¹ * min 1 ((π * c * |(t : ℝ)|)⁻¹ ^ 3) := by
  have hα : 0 < π * c := mul_pos pi_pos hc
  set y := π * c * |(t : ℝ)| with hy
  have hy0 : 0 ≤ y := by positivity
  have ht : |(t : ℝ)| = (π * c)⁻¹ * y := by rw [hy]; field_simp
  unfold sincBound
  rw [← hy, ht, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_or_gt y 1 with hy1 | hy1
  · calc y * min 1 (y⁻¹ ^ 4) ≤ y * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hy0
      _ ≤ min 1 (y⁻¹ ^ 3) := by
        rw [mul_one]
        apply le_min hy1
        rcases eq_or_lt_of_le hy0 with h0 | h0
        · rw [← h0]; simp
        · have : 1 ≤ y⁻¹ := one_le_inv_iff₀.mpr ⟨h0, hy1⟩
          calc y ≤ 1 := hy1
            _ ≤ y⁻¹ ^ 3 := one_le_pow₀ this
  · have hy0' : 0 < y := by linarith
    have h4 : y⁻¹ ^ 4 ≤ 1 := by rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hy1.le)
    have h3 : y⁻¹ ^ 3 ≤ 1 := by rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hy1.le)
    rw [min_eq_right h4, min_eq_right h3]
    rw [inv_pow, inv_pow]
    field_simp
    rfl

/-- `∑_{t ∈ ℤ} |t| sb_c(t) ≤ 3/(πc)²`. -/
theorem summable_abs_mul_sincBound {c : ℝ} (hc : 0 < c) :
    Summable (fun t : ℤ => |(t : ℝ)| * sincBound c t) ∧
      ∑' t : ℤ, |(t : ℝ)| * sincBound c t ≤ 3 / (π * c) ^ 2 := by
  have hα : 0 < π * c := mul_pos pi_pos hc
  have hnn : ∀ t : ℤ, 0 ≤ |(t : ℝ)| * sincBound c t :=
    fun t => mul_nonneg (abs_nonneg _) (sincBound_nonneg c t)
  have h3 := sum_min_inv_pow_three_le hα
  have h₁ : ∀ T, ∑ n ∈ range T, |((n : ℤ) : ℝ)| * sincBound c (n : ℤ) ≤ (π * c)⁻¹ * (3 / 2 / (π * c)) := by
    intro T
    cases T with
    | zero => simp only [range_zero, sum_empty]; positivity
    | succ T =>
      rw [sum_range_succ']
      simp only [Nat.cast_zero, Int.cast_zero, abs_zero, zero_mul, add_zero]
      calc ∑ n ∈ range T, |(((n + 1 : ℕ) : ℤ) : ℝ)| * sincBound c ((n + 1 : ℕ) : ℤ)
          ≤ ∑ n ∈ range T, (π * c)⁻¹ * min 1 ((π * c * ((n : ℝ) + 1))⁻¹ ^ 3) := by
            refine sum_le_sum fun n _ => ?_
            have := abs_mul_sincBound_le hc ((n + 1 : ℕ) : ℤ)
            push_cast at this ⊢
            rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] at this ⊢
        _ ≤ (π * c)⁻¹ * (3 / 2 / (π * c)) := by
            rw [← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [le_div_iff₀ hα]; linarith [h3 T]
  have h₂ : ∀ T, ∑ n ∈ range T, |((-((n : ℤ) + 1) : ℤ) : ℝ)| * sincBound c (-((n : ℤ) + 1)) ≤
      (π * c)⁻¹ * (3 / 2 / (π * c)) := by
    intro T
    calc ∑ n ∈ range T, |((-((n : ℤ) + 1) : ℤ) : ℝ)| * sincBound c (-((n : ℤ) + 1))
        ≤ ∑ n ∈ range T, (π * c)⁻¹ * min 1 ((π * c * ((n : ℝ) + 1))⁻¹ ^ 3) := by
          refine sum_le_sum fun n _ => ?_
          have := abs_mul_sincBound_le hc (-((n : ℤ) + 1))
          push_cast at this ⊢
          rwa [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] at this ⊢
      _ ≤ (π * c)⁻¹ * (3 / 2 / (π * c)) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ hα]; linarith [h3 T]
  have h := int_sum_le_of_nat hnn h₁ h₂
  refine ⟨h.1, le_trans h.2 (le_of_eq ?_)⟩
  field_simp
  ring

/-! ### Arithmetic of `κ_a` -/

/-- `ρ(k) = (m - k - j₀) mod (a + 1)`. -/
def rhoK (m a k : ℕ) : ℕ := (m - k - jZero m) % (a + 1)

/-- `ℓ_k = ⌊(m - k - j₀ + 1)/(a + 1)⌋`, so that `n_{κ_a(k)} = (a + 1) ℓ_k`. -/
def ellK (m a k : ℕ) : ℕ := (m - k - jZero m + 1) / (a + 1)

/-- `D(k) = κ_a(k) - k` as a function of `ρ`. -/
def dRho (m a ρ : ℕ) : ℕ := jZero m + (ρ + 1) % (a + 1)

theorem cancellerBelow_eq (m a k : ℕ) : cancellerBelow m a k = k + dRho m a (rhoK m a k) := by
  unfold cancellerBelow rhoK dRho jZero
  simp only [Nat.sub_sub]
  ring

theorem nKappa_eq {m a k : ℕ} (hfit : k + jZero m + a ≤ m) :
    m - cancellerBelow m a k + 1 = (a + 1) * ellK m a k := by
  rw [cancellerBelow_eq]
  unfold ellK dRho rhoK
  set x := m - k - jZero m with hx
  have hdiv := Nat.div_add_mod x (a + 1)
  have hlt := Nat.mod_lt x (Nat.succ_pos a)
  set q := x / (a + 1) with hq
  set r := x % (a + 1) with hr
  rcases Nat.lt_or_ge (r + 1) (a + 1) with h | h
  · rw [Nat.mod_eq_of_lt h]
    have e : x + 1 = (r + 1) + (a + 1) * q := by omega
    rw [e, Nat.add_mul_div_left _ _ (Nat.succ_pos a), Nat.div_eq_of_lt h, zero_add]
    omega
  · have hra : r = a := by omega
    rw [hra, Nat.mod_self]
    have e : x + 1 = (a + 1) * (q + 1) := by rw [mul_add, mul_one]; omega
    rw [e, Nat.mul_div_cancel_left _ (Nat.succ_pos a)]
    omega

theorem rho_ell_injective {m a k₁ k₂ : ℕ} (h₁ : k₁ + jZero m ≤ m) (h₂ : k₂ + jZero m ≤ m)
    (hρ : rhoK m a k₁ = rhoK m a k₂) (hℓ : ellK m a k₁ = ellK m a k₂) : k₁ = k₂ := by
  unfold rhoK at hρ
  unfold ellK at hℓ
  have e₁ := Nat.div_add_mod (m - k₁ - jZero m + 1) (a + 1)
  have e₂ := Nat.div_add_mod (m - k₂ - jZero m + 1) (a + 1)
  have m₁ : (m - k₁ - jZero m + 1) % (a + 1) = ((m - k₁ - jZero m) % (a + 1) + 1) % (a + 1) := by
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have m₂ : (m - k₂ - jZero m + 1) % (a + 1) = ((m - k₂ - jZero m) % (a + 1) + 1) % (a + 1) := by
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [hℓ, m₁, hρ] at e₁
  rw [m₂] at e₂
  omega

theorem ellK_antitone {m a k k' : ℕ} (h : k ≤ k') : ellK m a k' ≤ ellK m a k := by
  unfold ellK
  exact Nat.div_le_div_right (by omega)

/-- The `ℓ_k`, `k ∈ 𝒦 = [1, K]`, lie in `[ℓ_K, ℓ_1]`, an interval of `Λ` integers with
`(a + 1) Λ ≤ K + 2a`. -/
theorem ell_range_card {m a K : ℕ} (hK : 1 ≤ K) (hfit : K + jZero m ≤ m) :
    (a + 1) * (ellK m a 1 + 1 - ellK m a K) ≤ K + 2 * a := by
  have h1 := Nat.div_mul_le_self (m - 1 - jZero m + 1) (a + 1)
  have h2 := Nat.lt_div_mul_add (a := m - K - jZero m + 1) (Nat.succ_pos a)
  have hmono : ellK m a K ≤ ellK m a 1 := ellK_antitone hK
  unfold ellK at hmono ⊢
  set A := (m - 1 - jZero m + 1) / (a + 1)
  set B := (m - K - jZero m + 1) / (a + 1)
  have : (a + 1) * (A + 1 - B) = (a + 1) * A + (a + 1) - (a + 1) * B := by
    rw [Nat.mul_sub, mul_add, mul_one]
  rw [this]
  have hA : (a + 1) * A ≤ m - 1 - jZero m + 1 := by rw [mul_comm]; exact h1
  have hB : m - K - jZero m + 1 < (a + 1) * B + (a + 1) := by rw [mul_comm]; exact h2
  omega

/-! ### Lemma 7.14 applied to the products of `F(n, D)` -/

theorem int_two_pow_mul_odd {t : ℤ} (ht : t ≠ 0) : ∃ v : ℕ, ∃ t' : ℤ, Odd t' ∧ t = 2 ^ v * t' := by
  obtain ⟨v, n, hn, hneq⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr ht)
  have hn' : Odd (n : ℤ) := (Int.odd_coe_nat n).mpr hn
  rcases Int.natAbs_eq t with h | h
  · exact ⟨v, n, hn', by rw [h, hneq]; push_cast; ring⟩
  · exact ⟨v, -n, hn'.neg, by rw [h, hneq]; push_cast; ring⟩

theorem two_pow_le_abs {v : ℕ} {t t' : ℤ} (ht' : Odd t') (ht : t = 2 ^ v * t') :
    (2 : ℝ) ^ v ≤ |(t : ℝ)| := by
  have ht0 : t' ≠ 0 := by rintro rfl; exact absurd ht' (by decide)
  have h1 : (1 : ℝ) ≤ |(t' : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ht0
  rw [ht]; push_cast
  rw [abs_mul, abs_of_pos (by positivity)]
  have : (0 : ℝ) < 2 ^ v := by positivity
  nlinarith

/-- Lemma 7.14(b) with the progression written as `ℓ₀ + i`, `i < L`. -/
theorem progression_sum_le_range {a w o v j L : ℕ} {t t' : ℤ} (ho : Odd o)
    (hao : a + 1 = 2 ^ w * o) (ht' : Odd t') (ht : t = 2 ^ v * t') (c : ℕ → ℝ) (ℓ₀ : ℤ) :
    2 ^ j * ∑ i ∈ range L, ∏ e ∈ Ioc (v + w) (v + w + j),
      cos (π * t * ((a + 1) * ((ℓ₀ : ℝ) + i) + c e) / 2 ^ e) ^ 2 ≤ L + 2 ^ j - 1 := by
  have h := progression_sum_le (L := L) (j := j) ho hao ht' ht c ℓ₀
  rw [sum_Ico_int_eq_sum_range] at h
  simpa only [Int.cast_add, Int.cast_natCast] using h

/-- The cosine product `∏_{e=1}^{D} cos²(π t (n + D + 1 - e) 2^{-e})` of `F(n, D)`. -/
noncomputable def cosProd (n D : ℕ) (t : ℤ) : ℝ :=
  ∏ e ∈ Icc 1 D, Real.cos (π * t * (n + D + 1 - e : ℕ) / 2 ^ e) ^ 2

theorem cosProd_nonneg (n D : ℕ) (t : ℤ) : 0 ≤ cosProd n D t := prod_cos_sq_nonneg _ _

theorem cosProd_le_one (n D : ℕ) (t : ℤ) : cosProd n D t ≤ 1 := prod_cos_sq_le_one _ _

/-- **Lemma 7.14 for `F(n, D)`**: with `a + 1 = 2^w o` (`o` odd) and `t ≠ 0`, the sum of the cosine
products of `F((a + 1)ℓ, D)` over `Λ` consecutive `ℓ` is at most `Λ |t| 2^w / 2^D + 1`. -/
theorem sum_cosProd_le {a w o D : ℕ} (ho : Odd o) (hao : a + 1 = 2 ^ w * o) {t : ℤ} (ht : t ≠ 0)
    (ℓ₀ Λ : ℕ) :
    ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤ Λ * |(t : ℝ)| * 2 ^ w / 2 ^ D + 1 := by
  obtain ⟨v, t', ht', htv⟩ := int_two_pow_mul_odd ht
  have hv := two_pow_le_abs ht' htv
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg _
  rcases lt_or_ge (v + w) D with hvw | hvw
  · obtain ⟨j, hj⟩ : ∃ j, D = v + w + j := ⟨D - (v + w), by omega⟩
    have key := progression_sum_le_range (L := Λ) (j := j) ho hao ht' htv
      (fun e => (D : ℝ) + 1 - e) (ℓ₀ : ℤ)
    have hle : ∀ i : ℕ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤
        ∏ e ∈ Ioc (v + w) (v + w + j), cos (π * t * ((a + 1) * ((((ℓ₀ : ℤ)) : ℝ) + i) +
          ((D : ℝ) + 1 - e)) / 2 ^ e) ^ 2 := by
      intro i
      unfold cosProd
      have hsub : Ioc (v + w) (v + w + j) ⊆ Icc 1 D := by
        intro x; simp only [mem_Ioc, mem_Icc]; omega
      rw [← prod_sdiff hsub]
      refine le_trans (mul_le_of_le_one_left (prod_cos_sq_nonneg _ _) (prod_cos_sq_le_one _ _))
        (le_of_eq ?_)
      refine prod_congr rfl fun e he => ?_
      have he' := mem_Ioc.mp he
      congr 4
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hsum : ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤ (Λ + 2 ^ j - 1) / 2 ^ j := by
      rw [le_div_iff₀ hp, mul_comm]
      exact le_trans (mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hle i) hp.le) key
    have h1 : ((Λ : ℝ) + 2 ^ j - 1) / 2 ^ j ≤ Λ / 2 ^ j + 1 := by
      rw [div_add_one hp.ne']
      exact div_le_div_of_nonneg_right (by linarith) hp.le
    have h2 : (Λ : ℝ) / 2 ^ j ≤ Λ * |(t : ℝ)| * 2 ^ w / 2 ^ D := by
      rw [hj, pow_add, pow_add, div_le_div_iff₀ hp (by positivity)]
      have hw : (0 : ℝ) < 2 ^ w := by positivity
      have : (Λ : ℝ) * 2 ^ v * 2 ^ w * 2 ^ j ≤ Λ * |(t : ℝ)| * 2 ^ w * 2 ^ j := by
        have := mul_le_mul_of_nonneg_left hv hΛ0
        have h3 := mul_le_mul_of_nonneg_right this (le_of_lt (mul_pos hw hp))
        nlinarith
      nlinarith
    linarith
  · have hsum : ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤ Λ := by
      calc ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤ ∑ i ∈ range Λ, (1 : ℝ) :=
            sum_le_sum fun i _ => cosProd_le_one _ _ _
        _ = Λ := by simp
    have h2 : (2 : ℝ) ^ D ≤ 2 ^ v * 2 ^ w := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hvw
    have : (Λ : ℝ) ≤ Λ * |(t : ℝ)| * 2 ^ w / 2 ^ D := by
      rw [le_div_iff₀ (by positivity)]
      have hw : (0 : ℝ) ≤ 2 ^ w := by positivity
      have h4 : (2 : ℝ) ^ v * 2 ^ w ≤ |(t : ℝ)| * 2 ^ w := mul_le_mul_of_nonneg_right hv hw
      have h5 := mul_le_mul_of_nonneg_left (le_trans h2 h4) hΛ0
      nlinarith
    linarith

/-! ### Proposition 7.15(a): the fine floors -/

/-- `sinc(x)⁴ ≤ sb_c(t)` whenever `t ≠ 0` and `π c |t| ≤ |x|`. -/
theorem sinc_pow_four_le_sincBound {c x : ℝ} (hc : 0 < c) {t : ℤ} (ht : t ≠ 0)
    (hx : π * c * |(t : ℝ)| ≤ |x|) : Real.sinc x ^ 4 ≤ sincBound c t := by
  have ht' : (0 : ℝ) < |(t : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr ht)
  have hy : 0 < π * c * |(t : ℝ)| := by positivity
  have hx0 : 0 < |x| := lt_of_lt_of_le hy hx
  have h1 : |Real.sinc x| ≤ 1 := Real.abs_sinc_le_one x
  have h2 : |Real.sinc x| ≤ |x|⁻¹ := by
    rw [Real.sinc_of_ne_zero (abs_pos.mp hx0), abs_div, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg _)) (abs_sin_le_one x)
  have h3 : |x|⁻¹ ≤ (π * c * |(t : ℝ)|)⁻¹ := inv_anti₀ hy hx
  rw [← Even.pow_abs (by decide : Even 4)]
  unfold sincBound
  apply le_min
  · exact pow_le_one₀ (abs_nonneg _) h1
  · exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h2 h3) 4

/-- The majorant `∑_{t} sb_c(t) ∏_{e=1}^{D} cos²(π t (n + D + 1 - e) 2^{-e})` of `F(n, D)`. -/
noncomputable def fineMajorant (c : ℝ) (n D : ℕ) : ℝ := ∑' t : ℤ, sincBound c t * cosProd n D t

theorem summable_majorant_terms {c : ℝ} (hc : 0 < c) (n D : ℕ) :
    Summable (fun t : ℤ => sincBound c t * cosProd n D t) :=
  Summable.of_nonneg_of_le (fun t => mul_nonneg (sincBound_nonneg c t) (cosProd_nonneg n D t))
    (fun t => mul_le_of_le_one_right (sincBound_nonneg c t) (cosProd_le_one n D t))
    (summable_sincBound hc).1

/-- `F(n, D) ≤ fineMajorant c n D` when `c 2^{D+2} ≤ n`. -/
theorem fineFloor_le_majorant {c : ℝ} (hc : 0 < c) {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hcn : c * 2 ^ (D + 2) ≤ n) : fineFloor n D ≤ fineMajorant c n D := by
  unfold fineFloor fineMajorant
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_fineFloorTerm hn hD)
    (summable_majorant_terms hc n D)
  split_ifs with ht
  · exact mul_nonneg (sincBound_nonneg c t) (cosProd_nonneg n D t)
  · unfold fineFloorTerm
    apply mul_le_mul_of_nonneg_right _ (cosProd_nonneg n D t)
    apply sinc_pow_four_le_sincBound hc ht
    rw [abs_mul, abs_of_pos pi_pos, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (D + 2)),
      Nat.abs_cast, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ |(t : ℝ)| := abs_nonneg _
    nlinarith

/-- Summing the majorant over `Λ` consecutive `ℓ`, with Lemma 7.14 for each frequency. -/
theorem sum_majorant_le {a w o D : ℕ} (ho : Odd o) (hao : a + 1 = 2 ^ w * o) {c : ℝ} (hc : 0 < c)
    (ℓ₀ Λ : ℕ) :
    ∑ i ∈ range Λ, fineMajorant c ((a + 1) * (ℓ₀ + i)) D ≤
      Λ * 2 ^ w / 2 ^ D * (3 / (π * c) ^ 2) + 8 / (3 * (π * c)) := by
  unfold fineMajorant
  rw [← Summable.tsum_finsetSum (fun i _ => summable_majorant_terms hc _ D)]
  simp_rw [← Finset.mul_sum]
  have hs1 := summable_abs_mul_sincBound hc
  have hs0 := summable_sincBound hc
  have hcoef : (0 : ℝ) ≤ Λ * 2 ^ w / 2 ^ D := by positivity
  calc ∑' t : ℤ, sincBound c t * ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t
      ≤ ∑' t : ℤ, (Λ * 2 ^ w / 2 ^ D * (|(t : ℝ)| * sincBound c t) + sincBound c t) := by
        refine Summable.tsum_le_tsum (fun t => ?_) ?_ ((hs1.1.mul_left _).add hs0.1)
        · by_cases ht : t = 0
          · subst ht; simp [sincBound_zero]
          · have h := sum_cosProd_le ho hao ht ℓ₀ Λ (D := D)
            have h0 := sincBound_nonneg c t
            calc sincBound c t * ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t
                ≤ sincBound c t * (Λ * |(t : ℝ)| * 2 ^ w / 2 ^ D + 1) :=
                  mul_le_mul_of_nonneg_left h h0
              _ = _ := by ring
        · refine Summable.of_nonneg_of_le (fun t => mul_nonneg (sincBound_nonneg c t)
            (sum_nonneg fun i _ => cosProd_nonneg _ _ _)) (fun t => ?_) (hs0.1.mul_left (Λ : ℝ))
          have hsum : ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤ Λ := by
            calc ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t ≤ ∑ i ∈ range Λ, (1 : ℝ) :=
                  sum_le_sum fun i _ => cosProd_le_one _ _ _
              _ = Λ := by simp
          calc sincBound c t * ∑ i ∈ range Λ, cosProd ((a + 1) * (ℓ₀ + i)) D t
              ≤ sincBound c t * Λ := mul_le_mul_of_nonneg_left hsum (sincBound_nonneg c t)
            _ = Λ * sincBound c t := mul_comm _ _
    _ = Λ * 2 ^ w / 2 ^ D * ∑' t : ℤ, |(t : ℝ)| * sincBound c t + ∑' t : ℤ, sincBound c t := by
        rw [Summable.tsum_add (hs1.1.mul_left _) hs0.1, tsum_mul_left]
    _ ≤ Λ * 2 ^ w / 2 ^ D * (3 / (π * c) ^ 2) + 8 / (3 * (π * c)) := by
        gcongr
        · exact hs1.2
        · exact hs0.2

/-- Facts about `κ = κ_a(k)` for `k ∈ 𝒦` under the size condition `4(j₀ + a) ≤ N`. -/
theorem coarse_facts {m a k : ℕ} (ha : 1 ≤ a) (hsize : 4 * (jZero m + a) ≤ m + 1)
    (hk : k ∈ coarseZone m) :
    1 ≤ k ∧ k + jZero m + a ≤ m ∧ k < cancellerBelow m a k ∧ cancellerBelow m a k ≤ m ∧
      m + 1 ≤ 2 * (m - cancellerBelow m a k + 1) := by
  unfold coarseZone at hk
  rw [mem_Icc] at hk
  have hfit : k + (Nat.log 2 (m + 1) + 1) + a ≤ m := by unfold jZero at hsize; omega
  have hcoarse : 2 * (k + (Nat.log 2 (m + 1) + 1) + a) ≤ m + 1 := by unfold jZero at hsize; omega
  obtain ⟨_, h2, _, _, _, h6⟩ := cancellerBelow_props (s0 := m) ha le_rfl hk.1 hfit hcoarse
  refine ⟨hk.1, by unfold jZero; omega, ?_, h2, h6⟩
  rw [cancellerBelow_eq]; unfold dRho jZero; omega

theorem dRho_le (m a ρ : ℕ) : dRho m a ρ ≤ jZero m + a := by
  unfold dRho; have := Nat.mod_lt (ρ + 1) (by omega : 0 < a + 1); omega

theorem jZero_le_dRho (m a ρ : ℕ) : jZero m ≤ dRho m a ρ := by unfold dRho; omega

theorem lt_two_pow_jZero (m : ℕ) : m + 1 < 2 ^ jZero m :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m + 1)

theorem two_pow_jZero_le (m : ℕ) : 2 ^ jZero m ≤ 2 * (m + 1) := by
  unfold jZero
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (by omega : m + 1 ≠ 0)
  omega

/-- **Proposition 7.15(a).** Under the size condition `4(j₀ + a) ≤ N`,
`∑_{k ∈ 𝒦} F_k ≤ (a + 1) (3 (2^{a+4}/π)² + 8 · 2^{a+4}/(3π))`; so the average of `F_k` over `𝒦`
is `O_a(1/N)`. -/
theorem sum_fineFloorK_le {m a : ℕ} (ha : 1 ≤ a) (hsize : 4 * (jZero m + a) ≤ m + 1) :
    ∑ k ∈ coarseZone m, fineFloorK m k (cancellerBelow m a k) ≤
      (a + 1) * (3 * (2 ^ (a + 4) / π) ^ 2 + 8 * 2 ^ (a + 4) / (3 * π)) := by
  set c : ℝ := 1 / 2 ^ (a + 4) with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨w, o, ho, hao⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : a + 1 ≠ 0)
  have hw : 2 ^ w ≤ a + 1 := by
    rw [hao]; exact Nat.le_mul_of_pos_right _ ho.pos
  set K := (m + 1) / 4 with hK
  have hK1 : 1 ≤ K := by unfold jZero at hsize; omega
  have hKfit : K + jZero m ≤ m := by unfold jZero at hsize ⊢; omega
  set ℓlo := ellK m a K with hℓlo
  set Λ := ellK m a 1 + 1 - ℓlo with hΛ
  -- Step A: each fine floor is at most the majorant at its `ℓ_k`
  have hA : ∀ k ∈ coarseZone m, fineFloorK m k (cancellerBelow m a k) ≤
      fineMajorant c ((a + 1) * ellK m a k) (dRho m a (rhoK m a k)) := by
    intro k hk
    obtain ⟨hk1, hfit, hkκ, hκm, hhalf⟩ := coarse_facts ha hsize hk
    have hn := nKappa_eq hfit
    rw [fineFloorK_eq hk1 hkκ hκm, hn]
    have hD : cancellerBelow m a k - k = dRho m a (rhoK m a k) := by rw [cancellerBelow_eq]; omega
    rw [hD]
    apply fineFloor_le_majorant hc
    · omega
    · unfold dRho jZero; omega
    · have hnat : 2 ^ dRho m a (rhoK m a k) ≤ 2 ^ (a + 2) * ((a + 1) * ellK m a k) := by
        have h1 : 2 ^ dRho m a (rhoK m a k) ≤ 2 ^ (jZero m + a) :=
          Nat.pow_le_pow_right (by norm_num) (dRho_le m a _)
        have h2 := two_pow_jZero_le m
        rw [pow_add] at h1
        rw [pow_add]
        have h3 : 2 ^ jZero m * 2 ^ a ≤ 2 * (m + 1) * 2 ^ a := Nat.mul_le_mul_right _ h2
        have h4 : 2 * (m + 1) * 2 ^ a ≤ 2 * (2 * ((a + 1) * ellK m a k)) * 2 ^ a :=
          Nat.mul_le_mul_right _ (by omega)
        calc 2 ^ dRho m a (rhoK m a k) ≤ 2 ^ jZero m * 2 ^ a := h1
          _ ≤ 2 * (2 * ((a + 1) * ellK m a k)) * 2 ^ a := le_trans h3 h4
          _ = 2 ^ a * 2 ^ 2 * ((a + 1) * ellK m a k) := by ring
      have hreal : (2 : ℝ) ^ dRho m a (rhoK m a k) ≤ 2 ^ (a + 2) * (((a + 1) * ellK m a k : ℕ) : ℝ) := by
        exact_mod_cast hnat
      rw [hcdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity),
        show a + 4 = (a + 2) + 2 by ring, pow_add, pow_add]
      nlinarith
  -- Step B: pass to all pairs `(ρ, ℓ)` with `ρ ≤ a` and `ℓ ∈ [ℓ_K, ℓ_1]`
  have hG0 : ∀ n D, 0 ≤ fineMajorant c n D := fun n D =>
    tsum_nonneg fun t => mul_nonneg (sincBound_nonneg c t) (cosProd_nonneg _ _ _)
  have hB : ∑ k ∈ coarseZone m, fineMajorant c ((a + 1) * ellK m a k) (dRho m a (rhoK m a k)) ≤
      ∑ ρ ∈ range (a + 1), ∑ i ∈ range Λ, fineMajorant c ((a + 1) * (ℓlo + i)) (dRho m a ρ) := by
    set f : ℕ → ℕ × ℕ := fun k => (rhoK m a k, ellK m a k) with hf
    set G : ℕ × ℕ → ℝ := fun p => fineMajorant c ((a + 1) * p.2) (dRho m a p.1) with hG
    have hinj : ∀ x ∈ coarseZone m, ∀ y ∈ coarseZone m, f x = f y → x = y := by
      intro x hx y hy hxy
      simp only [f, Prod.mk.injEq] at hxy
      have hx' := coarse_facts ha hsize hx
      have hy' := coarse_facts ha hsize hy
      exact rho_ell_injective (by omega) (by omega) hxy.1 hxy.2
    have hsub : (coarseZone m).image f ⊆ range (a + 1) ×ˢ Icc ℓlo (ellK m a 1) := by
      intro p hp
      rw [mem_image] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      rw [mem_product, mem_range, mem_Icc]
      have hk' := mem_Icc.mp hk
      exact ⟨Nat.mod_lt _ (Nat.succ_pos a), ellK_antitone hk'.2, ellK_antitone hk'.1⟩
    calc ∑ k ∈ coarseZone m, fineMajorant c ((a + 1) * ellK m a k) (dRho m a (rhoK m a k))
        = ∑ p ∈ (coarseZone m).image f, G p := by rw [sum_image hinj]
      _ ≤ ∑ p ∈ range (a + 1) ×ˢ Icc ℓlo (ellK m a 1), G p :=
          sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hG0 _ _)
      _ = ∑ ρ ∈ range (a + 1), ∑ ℓ ∈ Icc ℓlo (ellK m a 1), G (ρ, ℓ) := sum_product _ _ _
      _ = ∑ ρ ∈ range (a + 1), ∑ i ∈ range Λ, fineMajorant c ((a + 1) * (ℓlo + i)) (dRho m a ρ) := by
          refine sum_congr rfl fun ρ _ => ?_
          rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  -- Step C: each residue class
  have hΛw : (Λ : ℝ) * 2 ^ w ≤ (m : ℝ) + 1 := by
    have h1 : (a + 1) * Λ ≤ K + 2 * a := ell_range_card (a := a) hK1 hKfit
    have h2 : Λ * 2 ^ w ≤ (a + 1) * Λ := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hw
    have h3 : K + 2 * a ≤ m + 1 := by unfold jZero at hsize; omega
    have : Λ * 2 ^ w ≤ m + 1 := by omega
    exact_mod_cast this
  have hC : ∀ ρ ∈ range (a + 1),
      ∑ i ∈ range Λ, fineMajorant c ((a + 1) * (ℓlo + i)) (dRho m a ρ) ≤
        3 / (π * c) ^ 2 + 8 / (3 * (π * c)) := by
    intro ρ _
    have h := sum_majorant_le (D := dRho m a ρ) ho hao hc ℓlo Λ
    have hD : ((m : ℝ) + 1) ≤ 2 ^ dRho m a ρ := by
      have h1 := lt_two_pow_jZero m
      have h2 : 2 ^ jZero m ≤ 2 ^ dRho m a ρ := Nat.pow_le_pow_right (by norm_num) (jZero_le_dRho m a ρ)
      exact_mod_cast (by omega : m + 1 ≤ 2 ^ dRho m a ρ)
    have hratio : (Λ : ℝ) * 2 ^ w / 2 ^ dRho m a ρ ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h3 : (0 : ℝ) ≤ 3 / (π * c) ^ 2 := by positivity
    calc ∑ i ∈ range Λ, fineMajorant c ((a + 1) * (ℓlo + i)) (dRho m a ρ)
        ≤ Λ * 2 ^ w / 2 ^ dRho m a ρ * (3 / (π * c) ^ 2) + 8 / (3 * (π * c)) := h
      _ ≤ 1 * (3 / (π * c) ^ 2) + 8 / (3 * (π * c)) := by gcongr
      _ = 3 / (π * c) ^ 2 + 8 / (3 * (π * c)) := by ring
  calc ∑ k ∈ coarseZone m, fineFloorK m k (cancellerBelow m a k)
      ≤ ∑ k ∈ coarseZone m, fineMajorant c ((a + 1) * ellK m a k) (dRho m a (rhoK m a k)) :=
        sum_le_sum hA
    _ ≤ ∑ ρ ∈ range (a + 1), ∑ i ∈ range Λ, fineMajorant c ((a + 1) * (ℓlo + i)) (dRho m a ρ) := hB
    _ ≤ ∑ ρ ∈ range (a + 1), (3 / (π * c) ^ 2 + 8 / (3 * (π * c))) := sum_le_sum hC
    _ = (a + 1) * (3 * (2 ^ (a + 4) / π) ^ 2 + 8 * 2 ^ (a + 4) / (3 * π)) := by
        rw [sum_const, card_range, nsmul_eq_mul, hcdef]
        push_cast
        field_simp

/-! ### Proposition 7.15(b): near semi-local frequencies -/

/-- `SL^{[h]}_k = ∑_{s odd} φ_k(N 2^{k-h} s)`. -/
noncomputable def semiLocal (m k κ h : ℕ) : ℝ :=
  ∑' s : ℤ, if Odd s then straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - h) * s) else 0

theorem summable_semiLocal {m k κ h : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    Summable (fun s : ℤ => if Odd s then straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - h) * s) else 0) := by
  set g : ℤ → ℝ := fun r => if r = 0 then 0 else straddlePhi m k κ r with hg
  have hgs : Summable g := (hasSum_straddlePhi_ne_zero (m := m) hk hkκ).summable
  have hinj : Function.Injective (fun s : ℤ => ((m : ℤ) + 1) * 2 ^ (k - h) * s) := by
    intro x y hxy
    exact mul_left_cancel₀ (by positivity : ((m : ℤ) + 1) * 2 ^ (k - h) ≠ 0) hxy
  refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) (hgs.comp_injective hinj)
  · split_ifs
    · exact straddlePhi_nonneg hk hkκ _
    · exact le_rfl
  · simp only [Function.comp, g]
    split_ifs with h1 h2
    · exfalso
      have : s ≠ 0 := by rintro rfl; exact absurd h1 (by decide)
      exact mul_ne_zero (by positivity : ((m : ℤ) + 1) * 2 ^ (k - h) ≠ 0) this h2
    · exact le_rfl
    · exact le_rfl
    · exact straddlePhi_nonneg hk hkκ _

theorem semiLocal_nonneg {m k κ h : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) : 0 ≤ semiLocal m k κ h :=
  tsum_nonneg fun s => by
    split_ifs
    · exact straddlePhi_nonneg hk hkκ _
    · exact le_rfl

/-- The cosine product `∏_{l ∈ (w, E]} cos²(π s (n + E + 1 - l) 2^{-l})` kept for `SL^{[h]}_k`. -/
noncomputable def slProd (n E w : ℕ) (s : ℤ) : ℝ :=
  ∏ l ∈ Ioc w E, Real.cos (π * s * (n + E + 1 - l : ℕ) / 2 ^ l) ^ 2

theorem slProd_nonneg (n E w : ℕ) (s : ℤ) : 0 ≤ slProd n E w s := prod_cos_sq_nonneg _ _

theorem slProd_le_one (n E w : ℕ) (s : ℤ) : slProd n E w s ≤ 1 := prod_cos_sq_le_one _ _

/-- The majorant of one semi-local term: for `s` odd and `2 ≤ h ≤ k < κ ≤ m`, with
`c 2^{κ-k+h+1} ≤ n_κ`, `φ_k(N 2^{k-h} s) ≤ sb_c(s) ∏_{l ∈ (w, κ-k+h-1]} cos²(π s m_l 2^{-l})`. -/
theorem straddlePhi_semiLocal_le {m k κ h w : ℕ} (hk : 1 ≤ k) (hkκ : k < κ) (hκm : κ ≤ m)
    (hh : h ≤ k) {c : ℝ} (hc : 0 < c)
    (hcn : c * 2 ^ (κ - k + h + 1) ≤ ((m - κ + 1 : ℕ) : ℝ)) {s : ℤ} (hs : s ≠ 0) :
    straddlePhi m k κ (((m : ℤ) + 1) * 2 ^ (k - h) * s) ≤
      sincBound c s * slProd (m - κ + 1) (κ - k + h - 1) w s := by
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set r : ℤ := ((m : ℤ) + 1) * 2 ^ (k - h) * s with hr
  set E := κ - k + h - 1 with hE
  rw [← phiGen_eq_straddlePhi hk hkκ.le]
  unfold phiGen
  set S4 := Real.sinc (π * r * piHat m κ / (2 * ((m : ℝ) + 1))) ^ 4 with hS4
  have hS40 : 0 ≤ S4 := by positivity
  have hP1 : ∏ i ∈ Icc 1 (k - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 ≤ 1 :=
    prod_cos_sq_le_one _ _
  have hP20 : 0 ≤ ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 :=
    prod_cos_sq_nonneg _ _
  -- keep only the indices `i = k - h + l`, `l ∈ (w, E]`
  have hsub : (Ioc w E).map (addLeftEmbedding (k - h)) ⊆ Icc 1 (κ - 1) := by
    intro x hx
    simp only [mem_map, mem_Ioc, addLeftEmbedding_apply] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    rw [mem_Icc]; omega
  have hP2 : ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 ≤
      slProd (m - κ + 1) E w s := by
    calc ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2
        ≤ ∏ i ∈ (Ioc w E).map (addLeftEmbedding (k - h)),
          Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 := by
          rw [← prod_sdiff hsub]
          exact mul_le_of_le_one_left (prod_cos_sq_nonneg _ _) (prod_cos_sq_le_one _ _)
      _ = slProd (m - κ + 1) E w s := by
          rw [prod_map]
          unfold slProd
          refine prod_congr rfl fun l hl => ?_
          have hl' := mem_Ioc.mp hl
          simp only [addLeftEmbedding_apply]
          congr 2
          rw [hr]
          unfold piHat
          have hnat : m - (k - h + l) + 1 = m - κ + 1 + E + 1 - l := by omega
          rw [hnat]
          have hp : (2 : ℝ) ^ (k - h + l) = 2 ^ (k - h) * 2 ^ l := pow_add _ _ _
          rw [hp]
          push_cast
          field_simp
  have hsinc : S4 ≤ sincBound c s := by
    apply sinc_pow_four_le_sincBound hc hs
    rw [hr]
    unfold piHat
    have hp : (2 : ℝ) ^ κ = 2 ^ (k - h) * 2 ^ (κ - k + h) := by
      rw [← pow_add]; congr 1; omega
    have hpos : (0 : ℝ) < 2 ^ (κ - k + h + 1) := by positivity
    have hval : π * (((((m : ℤ) + 1) * 2 ^ (k - h) * s : ℤ)) : ℝ) * (((m - κ + 1 : ℕ) : ℝ) / 2 ^ κ) /
        (2 * ((m : ℝ) + 1)) = π * s * (((m - κ + 1 : ℕ) : ℝ) / 2 ^ (κ - k + h + 1)) := by
      rw [hp, pow_succ]; push_cast; field_simp
    rw [hval, abs_mul, abs_mul, abs_of_pos pi_pos, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((m - κ + 1 : ℕ) : ℝ) / 2 ^ (κ - k + h + 1))]
    have : c ≤ ((m - κ + 1 : ℕ) : ℝ) / 2 ^ (κ - k + h + 1) := by rw [le_div_iff₀ hpos]; exact hcn
    have h0 : (0 : ℝ) ≤ |(s : ℝ)| := abs_nonneg _
    have := mul_le_mul_of_nonneg_left this h0
    nlinarith [pi_pos]
  calc S4 * (∏ i ∈ Icc 1 (k - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2) *
        ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2
      ≤ S4 * 1 * ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 := by
        gcongr
    _ = S4 * ∏ i ∈ Icc 1 (κ - 1), Real.cos (π * r * piHat m i / ((m : ℝ) + 1)) ^ 2 := by ring
    _ ≤ sincBound c s * slProd (m - κ + 1) E w s := by
        apply mul_le_mul hsinc hP2 hP20 (sincBound_nonneg c s)

/-- **Lemma 7.14 for the semi-local products** (`s` odd). -/
theorem sum_slProd_le {a w o E : ℕ} (ho : Odd o) (hao : a + 1 = 2 ^ w * o) {s : ℤ} (hs : Odd s)
    (ℓ₀ Λ : ℕ) :
    ∑ i ∈ range Λ, slProd ((a + 1) * (ℓ₀ + i)) E w s ≤ Λ * 2 ^ w / 2 ^ E + 1 := by
  have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg _
  rcases lt_or_ge w E with hwE | hwE
  · obtain ⟨j, hj⟩ : ∃ j, E = 0 + w + j := ⟨E - w, by omega⟩
    have key := progression_sum_le_range (L := Λ) (j := j) (v := 0) ho hao hs (by ring)
      (fun l => (E : ℝ) + 1 - l) (ℓ₀ : ℤ)
    have heq : ∀ i : ℕ, slProd ((a + 1) * (ℓ₀ + i)) E w s =
        ∏ l ∈ Ioc (0 + w) (0 + w + j), cos (π * s * ((a + 1) * ((((ℓ₀ : ℤ)) : ℝ) + i) +
          ((E : ℝ) + 1 - l)) / 2 ^ l) ^ 2 := by
      intro i
      unfold slProd
      rw [show 0 + w + j = E by omega, zero_add]
      refine prod_congr rfl fun l hl => ?_
      have hl' := mem_Ioc.mp hl
      congr 4
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    simp_rw [heq]
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hsum : ∑ i ∈ range Λ, ∏ l ∈ Ioc (0 + w) (0 + w + j), cos (π * s * ((a + 1) *
        ((((ℓ₀ : ℤ)) : ℝ) + i) + ((E : ℝ) + 1 - l)) / 2 ^ l) ^ 2 ≤ (Λ + 2 ^ j - 1) / 2 ^ j := by
      rw [le_div_iff₀ hp, mul_comm]; exact key
    have h1 : ((Λ : ℝ) + 2 ^ j - 1) / 2 ^ j ≤ Λ / 2 ^ j + 1 := by
      rw [div_add_one hp.ne']
      exact div_le_div_of_nonneg_right (by linarith) hp.le
    have h2 : (Λ : ℝ) / 2 ^ j = Λ * 2 ^ w / 2 ^ E := by
      rw [hj, zero_add, pow_add]; field_simp
    linarith
  · have hempty : Ioc w E = ∅ := Ioc_eq_empty (by omega)
    have : ∀ i : ℕ, slProd ((a + 1) * (ℓ₀ + i)) E w s = 1 := fun i => by
      unfold slProd; rw [hempty, prod_empty]
    simp_rw [this]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    have : (Λ : ℝ) ≤ Λ * 2 ^ w / 2 ^ E := by
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ E ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hwE
      nlinarith
    linarith

/-- Sums over `𝒦` of nonnegative functions of `(ρ(k), ℓ_k)` are at most the sums over all pairs
`ρ ≤ a`, `ℓ ∈ [ℓ_K, ℓ_1]` (`k ↦ (ρ(k), ℓ_k)` is injective on `𝒦`). -/
theorem sum_coarse_le_pairs {m a : ℕ} (ha : 1 ≤ a) (hsize : 4 * (jZero m + a) ≤ m + 1)
    (G : ℕ → ℕ → ℝ) (hG : ∀ ρ ℓ, 0 ≤ G ρ ℓ) :
    ∑ k ∈ coarseZone m, G (rhoK m a k) (ellK m a k) ≤
      ∑ ρ ∈ range (a + 1), ∑ i ∈ range (ellK m a 1 + 1 - ellK m a ((m + 1) / 4)),
        G ρ (ellK m a ((m + 1) / 4) + i) := by
  set f : ℕ → ℕ × ℕ := fun k => (rhoK m a k, ellK m a k) with hf
  have hinj : ∀ x ∈ coarseZone m, ∀ y ∈ coarseZone m, f x = f y → x = y := by
    intro x hx y hy hxy
    simp only [f, Prod.mk.injEq] at hxy
    have hx' := coarse_facts ha hsize hx
    have hy' := coarse_facts ha hsize hy
    exact rho_ell_injective (by omega) (by omega) hxy.1 hxy.2
  have hsub : (coarseZone m).image f ⊆
      range (a + 1) ×ˢ Icc (ellK m a ((m + 1) / 4)) (ellK m a 1) := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [mem_product, mem_range, mem_Icc]
    have hk' := mem_Icc.mp hk
    exact ⟨Nat.mod_lt _ (Nat.succ_pos a), ellK_antitone hk'.2, ellK_antitone hk'.1⟩
  calc ∑ k ∈ coarseZone m, G (rhoK m a k) (ellK m a k)
      = ∑ p ∈ (coarseZone m).image f, G p.1 p.2 := by rw [sum_image hinj]
    _ ≤ ∑ p ∈ range (a + 1) ×ˢ Icc (ellK m a ((m + 1) / 4)) (ellK m a 1), G p.1 p.2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hG _ _)
    _ = ∑ ρ ∈ range (a + 1), ∑ ℓ ∈ Icc (ellK m a ((m + 1) / 4)) (ellK m a 1), G ρ ℓ :=
        sum_product _ _ _
    _ = _ := by
        refine sum_congr rfl fun ρ _ => ?_
        rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]

/-- The number `Λ` of `ℓ`'s satisfies `Λ 2^w ≤ N`. -/
theorem ellRange_mul_le {m a w o : ℕ} (hsize : 4 * (jZero m + a) ≤ m + 1)
    (hao : a + 1 = 2 ^ w * o) (ho : Odd o) :
    (((ellK m a 1 + 1 - ellK m a ((m + 1) / 4) : ℕ)) : ℝ) * 2 ^ w ≤ (m : ℝ) + 1 := by
  have hw : 2 ^ w ≤ a + 1 := by rw [hao]; exact Nat.le_mul_of_pos_right _ ho.pos
  have hK1 : 1 ≤ (m + 1) / 4 := by unfold jZero at hsize; omega
  have hKfit : (m + 1) / 4 + jZero m ≤ m := by unfold jZero at hsize ⊢; omega
  set Λ := ellK m a 1 + 1 - ellK m a ((m + 1) / 4)
  have h1 : (a + 1) * Λ ≤ (m + 1) / 4 + 2 * a := ell_range_card (a := a) hK1 hKfit
  have h2 : Λ * 2 ^ w ≤ (a + 1) * Λ := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hw
  have h3 : (m + 1) / 4 + 2 * a ≤ m + 1 := by unfold jZero at hsize; omega
  have : Λ * 2 ^ w ≤ m + 1 := by omega
  exact_mod_cast this

/-- The majorant `∑_{s odd} sb_c(s) slProd(n, E, w, s)` of `SL^{[h]}_k`. -/
noncomputable def slMajorant (c : ℝ) (n E w : ℕ) : ℝ :=
  ∑' s : ℤ, if Odd s then sincBound c s * slProd n E w s else 0

theorem summable_slMajorant_terms {c : ℝ} (hc : 0 < c) (n E w : ℕ) :
    Summable (fun s : ℤ => if Odd s then sincBound c s * slProd n E w s else 0) := by
  refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) (summable_sincBound hc).1
  · split_ifs
    · exact mul_nonneg (sincBound_nonneg c s) (slProd_nonneg _ _ _ _)
    · exact le_rfl
  · split_ifs
    · exact mul_le_of_le_one_right (sincBound_nonneg c s) (slProd_le_one _ _ _ _)
    · exact sincBound_nonneg c s

theorem slMajorant_nonneg (c : ℝ) (n E w : ℕ) : 0 ≤ slMajorant c n E w :=
  tsum_nonneg fun s => by
    split_ifs
    · exact mul_nonneg (sincBound_nonneg c s) (slProd_nonneg _ _ _ _)
    · exact le_rfl

theorem sum_slMajorant_le {a w o E : ℕ} (ho : Odd o) (hao : a + 1 = 2 ^ w * o) {c : ℝ}
    (hc : 0 < c) (ℓ₀ Λ : ℕ) :
    ∑ i ∈ range Λ, slMajorant c ((a + 1) * (ℓ₀ + i)) E w ≤
      (Λ * 2 ^ w / 2 ^ E + 1) * (8 / (3 * (π * c))) := by
  unfold slMajorant
  rw [← Summable.tsum_finsetSum (fun i _ => summable_slMajorant_terms hc _ E w)]
  have hs0 := summable_sincBound hc
  have hcoef : (0 : ℝ) ≤ Λ * 2 ^ w / 2 ^ E + 1 := by positivity
  calc ∑' s : ℤ, ∑ i ∈ range Λ, (if Odd s then sincBound c s * slProd ((a + 1) * (ℓ₀ + i)) E w s
        else 0)
      ≤ ∑' s : ℤ, (Λ * 2 ^ w / 2 ^ E + 1) * sincBound c s := by
        refine Summable.tsum_le_tsum (fun s => ?_) ?_ (hs0.1.mul_left _)
        · by_cases hs : Odd s
          · simp only [hs, ↓reduceIte]
            rw [← Finset.mul_sum]
            have h := sum_slProd_le ho hao hs ℓ₀ Λ (E := E)
            calc sincBound c s * ∑ i ∈ range Λ, slProd ((a + 1) * (ℓ₀ + i)) E w s
                ≤ sincBound c s * (Λ * 2 ^ w / 2 ^ E + 1) :=
                  mul_le_mul_of_nonneg_left h (sincBound_nonneg c s)
              _ = _ := by ring
          · simp only [hs, ↓reduceIte, sum_const_zero]
            exact mul_nonneg hcoef (sincBound_nonneg c s)
        · exact summable_sum fun i _ => summable_slMajorant_terms hc _ E w
    _ = (Λ * 2 ^ w / 2 ^ E + 1) * ∑' s : ℤ, sincBound c s := tsum_mul_left
    _ ≤ (Λ * 2 ^ w / 2 ^ E + 1) * (8 / (3 * (π * c))) := by gcongr; exact hs0.2

/-- `2^{D(k)} ≤ 2^{a+2} n_{κ_a(k)}` for `k ∈ 𝒦` (so `n_κ 2^{-D-2} ≥ 2^{-a-4}`). -/
theorem two_pow_dRho_le {m a k : ℕ} (ha : 1 ≤ a) (hsize : 4 * (jZero m + a) ≤ m + 1)
    (hk : k ∈ coarseZone m) :
    (2 : ℝ) ^ dRho m a (rhoK m a k) ≤ 2 ^ (a + 2) * (((a + 1) * ellK m a k : ℕ) : ℝ) := by
  obtain ⟨hk1, hfit, hkκ, hκm, hhalf⟩ := coarse_facts ha hsize hk
  have hn := nKappa_eq hfit
  have hnat : 2 ^ dRho m a (rhoK m a k) ≤ 2 ^ (a + 2) * ((a + 1) * ellK m a k) := by
    have h1 : 2 ^ dRho m a (rhoK m a k) ≤ 2 ^ (jZero m + a) :=
      Nat.pow_le_pow_right (by norm_num) (dRho_le m a _)
    have h2 := two_pow_jZero_le m
    rw [pow_add] at h1
    rw [pow_add]
    have h3 : 2 ^ jZero m * 2 ^ a ≤ 2 * (m + 1) * 2 ^ a := Nat.mul_le_mul_right _ h2
    have h4 : 2 * (m + 1) * 2 ^ a ≤ 2 * (2 * ((a + 1) * ellK m a k)) * 2 ^ a :=
      Nat.mul_le_mul_right _ (by omega)
    calc 2 ^ dRho m a (rhoK m a k) ≤ 2 ^ jZero m * 2 ^ a := h1
      _ ≤ 2 * (2 * ((a + 1) * ellK m a k)) * 2 ^ a := le_trans h3 h4
      _ = 2 ^ a * 2 ^ 2 * ((a + 1) * ellK m a k) := by ring
  exact_mod_cast hnat

/-- For `k ∈ 𝒦` and `2 ≤ h ≤ k`, `SL^{[h]}_k` is at most the majorant at `ℓ_k`, with
`c = 2^{-(a+3+h)}` and the cosine factors of index `l ∈ (w, D(k) + h - 1]` kept. -/
theorem semiLocal_le_majorant {m a k h : ℕ} (w : ℕ) (ha : 1 ≤ a)
    (hsize : 4 * (jZero m + a) ≤ m + 1) (hk : k ∈ coarseZone m) (hh : h ≤ k) :
    semiLocal m k (cancellerBelow m a k) h ≤
      slMajorant (1 / 2 ^ (a + 3 + h)) ((a + 1) * ellK m a k) (dRho m a (rhoK m a k) + h - 1) w := by
  obtain ⟨hk1, hfit, hkκ, hκm, hhalf⟩ := coarse_facts ha hsize hk
  have hn := nKappa_eq hfit
  have hD : cancellerBelow m a k - k = dRho m a (rhoK m a k) := by rw [cancellerBelow_eq]; omega
  have hc : (0 : ℝ) < 1 / 2 ^ (a + 3 + h) := by positivity
  unfold semiLocal slMajorant
  refine Summable.tsum_le_tsum (fun s => ?_) (summable_semiLocal hk1 hkκ.le)
    (summable_slMajorant_terms hc _ _ _)
  split_ifs with hs
  · have hs0 : s ≠ 0 := by rintro rfl; exact absurd hs (by decide)
    have hcn : 1 / 2 ^ (a + 3 + h) * 2 ^ (cancellerBelow m a k - k + h + 1) ≤
        ((m - cancellerBelow m a k + 1 : ℕ) : ℝ) := by
      rw [hD, hn]
      have h2 := two_pow_dRho_le ha hsize hk
      have e1 : (2 : ℝ) ^ (dRho m a (rhoK m a k) + h + 1) =
          2 ^ dRho m a (rhoK m a k) * 2 ^ (h + 1) := by rw [add_assoc, pow_add]
      have e2 : (2 : ℝ) ^ (a + 3 + h) = 2 ^ (a + 2) * 2 ^ (h + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [e1, e2, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      have hp : (0 : ℝ) < 2 ^ (h + 1) := by positivity
      have := mul_le_mul_of_nonneg_right h2 hp.le
      calc (2 : ℝ) ^ dRho m a (rhoK m a k) * 2 ^ (h + 1)
          ≤ 2 ^ (a + 2) * (((a + 1) * ellK m a k : ℕ) : ℝ) * 2 ^ (h + 1) := this
        _ = (((a + 1) * ellK m a k : ℕ) : ℝ) * (2 ^ (a + 2) * 2 ^ (h + 1)) := by ring
    have key := straddlePhi_semiLocal_le (w := w) hk1 hkκ hκm hh hc hcn hs0
    rw [hn] at key
    rw [show cancellerBelow m a k - k + h - 1 = dRho m a (rhoK m a k) + h - 1 by omega] at key
    exact key
  · exact le_rfl

/-- **Proposition 7.15(b).** Under `4(j₀ + a) ≤ N`, for every `H`,
`∑_{k ∈ 𝒦} ∑_{h=2}^{min(H,k)} SL^{[h]}_k ≤ (a + 1) 2^{a+H+8}/(3π)`; so the average over `𝒦` is
`O_a(2^H/N)`. -/
theorem sum_semiLocal_le {m a : ℕ} (H : ℕ) (ha : 1 ≤ a) (hsize : 4 * (jZero m + a) ≤ m + 1) :
    ∑ k ∈ coarseZone m, ∑ h ∈ Icc 2 (min H k), semiLocal m k (cancellerBelow m a k) h ≤
      (a + 1) * 2 ^ (a + H + 8) / (3 * π) := by
  obtain ⟨w, o, ho, hao⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : a + 1 ≠ 0)
  rw [Finset.sum_comm' (t' := Icc 2 H) (s' := fun h => (coarseZone m).filter (h ≤ ·))
    (fun k h => by
      simp only [mem_Icc, mem_filter, le_min_iff]
      constructor
      · rintro ⟨hk, h1, h2, h3⟩; exact ⟨⟨hk, h3⟩, h1, h2⟩
      · rintro ⟨⟨hk, h1⟩, h2, h3⟩; exact ⟨hk, h2, h3, h1⟩)]
  have hΛw := ellRange_mul_le hsize hao ho
  set Λ := ellK m a 1 + 1 - ellK m a ((m + 1) / 4)
  have hper : ∀ h ∈ Icc 2 H,
      ∑ k ∈ (coarseZone m).filter (h ≤ ·), semiLocal m k (cancellerBelow m a k) h ≤
        (a + 1) * 2 ^ (a + 7 + h) / (3 * π) := by
    intro h hh
    have hh2 : 2 ≤ h := (mem_Icc.mp hh).1
    have hc : (0 : ℝ) < 1 / 2 ^ (a + 3 + h) := by positivity
    have hρ : ∀ ρ ∈ range (a + 1),
        ∑ i ∈ range Λ, slMajorant (1 / 2 ^ (a + 3 + h)) ((a + 1) * (ellK m a ((m + 1) / 4) + i))
          (dRho m a ρ + h - 1) w ≤ 2 * (8 / (3 * (π * (1 / 2 ^ (a + 3 + h))))) := by
      intro ρ _
      have h1 := sum_slMajorant_le (E := dRho m a ρ + h - 1) ho hao hc (ellK m a ((m + 1) / 4)) Λ
      have hE : ((m : ℝ) + 1) ≤ 2 ^ (dRho m a ρ + h - 1) := by
        have h1 := lt_two_pow_jZero m
        have h2 : 2 ^ jZero m ≤ 2 ^ (dRho m a ρ + h - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by have := jZero_le_dRho m a ρ; omega)
        exact_mod_cast (by omega : m + 1 ≤ 2 ^ (dRho m a ρ + h - 1))
      have hratio : (Λ : ℝ) * 2 ^ w / 2 ^ (dRho m a ρ + h - 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h8 : (0 : ℝ) ≤ 8 / (3 * (π * (1 / 2 ^ (a + 3 + h)))) := by positivity
      calc _ ≤ (Λ * 2 ^ w / 2 ^ (dRho m a ρ + h - 1) + 1) * (8 / (3 * (π * (1 / 2 ^ (a + 3 + h))))) := h1
        _ ≤ (1 + 1) * (8 / (3 * (π * (1 / 2 ^ (a + 3 + h))))) := by gcongr
        _ = 2 * (8 / (3 * (π * (1 / 2 ^ (a + 3 + h))))) := by ring
    calc ∑ k ∈ (coarseZone m).filter (h ≤ ·), semiLocal m k (cancellerBelow m a k) h
        ≤ ∑ k ∈ (coarseZone m).filter (h ≤ ·), slMajorant (1 / 2 ^ (a + 3 + h))
            ((a + 1) * ellK m a k) (dRho m a (rhoK m a k) + h - 1) w :=
          sum_le_sum fun k hk => semiLocal_le_majorant w ha hsize (mem_filter.mp hk).1
            (mem_filter.mp hk).2
      _ ≤ ∑ k ∈ coarseZone m, slMajorant (1 / 2 ^ (a + 3 + h))
            ((a + 1) * ellK m a k) (dRho m a (rhoK m a k) + h - 1) w :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => slMajorant_nonneg _ _ _ _)
      _ ≤ ∑ ρ ∈ range (a + 1), ∑ i ∈ range Λ, slMajorant (1 / 2 ^ (a + 3 + h))
            ((a + 1) * (ellK m a ((m + 1) / 4) + i)) (dRho m a ρ + h - 1) w :=
          sum_coarse_le_pairs ha hsize
            (fun ρ ℓ => slMajorant (1 / 2 ^ (a + 3 + h)) ((a + 1) * ℓ) (dRho m a ρ + h - 1) w)
            (fun _ _ => slMajorant_nonneg _ _ _ _)
      _ ≤ ∑ ρ ∈ range (a + 1), 2 * (8 / (3 * (π * (1 / 2 ^ (a + 3 + h))))) := sum_le_sum hρ
      _ = (a + 1) * 2 ^ (a + 7 + h) / (3 * π) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          rw [show a + 7 + h = (a + 3 + h) + 4 by ring, pow_add]
          field_simp
          ring
  calc ∑ h ∈ Icc 2 H, ∑ k ∈ (coarseZone m).filter (h ≤ ·), semiLocal m k (cancellerBelow m a k) h
      ≤ ∑ h ∈ Icc 2 H, (a + 1) * 2 ^ (a + 7 + h) / (3 * π) := sum_le_sum hper
    _ ≤ ∑ h ∈ range (H + 1), (a + 1) * 2 ^ (a + 7 + h) / (3 * π) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx; simp only [mem_Icc] at hx; simp only [mem_range]; omega
        · intro _ _ _; positivity
    _ = (a + 1) * 2 ^ (a + 7) / (3 * π) * ∑ h ∈ range (H + 1), (2 : ℝ) ^ h := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun h _ => ?_
        rw [pow_add]; ring
    _ ≤ (a + 1) * 2 ^ (a + H + 8) / (3 * π) := by
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
        have : ((2 : ℝ) ^ (H + 1) - 1) / (2 - 1) ≤ 2 ^ (H + 1) := by norm_num
        calc (a + 1) * 2 ^ (a + 7) / (3 * π) * (((2 : ℝ) ^ (H + 1) - 1) / (2 - 1))
            ≤ (a + 1) * 2 ^ (a + 7) / (3 * π) * 2 ^ (H + 1) := by gcongr
          _ = (a + 1) * 2 ^ (a + H + 8) / (3 * π) := by
              rw [show a + H + 8 = (a + 7) + (H + 1) by ring, pow_add]; ring

/-! ### Proposition 7.15(c) -/

/-- `H_N = ⌊(log₂ N)/4⌋`. -/
def hN (m : ℕ) : ℕ := Nat.log 2 (m + 1) / 4

/-- `NL_k = V^{(a)}_k - F_k - ∑_{h=2}^{min(H_N, k)} SL^{[h]}_k`. -/
noncomputable def nonLocal (m a k : ℕ) : ℝ :=
  relVarianceA m a k - fineFloorK m k (cancellerBelow m a k) -
    ∑ h ∈ Icc 2 (min (hN m) k), semiLocal m k (cancellerBelow m a k) h

/-- The average of `NL_k` over the coarse zone. -/
noncomputable def meanNonLocal (m a : ℕ) : ℝ :=
  ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, nonLocal m a k

theorem fineFloorK_nonneg {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) : 0 ≤ fineFloorK m k κ :=
  tsum_nonneg fun t => by
    split_ifs
    · exact le_rfl
    · exact straddlePhi_nonneg hk hkκ _

theorem meanRelVariance_sub_meanNonLocal (m a : ℕ) :
    meanRelVariance m a - meanNonLocal m a = ((coarseZone m).card : ℝ)⁻¹ *
      ∑ k ∈ coarseZone m, (fineFloorK m k (cancellerBelow m a k) +
        ∑ h ∈ Icc 2 (min (hN m) k), semiLocal m k (cancellerBelow m a k) h) := by
  unfold meanRelVariance meanNonLocal nonLocal
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  ring

theorem meanError_nonneg (m a : ℕ) : 0 ≤ meanRelVariance m a - meanNonLocal m a := by
  rw [meanRelVariance_sub_meanNonLocal]
  refine mul_nonneg (by positivity) (sum_nonneg fun k hk => ?_)
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hkκ : k ≤ cancellerBelow m a k := by rw [cancellerBelow_eq]; omega
  exact add_nonneg (fineFloorK_nonneg hk1 hkκ) (sum_nonneg fun h _ => semiLocal_nonneg hk1 hkκ)

theorem meanError_le {m a : ℕ} (ha : 1 ≤ a) (hsize : 4 * (jZero m + a) ≤ m + 1) :
    meanRelVariance m a - meanNonLocal m a ≤
      (((m + 1) / 4 : ℕ) : ℝ)⁻¹ * ((a + 1) * (3 * (2 ^ (a + 4) / π) ^ 2 + 8 * 2 ^ (a + 4) / (3 * π)) +
        (a + 1) * 2 ^ (a + hN m + 8) / (3 * π)) := by
  rw [meanRelVariance_sub_meanNonLocal, sum_add_distrib]
  have hcard : (coarseZone m).card = (m + 1) / 4 := by unfold coarseZone; simp
  rw [hcard]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (sum_fineFloorK_le ha hsize) (sum_semiLocal_le (hN m) ha hsize)

theorem two_pow_hN_le_sqrt (m : ℕ) : (2 : ℝ) ^ hN m ≤ √((m : ℝ) + 1) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have h1 : 2 * hN m ≤ Nat.log 2 (m + 1) := by unfold hN; omega
  have h2 : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
  have h3 : 2 ^ (2 * hN m) ≤ m + 1 := le_trans (Nat.pow_le_pow_right (by norm_num) h1) h2
  rw [← pow_mul, mul_comm]
  exact_mod_cast h3

/-- The error term `V̄^{(a)}_m - mean NL` tends to `0`. -/
theorem tendsto_meanError {a : ℕ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun m => meanRelVariance m a - meanNonLocal m a) Filter.atTop (nhds 0) := by
  set C₁ : ℝ := (a + 1) * (3 * (2 ^ (a + 4) / π) ^ 2 + 8 * 2 ^ (a + 4) / (3 * π)) with hC₁
  set C₂ : ℝ := (a + 1) * 2 ^ (a + 8) / (3 * π) with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hsize : ∀ᶠ m in Filter.atTop, 4 * (jZero m + a) ≤ m + 1 := by
    have := (Filter.tendsto_add_atTop_nat 1).eventually (eventually_four_mul_log_add_le (1 + a))
    filter_upwards [this] with m hm
    unfold jZero; omega
  have hm8 : ∀ᶠ m : ℕ in Filter.atTop, 8 ≤ m := Filter.eventually_ge_atTop 8
  refine squeeze_zero' (Filter.Eventually.of_forall fun m => meanError_nonneg m a) ?_
    (g := fun m : ℕ => 8 * (C₁ + C₂) / √((m : ℝ) + 1)) ?_
  · filter_upwards [hsize, hm8] with m hm hm8
    have hb := meanError_le ha hm
    have hK : (0 : ℝ) < (((m + 1) / 4 : ℕ) : ℝ) := by
      have : 0 < (m + 1) / 4 := by omega
      exact_mod_cast this
    have hK8 : ((m : ℝ) + 1) ≤ 8 * (((m + 1) / 4 : ℕ) : ℝ) := by
      have : m + 1 ≤ 8 * ((m + 1) / 4) := by omega
      exact_mod_cast this
    have hsq : 0 < √((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsq2 : √((m : ℝ) + 1) * √((m : ℝ) + 1) = (m : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hsq1 : 1 ≤ √((m : ℝ) + 1) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; simp
    have h2H := two_pow_hN_le_sqrt m
    have hsplit : (a + 1 : ℝ) * 2 ^ (a + hN m + 8) / (3 * π) = C₂ * 2 ^ hN m := by
      rw [hC₂, show a + hN m + 8 = (a + 8) + hN m by ring, pow_add]; ring
    rw [hsplit, ← hC₁] at hb
    refine le_trans hb ?_
    rw [inv_mul_le_iff₀ hK, ← mul_div_assoc, le_div_iff₀ hsq]
    -- (C₁ + C₂ 2^H) √N ≤ (m + 1/4) * 8 (C₁ + C₂)... via N ≤ 8K
    have e1 : (C₁ + C₂ * 2 ^ hN m) * √((m : ℝ) + 1) ≤ (C₁ + C₂) * ((m : ℝ) + 1) := by
      have : C₂ * 2 ^ hN m * √((m : ℝ) + 1) ≤ C₂ * ((m : ℝ) + 1) := by
        have h := mul_le_mul_of_nonneg_right h2H hsq.le
        rw [hsq2] at h
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h hC₂0
      have : C₁ * √((m : ℝ) + 1) ≤ C₁ * ((m : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ hC₁0
        nlinarith
      nlinarith
    have e2 : (C₁ + C₂) * ((m : ℝ) + 1) ≤ (C₁ + C₂) * (8 * (((m + 1) / 4 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hK8 (by positivity)
    calc (C₁ + C₂ * 2 ^ hN m) * √((m : ℝ) + 1) ≤ (C₁ + C₂) * (8 * (((m + 1) / 4 : ℕ) : ℝ)) :=
          le_trans e1 e2
      _ = (((m + 1) / 4 : ℕ) : ℝ) * (8 * (C₁ + C₂)) := by ring
  · have h1 : Filter.Tendsto (fun m : ℕ => √((m : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp (Filter.tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop)
    exact tendsto_const_nhds.div_atTop h1

/-- **Proposition 7.15(c) at the cut-off `H_N = ⌊¼ log₂ N⌋`**: Conjecture S holds for `a` if and
only if the average of `NL_k = V^{(a)}_k - F_k - ∑_{h=2}^{min(H_N, k)} SL^{[h]}_k` over `𝒦` tends
to `0`. -/
theorem conjectureS_iff_meanNonLocal {a : ℕ} (ha : 1 ≤ a) :
    ConjectureS a ↔ Filter.Tendsto (fun m => meanNonLocal m a) Filter.atTop (nhds 0) := by
  have hE := tendsto_meanError ha
  unfold ConjectureS
  constructor
  · intro h
    have := h.sub hE
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  · intro h
    have := h.add hE
    simp only [add_sub_cancel, add_zero] at this
    exact this

/-! ### The decomposition `V_k = F_k + ∑_h SL^{[h]}_k + SB_k` -/

/-- `SB_k = ∑_{r ∉ Nℤ} φ_k(r)`, the sidebands. -/
noncomputable def sideband (m k κ : ℕ) : ℝ :=
  ∑' r : ℤ, if ((m : ℤ) + 1) ∣ r then 0 else straddlePhi m k κ r

theorem summable_ite {f : ℤ → ℝ} (hf : Summable f) (p : ℤ → Prop) [DecidablePred p] :
    Summable (fun w => if p w then f w else 0) :=
  hf.summable_of_eq_zero_or_self fun w => by
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- One dyadic step: `∑_{w ≠ 0} f(w) = ∑_{w odd} f(w) + ∑_{t ≠ 0} f(2t)`. -/
theorem tsum_ne_zero_split {f : ℤ → ℝ} (hf : Summable f) :
    ∑' w : ℤ, (if w = 0 then 0 else f w) =
      ∑' w : ℤ, (if Odd w then f w else 0) + ∑' t : ℤ, (if t = 0 then 0 else f (2 * t)) := by
  have hpt : ∀ w : ℤ, (if w = 0 then 0 else f w) =
      (if Odd w then f w else 0) + (if Even w ∧ w ≠ 0 then f w else 0) := by
    intro w
    by_cases hw : w = 0
    · subst hw; simp
    · rcases Int.even_or_odd w with he | ho
      · have : ¬ Odd w := Int.not_odd_iff_even.mpr he
        simp [hw, he, this]
      · have : ¬ Even w := Int.not_even_iff_odd.mpr ho
        simp [hw, ho, this]
  simp_rw [hpt]
  rw [Summable.tsum_add (summable_ite hf _) (summable_ite hf _)]
  congr 1
  have hinj : Function.Injective (fun t : ℤ => 2 * t) := fun x y h => by simpa using h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun t => ?_
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht]
  · intro w hw
    rw [Function.mem_support] at hw
    by_cases h : Even w ∧ w ≠ 0
    · obtain ⟨⟨r, hr⟩, _⟩ := h
      exact ⟨r, by simp only; omega⟩
    · simp [h] at hw

/-- Iterated dyadic splitting:
`∑_{w ≠ 0} f(w) = ∑_{i<j} ∑_{s odd} f(2^i s) + ∑_{t ≠ 0} f(2^j t)`. -/
theorem tsum_ne_zero_dyadic {f : ℤ → ℝ} (hf : Summable f) (j : ℕ) :
    ∑' w : ℤ, (if w = 0 then 0 else f w) =
      ∑ i ∈ range j, ∑' s : ℤ, (if Odd s then f (2 ^ i * s) else 0) +
        ∑' t : ℤ, (if t = 0 then 0 else f (2 ^ j * t)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hinj : Function.Injective (fun t : ℤ => 2 ^ j * t) := fun x y h =>
      mul_left_cancel₀ (by positivity : (2 : ℤ) ^ j ≠ 0) h
    have hfj : Summable (fun t : ℤ => f (2 ^ j * t)) := hf.comp_injective hinj
    have hstep := tsum_ne_zero_split hfj
    rw [ih, hstep, sum_range_succ, add_assoc]
    congr 3
    ext t
    rw [pow_succ, mul_assoc]

/-- **The decomposition** `V_k = SB_k + F_k + ∑_{h=2}^{k} SL^{[h]}_k` (`1 ≤ k ≤ κ`). -/
theorem relVariance_decomp {m k κ : ℕ} (hk : 1 ≤ k) (hkκ : k ≤ κ) :
    relVariance m k κ = sideband m k κ + fineFloorK m k κ + ∑ h ∈ Icc 2 k, semiLocal m k κ h := by
  rw [relVariance_eq_tsum hk hkκ]
  set φ := straddlePhi m k κ with hφ
  set N : ℤ := (m : ℤ) + 1 with hN
  have hNpos : 0 < N := by positivity
  have hsum : Summable (fun r : ℤ => if r = 0 then 0 else φ r) :=
    (hasSum_straddlePhi_ne_zero (m := m) hk hkκ).summable
  have hφs : Summable φ := (hasSum_straddlePhi (m := m) hk hkκ).summable
  -- split off the sidebands
  have hpt : ∀ r : ℤ, (if r = 0 then 0 else φ r) =
      (if N ∣ r then 0 else φ r) + (if N ∣ r ∧ r ≠ 0 then φ r else 0) := by
    intro r
    by_cases hr : r = 0
    · subst hr; simp
    · by_cases hd : N ∣ r
      · simp [hr, hd]
      · simp [hr, hd]
  simp_rw [hpt]
  have hs1 : Summable (fun r : ℤ => if N ∣ r then 0 else φ r) :=
    hφs.summable_of_eq_zero_or_self fun r => by
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [Summable.tsum_add hs1 (summable_ite hφs _)]
  -- the multiples of `N`
  have hinjN : Function.Injective (fun w : ℤ => N * w) := fun x y h =>
    mul_left_cancel₀ hNpos.ne' h
  have hmult : ∑' r : ℤ, (if N ∣ r ∧ r ≠ 0 then φ r else 0) =
      ∑' w : ℤ, (if w = 0 then 0 else φ (N * w)) := by
    rw [← hinjN.tsum_eq]
    · refine tsum_congr fun w => ?_
      by_cases hw : w = 0
      · simp [hw]
      · have : N * w ≠ 0 := mul_ne_zero hNpos.ne' hw
        simp [hw, this]
    · intro r hr
      rw [Function.mem_support] at hr
      by_cases h : N ∣ r ∧ r ≠ 0
      · obtain ⟨⟨w, hw⟩, _⟩ := h
        exact ⟨w, hw.symm⟩
      · simp [h] at hr
  rw [hmult, tsum_ne_zero_dyadic (f := fun w => φ (N * w)) (hφs.comp_injective hinjN) (k - 1)]
  unfold sideband fineFloorK
  rw [← hN, add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  · refine tsum_congr fun t => ?_
    simp only [hφ, mul_assoc]
  · -- reindex `i = k - h`
    unfold semiLocal
    refine Finset.sum_nbij' (fun i => k - i) (fun h => k - h) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [mem_range] at hi; simp only [mem_Icc]; omega
    · intro h hh; simp only [mem_Icc] at hh; simp only [mem_range]; omega
    · intro i hi; simp only [mem_range] at hi; omega
    · intro h hh; simp only [mem_Icc] at hh; omega
    · intro i hi
      simp only [mem_range] at hi
      refine tsum_congr fun s => ?_
      rw [show k - (k - i) = i by omega, ← hN, mul_assoc]

/-! ### Proposition 7.15(c) for every cut-off `H` with `2^H = o(N)` -/

/-- `NL^{(H)}_k = V^{(a)}_k - F_k - ∑_{h=2}^{min(H,k)} SL^{[h]}_k` for a cut-off `H`. -/
noncomputable def nonLocalGen (m a H k : ℕ) : ℝ :=
  relVarianceA m a k - fineFloorK m k (cancellerBelow m a k) -
    ∑ h ∈ Icc 2 (min H k), semiLocal m k (cancellerBelow m a k) h

/-- The average of `NL^{(H)}_k` over the coarse zone. -/
noncomputable def meanNonLocalGen (m a H : ℕ) : ℝ :=
  ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, nonLocalGen m a H k

/-- **Proposition 7.15(c)**: for every cut-off sequence `H(m)` with
`2^{H(m)}/N → 0` (e.g. `H(m) = ⌊log₂ N⌋ - ⌈log₂ log₂ N⌉`, far beyond `⌊¼ log₂ N⌋`), Conjecture S
holds for `a` iff the average of `NL^{(H)}_k` over `𝒦` tends to `0`. -/
theorem conjectureS_iff_meanNonLocalGen {a : ℕ} (ha : 1 ≤ a) (H : ℕ → ℕ)
    (hH : Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ H m / ((m : ℝ) + 1)) Filter.atTop (nhds 0)) :
    ConjectureS a ↔ Filter.Tendsto (fun m => meanNonLocalGen m a (H m)) Filter.atTop (nhds 0) := by
  set C₁ : ℝ := (a + 1) * (3 * (2 ^ (a + 4) / π) ^ 2 + 8 * 2 ^ (a + 4) / (3 * π)) with hC₁
  set C₂ : ℝ := (a + 1) * 2 ^ (a + 8) / (3 * π) with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hdiff : ∀ m, meanRelVariance m a - meanNonLocalGen m a (H m) =
      ((coarseZone m).card : ℝ)⁻¹ * ∑ k ∈ coarseZone m, (fineFloorK m k (cancellerBelow m a k) +
        ∑ h ∈ Icc 2 (min (H m) k), semiLocal m k (cancellerBelow m a k) h) := by
    intro m
    unfold meanRelVariance meanNonLocalGen nonLocalGen
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    ring
  have hE : Filter.Tendsto (fun m => meanRelVariance m a - meanNonLocalGen m a (H m))
      Filter.atTop (nhds 0) := by
    have hsize : ∀ᶠ m in Filter.atTop, 4 * (jZero m + a) ≤ m + 1 := by
      have := (Filter.tendsto_add_atTop_nat 1).eventually (eventually_four_mul_log_add_le (1 + a))
      filter_upwards [this] with m hm
      unfold jZero; omega
    have hm8 : ∀ᶠ m : ℕ in Filter.atTop, 8 ≤ m := Filter.eventually_ge_atTop 8
    have hnn : ∀ m, 0 ≤ meanRelVariance m a - meanNonLocalGen m a (H m) := by
      intro m
      rw [hdiff]
      refine mul_nonneg (by positivity) (sum_nonneg fun k hk => ?_)
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have hkκ : k ≤ cancellerBelow m a k := by rw [cancellerBelow_eq]; omega
      exact add_nonneg (fineFloorK_nonneg hk1 hkκ) (sum_nonneg fun h _ => semiLocal_nonneg hk1 hkκ)
    refine squeeze_zero' (Filter.Eventually.of_forall hnn) ?_
      (g := fun m : ℕ => 8 * C₁ * (1 / ((m : ℝ) + 1)) + 8 * C₂ * ((2 : ℝ) ^ H m / ((m : ℝ) + 1))) ?_
    · filter_upwards [hsize, hm8] with m hm hm8
      rw [hdiff, sum_add_distrib]
      have hcard : (coarseZone m).card = (m + 1) / 4 := by unfold coarseZone; simp
      rw [hcard]
      have hK : (0 : ℝ) < (((m + 1) / 4 : ℕ) : ℝ) := by
        have : 0 < (m + 1) / 4 := by omega
        exact_mod_cast this
      have hK8 : ((m : ℝ) + 1) ≤ 8 * (((m + 1) / 4 : ℕ) : ℝ) := by
        have : m + 1 ≤ 8 * ((m + 1) / 4) := by omega
        exact_mod_cast this
      have h1 := sum_fineFloorK_le ha hm
      have h2 := sum_semiLocal_le (H m) ha hm
      rw [← hC₁] at h1
      have h2' : ∑ k ∈ coarseZone m, ∑ h ∈ Icc 2 (min (H m) k), semiLocal m k (cancellerBelow m a k) h
          ≤ C₂ * 2 ^ H m := by
        refine le_trans h2 (le_of_eq ?_)
        rw [hC₂, show a + H m + 8 = (a + 8) + H m by ring, pow_add]; ring
      have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [inv_mul_le_iff₀ hK]
      have e : (((m + 1) / 4 : ℕ) : ℝ) * (8 * C₁ * (1 / ((m : ℝ) + 1)) +
          8 * C₂ * ((2 : ℝ) ^ H m / ((m : ℝ) + 1))) =
          (8 * (((m + 1) / 4 : ℕ) : ℝ) / ((m : ℝ) + 1)) * (C₁ + C₂ * 2 ^ H m) := by
        field_simp
      rw [e]
      have hratio : 1 ≤ 8 * (((m + 1) / 4 : ℕ) : ℝ) / ((m : ℝ) + 1) := by
        rw [le_div_iff₀ hN]; linarith
      have hpos : 0 ≤ C₁ + C₂ * 2 ^ H m := by positivity
      calc _ ≤ C₁ + C₂ * 2 ^ H m := add_le_add h1 h2'
        _ ≤ (8 * (((m + 1) / 4 : ℕ) : ℝ) / ((m : ℝ) + 1)) * (C₁ + C₂ * 2 ^ H m) :=
            le_mul_of_one_le_left hpos hratio
    · have h1 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := (h1.const_mul (8 * C₁)).add (hH.const_mul (8 * C₂))
      simpa using this
  unfold ConjectureS
  constructor
  · intro h
    have := h.sub hE
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  · intro h
    have := h.add hE
    simp only [add_sub_cancel, add_zero] at this
    exact this

end MergeDepth
