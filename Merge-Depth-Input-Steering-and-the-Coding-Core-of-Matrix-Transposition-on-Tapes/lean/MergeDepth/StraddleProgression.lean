import Mathlib

/-!
# Partial results on Conjecture S: dyadic products along a progression (Lemma 7.14)

* `window_sum_prod_cos_sq`: **the window identity**. For odd `u`, real `γ_s` and any `ℓ₀`,
  `∑_{ℓ ∈ [ℓ₀, ℓ₀ + 2^j)} ∏_{s=1}^{j} cos²(π(u ℓ 2^{-s} + γ_s)) = 1` (split off the top bit:
  `cos²θ + cos²(θ + π u/2) = 1`).
* `sum_prod_cos_sq_le`: hence the sum over any `L` consecutive integers is at most `⌈L/2^j⌉`.
* `progression_sum_le`, `progression_avg_le_strong`: **Lemma 7.14, strengthened**. With
  `a + 1 = 2^w o`, `t = 2^v t'` (`o`, `t'` odd) and `ℓ` over `L` consecutive integers, already the
  products over the `j` indices `e ∈ (v + w, v + w + j]` satisfy
  `2^j ∑_ℓ ∏_e cos²(π t((a+1)ℓ + c_e) 2^{-e}) ≤ L + 2^j - 1`, i.e. the average is at most
  `2^{-j} + (1 - 2^{-j})/L`.
* `progression_avg_le`: **Lemma 7.14** as stated (product over `e ∈ (v, v + w + j]`, bound
  `2^{-j} + 2^j/(2L)`, `j ≥ 1`, `L ≥ 1`).
-/

namespace MergeDepth

open Finset Real

/-- `cos²(π(x + n)) = cos²(πx)` for integers `n`. -/
theorem cos_sq_pi_mul_add_int (x : ℝ) (n : ℤ) : cos (π * (x + n)) ^ 2 = cos (π * x) ^ 2 := by
  rw [mul_add, mul_comm π (n : ℝ), cos_add_int_mul_pi, mul_pow]
  have : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [sq, ← mul_zpow]; norm_num
  rw [this, one_mul]

/-- `cos²(π(x + u/2)) = sin²(πx)` for odd `u`. -/
theorem cos_sq_pi_mul_add_half_odd (x : ℝ) {u : ℤ} (hu : Odd u) :
    cos (π * (x + u / 2)) ^ 2 = sin (π * x) ^ 2 := by
  obtain ⟨c, rfl⟩ := hu
  have : π * (x + ((2 * c + 1 : ℤ) : ℝ) / 2) = (π * x + π / 2) + c * π := by push_cast; ring
  rw [this, cos_add_int_mul_pi, mul_pow, cos_add_pi_div_two, neg_sq]
  have h1 : ((-1 : ℝ) ^ c) ^ 2 = 1 := by
    rw [sq, ← mul_zpow]; norm_num
  rw [h1, one_mul]

/-- **The window identity.** For an odd integer `u`, real `γ_s` and any integer `ℓ₀`, the sum of
`∏_{s=1}^{j} cos²(π(u ℓ 2^{-s} + γ_s))` over the `2^j` consecutive integers `ℓ ∈ [ℓ₀, ℓ₀ + 2^j)`
is exactly `1`. -/
theorem window_sum_prod_cos_sq {u : ℤ} (hu : Odd u) (γ : ℕ → ℝ) (ℓ₀ : ℤ) (j : ℕ) :
    ∑ i ∈ range (2 ^ j), ∏ s ∈ Icc 1 j, cos (π * (u * (ℓ₀ + i) / 2 ^ s + γ s)) ^ 2 = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
    refine Eq.trans (sum_congr rfl fun i _ => ?_) ih
    rw [prod_Icc_succ_top (by omega), prod_Icc_succ_top (by omega)]
    have h1 : ∏ s ∈ Icc 1 j, cos (π * (u * (ℓ₀ + ((2 ^ j + i : ℕ) : ℝ)) / 2 ^ s + γ s)) ^ 2 =
        ∏ s ∈ Icc 1 j, cos (π * (u * (ℓ₀ + i) / 2 ^ s + γ s)) ^ 2 := by
      refine prod_congr rfl fun s hs => ?_
      have hs' : s ≤ j := (mem_Icc.mp hs).2
      have : (u : ℝ) * (ℓ₀ + ((2 ^ j + i : ℕ) : ℝ)) / 2 ^ s + γ s =
          (u * (ℓ₀ + i) / 2 ^ s + γ s) + ((u * 2 ^ (j - s) : ℤ) : ℝ) := by
        push_cast
        rw [show (2 : ℝ) ^ j = 2 ^ (j - s) * 2 ^ s by rw [← pow_add, Nat.sub_add_cancel hs']]
        field_simp
        ring
      rw [this, cos_sq_pi_mul_add_int]
    have h2 : cos (π * (u * (ℓ₀ + ((2 ^ j + i : ℕ) : ℝ)) / 2 ^ (j + 1) + γ (j + 1))) ^ 2 =
        sin (π * (u * (ℓ₀ + i) / 2 ^ (j + 1) + γ (j + 1))) ^ 2 := by
      have : (u : ℝ) * (ℓ₀ + ((2 ^ j + i : ℕ) : ℝ)) / 2 ^ (j + 1) + γ (j + 1) =
          (u * (ℓ₀ + i) / 2 ^ (j + 1) + γ (j + 1)) + u / 2 := by
        push_cast
        rw [pow_succ]
        field_simp
        ring
      rw [this, cos_sq_pi_mul_add_half_odd _ hu]
    rw [h1, h2, ← mul_add, cos_sq_add_sin_sq, mul_one]


theorem prod_cos_sq_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ ∏ i ∈ s, cos (f i) ^ 2 := prod_nonneg fun _ _ => sq_nonneg _

theorem prod_cos_sq_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, cos (f i) ^ 2 ≤ 1 :=
  prod_le_one₀ (fun _ _ => sq_nonneg _) fun _ _ => by
    rw [sq_le_one_iff_abs_le_one]; exact abs_cos_le_one _

/-- **Sums over progressions.** Splitting `L` consecutive integers into windows of `2^j` and a
shorter rest, each of sum at most `1` by `window_sum_prod_cos_sq`:
`2^j ∑_{i < L} ∏_{s=1}^{j} cos²(π(u(ℓ₀ + i)2^{-s} + γ_s)) ≤ L + 2^j - 1`, i.e. the sum is at most
`⌈L/2^j⌉`. -/
theorem sum_prod_cos_sq_le {u : ℤ} (hu : Odd u) (γ : ℕ → ℝ) (j : ℕ) :
    ∀ (L : ℕ) (ℓ₀ : ℤ), 2 ^ j * ∑ i ∈ range L,
      ∏ s ∈ Icc 1 j, cos (π * (u * (ℓ₀ + i) / 2 ^ s + γ s)) ^ 2 ≤ L + 2 ^ j - 1 := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro ℓ₀
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rcases le_or_gt L (2 ^ j) with hL | hL
    · have hle : ∑ i ∈ range L, ∏ s ∈ Icc 1 j, cos (π * (u * (ℓ₀ + i) / 2 ^ s + γ s)) ^ 2 ≤ 1 := by
        rw [← window_sum_prod_cos_sq hu γ ℓ₀ j]
        exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hL)
          fun _ _ _ => prod_cos_sq_nonneg _ _
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0; simp only [range_zero, sum_empty, mul_zero, Nat.cast_zero, zero_add]; linarith
      · have : (1 : ℝ) ≤ L := by exact_mod_cast h0
        nlinarith
    · obtain ⟨M, rfl⟩ : ∃ M, L = 2 ^ j + M := ⟨L - 2 ^ j, by omega⟩
      rw [sum_range_add, window_sum_prod_cos_sq hu γ ℓ₀ j]
      have h := ih M (Nat.lt_add_of_pos_left (Nat.two_pow_pos j)) (ℓ₀ + 2 ^ j)
      have hcongr : ∑ i ∈ range M, ∏ s ∈ Icc 1 j,
            cos (π * (u * (ℓ₀ + ((2 ^ j + i : ℕ) : ℝ)) / 2 ^ s + γ s)) ^ 2 =
          ∑ i ∈ range M, ∏ s ∈ Icc 1 j,
            cos (π * (u * (((ℓ₀ + 2 ^ j : ℤ) : ℝ) + i) / 2 ^ s + γ s)) ^ 2 := by
        refine sum_congr rfl fun i _ => prod_congr rfl fun s _ => ?_
        push_cast; ring_nf
      rw [hcongr]
      push_cast at h ⊢
      nlinarith

/-- Reindexing `∏_{e ∈ (b, b + j]}` as `∏_{s = 1}^{j}`. -/
theorem prod_Ioc_add_eq_prod_Icc {M : Type*} [CommMonoid M] (g : ℕ → M) (b : ℕ) :
    ∀ j : ℕ, ∏ e ∈ Ioc b (b + j), g e = ∏ s ∈ Icc 1 j, g (b + s) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show b + (j + 1) = (b + j) + 1 by ring, prod_Ioc_succ_top (by omega), ih,
      prod_Icc_succ_top (by omega)]
    rfl

/-- `L` consecutive integers starting at `ℓ₀`. -/
theorem sum_Ico_int_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (ℓ₀ : ℤ) (L : ℕ) :
    ∑ ℓ ∈ Ico ℓ₀ (ℓ₀ + L), f ℓ = ∑ i ∈ range L, f (ℓ₀ + i) := by
  have : Ico ℓ₀ (ℓ₀ + L) = (range L).image (fun i : ℕ => ℓ₀ + i) := by
    ext x
    simp only [mem_Ico, mem_image, mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(x - ℓ₀).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [this, sum_image (fun a _ b _ h => by simpa using h)]

/-- **Lemma 7.14, strengthened.** Let `a + 1 = 2^w o` and `t = 2^v t'` with `o`, `t'` odd, let
`c_e` be real and let `ℓ` run over `L` consecutive integers. Then the products over only the `j`
indices `e ∈ (v + w, v + w + j]` already satisfy
`2^j ∑_ℓ ∏_e cos²(π t((a+1)ℓ + c_e) 2^{-e}) ≤ L + 2^j - 1`, i.e. their average is at most
`2^{-j} + (1 - 2^{-j})/L ≤ 2^{-j} + 1/L`. -/
theorem progression_sum_le {a w o v j L : ℕ} {t t' : ℤ} (ho : Odd o) (hao : a + 1 = 2 ^ w * o)
    (ht' : Odd t') (ht : t = 2 ^ v * t') (c : ℕ → ℝ) (ℓ₀ : ℤ) :
    2 ^ j * ∑ ℓ ∈ Ico ℓ₀ (ℓ₀ + L), ∏ e ∈ Ioc (v + w) (v + w + j),
      cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2 ≤ L + 2 ^ j - 1 := by
  have hu : Odd (t' * o) := ht'.mul (Int.odd_coe_nat o |>.mpr ho)
  have key := sum_prod_cos_sq_le hu (fun s => t * c (v + w + s) / 2 ^ (v + w + s)) j L ℓ₀
  refine le_of_eq_of_le ?_ key
  rw [sum_Ico_int_eq_sum_range]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [prod_Ioc_add_eq_prod_Icc]
  refine prod_congr rfl fun s _ => ?_
  congr 2
  have hao' : ((a : ℝ) + 1) = 2 ^ w * o := by exact_mod_cast hao
  rw [ht, hao']
  push_cast
  rw [pow_add, pow_add]
  field_simp

/-- **Lemma 7.14, strengthened (average form).** -/
theorem progression_avg_le_strong {a w o v j L : ℕ} {t t' : ℤ} (ho : Odd o)
    (hao : a + 1 = 2 ^ w * o) (ht' : Odd t') (ht : t = 2 ^ v * t') (c : ℕ → ℝ) (ℓ₀ : ℤ)
    (hL : 1 ≤ L) :
    (L : ℝ)⁻¹ * ∑ ℓ ∈ Ico ℓ₀ (ℓ₀ + L), ∏ e ∈ Ioc (v + w) (v + w + j),
      cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2 ≤ 2⁻¹ ^ j + (1 - 2⁻¹ ^ j) / L := by
  have key := progression_sum_le (L := L) (j := j) ho hao ht' ht c ℓ₀
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [inv_pow]
  rw [inv_mul_le_iff₀ hL']
  have : (L : ℝ) * ((2 ^ j)⁻¹ + (1 - (2 ^ j)⁻¹) / L) = (L + 2 ^ j - 1) / 2 ^ j := by
    field_simp; ring
  rw [this, le_div_iff₀ hp, mul_comm]
  exact key

/-- **Lemma 7.14** as stated: for `j ≥ 1`, the average over `L ≥ 1` consecutive integers of the
product over all `e ∈ (v, v + w + j]` is at most `2^{-j} + 2^j/(2L)`. -/
theorem progression_avg_le {a w o v j L : ℕ} {t t' : ℤ} (ho : Odd o)
    (hao : a + 1 = 2 ^ w * o) (ht' : Odd t') (ht : t = 2 ^ v * t') (hj : 1 ≤ j) (c : ℕ → ℝ)
    (ℓ₀ : ℤ) (hL : 1 ≤ L) :
    (L : ℝ)⁻¹ * ∑ ℓ ∈ Ico ℓ₀ (ℓ₀ + L), ∏ e ∈ Ioc v (v + w + j),
      cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2 ≤ 2⁻¹ ^ j + 2 ^ j / (2 * L) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : Ioc (v + w) (v + w + j) ⊆ Ioc v (v + w + j) := by
    intro x; simp only [mem_Ioc]; omega
  have hpt : ∀ ℓ : ℤ, ∏ e ∈ Ioc v (v + w + j), cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2 ≤
      ∏ e ∈ Ioc (v + w) (v + w + j), cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2 := by
    intro ℓ
    rw [← prod_sdiff hsub]
    exact mul_le_of_le_one_left (prod_cos_sq_nonneg _ _) (prod_cos_sq_le_one _ _)
  calc (L : ℝ)⁻¹ * ∑ ℓ ∈ Ico ℓ₀ (ℓ₀ + L), ∏ e ∈ Ioc v (v + w + j),
        cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2
      ≤ (L : ℝ)⁻¹ * ∑ ℓ ∈ Ico ℓ₀ (ℓ₀ + L), ∏ e ∈ Ioc (v + w) (v + w + j),
        cos (π * t * ((a + 1) * ℓ + c e) / 2 ^ e) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => hpt ℓ) (by positivity)
    _ ≤ 2⁻¹ ^ j + (1 - 2⁻¹ ^ j) / L := progression_avg_le_strong ho hao ht' ht c ℓ₀ hL
    _ ≤ 2⁻¹ ^ j + 2 ^ j / (2 * L) := by
        have h1 : (1 : ℝ) - 2⁻¹ ^ j ≤ 2 ^ j / 2 := by
          have : (2 : ℝ) ≤ 2 ^ j := by
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
          have : (0 : ℝ) ≤ 2⁻¹ ^ j := by positivity
          linarith
        have : (1 - 2⁻¹ ^ j) / (L : ℝ) ≤ (2 ^ j / 2) / L := div_le_div_of_nonneg_right h1 hL'.le
        rw [div_div] at this
        linarith

end MergeDepth
