import MergeDepth.StraddleFourier

/-!
# Partial results on Conjecture S: classes with a large fine floor (Proposition 7.13)

* `cancellerBelow_resonance`, `coarseZone_resonance`: for `m = 2^q + k + 3` (`q ≥ 6` even,
  `3k ≤ 2^q + 4`), `k ∈ 𝒦` and `κ_1(k) = k + q + 2`.
* `resFactor`, `fineFloorTerm_resonance`: at `t = 4` the cosine factors of
  `F(2^q - q + 2, q + 2)` are `cos²(π(e - 5)/2^{e-2})`, independent of `q`; those with `e ≤ 5`
  multiply to `1/2`, and the tail is controlled by `∏ cos² ≥ 1 - ∑ y²` and the closed form of
  `∑_{j ≥ 4} j² 4^{-j}` (`sum_tail_eq`).
* `fineFloor_resonance_gt`: `F(2^q - q + 2, q + 2) > 0.585` for every `q ≥ 6`.
* `resonance_class`: **Proposition 7.13** with `0.585`; `resonance_class_paper`: with `0.551`.
-/

namespace MergeDepth

open Finset Real DirectedReciprocity

/-! ### Arithmetic of the resonant classes -/

theorem sixtyfour_le_two_pow {q : ℕ} (hq : 6 ≤ q) : 64 ≤ 2 ^ q :=
  calc 64 = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq

theorem log_two_resonance {q k : ℕ} (hq : 6 ≤ q) (hk3 : 3 * k ≤ 2 ^ q + 4) :
    Nat.log 2 (2 ^ q + k + 3 + 1) = q := by
  have h64 := sixtyfour_le_two_pow hq
  rw [Nat.log_eq_iff (Or.inl (by omega))]
  constructor
  · omega
  · rw [pow_succ]; omega

theorem coarseZone_resonance {q k : ℕ} (hk : 1 ≤ k) (hk3 : 3 * k ≤ 2 ^ q + 4) :
    k ∈ coarseZone (2 ^ q + k + 3) := by
  unfold coarseZone
  rw [mem_Icc]
  omega

theorem cancellerBelow_resonance {q k : ℕ} (hq : 6 ≤ q) (hqe : Even q) (hk3 : 3 * k ≤ 2 ^ q + 4) :
    cancellerBelow (2 ^ q + k + 3) 1 k = k + q + 2 := by
  have hlog := log_two_resonance hq hk3
  have h64 := sixtyfour_le_two_pow hq
  have hqle : q < 2 ^ q := Nat.lt_two_pow_self
  have heven2 : 2 ∣ 2 ^ q := dvd_pow_self 2 (by omega)
  obtain ⟨r, hr⟩ := hqe
  unfold cancellerBelow
  simp only [hlog]
  omega

/-! ### Elementary trigonometric bounds -/

/-- `sin x₀ / x₀ ≤ sin x / x` for `0 < x ≤ x₀ ≤ π` (concavity of `sin`). -/
theorem sin_div_le_sin_div {x x₀ : ℝ} (hx : 0 < x) (hxx : x ≤ x₀) (hx₀ : x₀ ≤ π) :
    sin x₀ / x₀ ≤ sin x / x := by
  have hx0pos : 0 < x₀ := lt_of_lt_of_le hx hxx
  have h := (strictConcaveOn_sin_Icc.concaveOn).2 (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    (show x₀ ∈ Set.Icc 0 π from ⟨hx0pos.le, hx₀⟩)
    (show 0 ≤ 1 - x / x₀ by rw [sub_nonneg, div_le_one hx0pos]; exact hxx)
    (show 0 ≤ x / x₀ by positivity) (show 1 - x / x₀ + x / x₀ = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero] at h
  rw [div_mul_cancel₀ _ hx0pos.ne'] at h
  rw [div_le_div_iff₀ hx0pos hx]
  have := mul_le_mul_of_nonneg_right h hx0pos.le
  have e : x / x₀ * sin x₀ * x₀ = sin x₀ * x := by field_simp
  linarith

/-- `sinc⁴(πy) ≥ 64/π⁴` for `0 < y ≤ 1/4` (`sinc` normalized). -/
theorem sinc_pow_four_ge {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 1 / 4) :
    64 / π ^ 4 ≤ Real.sinc (π * y) ^ 4 := by
  have hpy : 0 < π * y := mul_pos pi_pos hy
  rw [sinc_of_ne_zero hpy.ne']
  have h := sin_div_le_sin_div hpy (show π * y ≤ π / 4 by nlinarith [pi_pos])
    (by linarith [pi_pos])
  rw [sin_pi_div_four] at h
  have hval : √2 / 2 / (π / 4) = 2 * √2 / π := by field_simp; ring
  rw [hval] at h
  have h0 : 0 ≤ 2 * √2 / π := by positivity
  have h4 : (2 * √2 / π) ^ 4 = 64 / π ^ 4 := by
    rw [div_pow, mul_pow, show (√2 : ℝ) ^ 4 = (√2 ^ 2) ^ 2 by ring, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [← h4]
  exact pow_le_pow_left₀ h0 h 4

/-- `cos² y ≥ 1 - y²`. -/
theorem one_sub_sq_le_cos_sq (y : ℝ) : 1 - y ^ 2 ≤ cos y ^ 2 := by
  have h1 : sin y ^ 2 ≤ y ^ 2 := by
    rw [← sq_abs (sin y), ← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sin_le_abs) 2
  have h2 := sin_sq_add_cos_sq y
  linarith

/-- `∏ cos²(y_e) ≥ 1 - ∑ y_e²`. -/
theorem one_sub_sum_sq_le_prod_cos_sq (s : Finset ℕ) (y : ℕ → ℝ) :
    1 - ∑ e ∈ s, y e ^ 2 ≤ ∏ e ∈ s, cos (y e) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hP0 : 0 ≤ ∏ e ∈ s, cos (y e) ^ 2 := prod_nonneg fun _ _ => sq_nonneg _
    have hS0 : 0 ≤ ∑ e ∈ s, y e ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hc := one_sub_sq_le_cos_sq (y a)
    have hc0 : 0 ≤ cos (y a) ^ 2 := sq_nonneg _
    rcases le_or_gt (1 - y a ^ 2) 0 with h | h
    · nlinarith
    · nlinarith

/-- `∑_{e=9}^{J+8} (e - 5)²/4^{e-2} = 173/110592 - ((J+3)²/3 + 8(J+3)/9 + 20/27)/(64 · 4^{J+3})`. -/
theorem sum_tail_eq (J : ℕ) :
    ∑ e ∈ Icc 9 (J + 8), ((e : ℝ) - 5) ^ 2 / 4 ^ (e - 2) =
      173 / 110592 - (((J : ℝ) + 3) ^ 2 / 3 + 8 * ((J : ℝ) + 3) / 9 + 20 / 27) / (64 * 4 ^ (J + 3)) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [show J + 1 + 8 = (J + 8) + 1 by ring, sum_Icc_succ_top (by omega), ih]
    rw [show J + 8 + 1 - 2 = J + 7 by omega]
    push_cast
    rw [show J + 1 + 3 = (J + 3) + 1 by ring, pow_succ, show J + 7 = (J + 3) + 4 by ring, pow_add]
    field_simp
    ring

theorem sum_tail_le (Q : ℕ) :
    ∑ e ∈ Icc 9 Q, ((e : ℝ) - 5) ^ 2 / 4 ^ (e - 2) ≤ 173 / 110592 := by
  rcases le_or_gt Q 8 with hQ | hQ
  · rw [Icc_eq_empty (by omega), sum_empty]; norm_num
  · obtain ⟨J, rfl⟩ : ∃ J, Q = J + 8 := ⟨Q - 8, by omega⟩
    rw [sum_tail_eq]
    have : 0 ≤ (((J : ℝ) + 3) ^ 2 / 3 + 8 * ((J : ℝ) + 3) / 9 + 20 / 27) / (64 * 4 ^ (J + 3)) := by
      positivity
    linarith

/-! ### The term `t = 4` of `F(2^q - q + 2, q + 2)` -/

/-- The `e`-th cosine factor at `t = 4`, which does not depend on `q`:
`cos²(4π(5 - e)/2^e) = cos²(π(e - 5)/2^{e-2})`. -/
noncomputable def resFactor (e : ℕ) : ℝ := cos (π * (4 * (5 - (e : ℝ)) / 2 ^ e)) ^ 2

theorem resFactor_eq {q e : ℕ} (hq : 6 ≤ q) (he : e ≤ q + 2) :
    cos (π * ((4 : ℤ) : ℝ) * ((2 ^ q - q + 2 + (q + 2) + 1 - e : ℕ) : ℝ) / 2 ^ e) ^ 2 =
      resFactor e := by
  have hqle : q < 2 ^ q := Nat.lt_two_pow_self
  have h64 := sixtyfour_le_two_pow hq
  have hnat : 2 ^ q - q + 2 + (q + 2) + 1 - e = 2 ^ q + 5 - e := by omega
  rw [hnat]
  have hcast : ((2 ^ q + 5 - e : ℕ) : ℝ) = 2 ^ q + 5 - e := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have harg : π * ((4 : ℤ) : ℝ) * ((2 ^ q + 5 - e : ℕ) : ℝ) / 2 ^ e =
      π * (4 * (5 - (e : ℝ)) / 2 ^ e + ((2 ^ (q + 2 - e) : ℕ) : ℤ)) := by
    rw [hcast]
    have hp : (2 : ℝ) ^ (q + 2) = 2 ^ (q + 2 - e) * 2 ^ e := by
      rw [← pow_add]; congr 1; omega
    push_cast
    have hp' : (2 : ℝ) ^ q * 4 = 2 ^ (q + 2 - e) * 2 ^ e := by
      rw [← hp, pow_add]; norm_num
    field_simp
    linear_combination hp'
  rw [harg, cos_sq_pi_mul_add_int]
  rfl

theorem resFactor_int {e : ℕ} {n : ℤ} (h : 4 * (5 - (e : ℝ)) / 2 ^ e = n) : resFactor e = 1 := by
  unfold resFactor
  rw [h, show π * (n : ℝ) = π * (0 + n) by ring, cos_sq_pi_mul_add_int, mul_zero, cos_zero, one_pow]

theorem prod_resFactor_one_five : ∏ e ∈ Icc 1 5, resFactor e = 1 / 2 := by
  have h1 : resFactor 1 = 1 := resFactor_int (n := 8) (by norm_num)
  have h2 : resFactor 2 = 1 := resFactor_int (n := 3) (by norm_num)
  have h3 : resFactor 3 = 1 := resFactor_int (n := 1) (by norm_num)
  have h5 : resFactor 5 = 1 := resFactor_int (n := 0) (by norm_num)
  have h4 : resFactor 4 = 1 / 2 := by
    unfold resFactor
    rw [show π * (4 * (5 - ((4 : ℕ) : ℝ)) / 2 ^ 4) = π / 4 by norm_num; ring, cos_pi_div_four,
      div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [show Icc 1 5 = {1, 2, 3, 4, 5} by rfl]
  simp [h1, h2, h3, h4, h5]

theorem resFactor_nonneg (e : ℕ) : 0 ≤ resFactor e := sq_nonneg _

theorem resFactor_le_one (e : ℕ) : resFactor e ≤ 1 := by
  unfold resFactor; rw [sq_le_one_iff_abs_le_one]; exact abs_cos_le_one _

theorem resFactor_six : resFactor 6 = cos (π / 16) ^ 2 := by
  unfold resFactor
  rw [show π * (4 * (5 - ((6 : ℕ) : ℝ)) / 2 ^ 6) = -(π / 16) by norm_num; ring, cos_neg]

theorem resFactor_seven : resFactor 7 = cos (π / 16) ^ 2 := by
  unfold resFactor
  rw [show π * (4 * (5 - ((7 : ℕ) : ℝ)) / 2 ^ 7) = -(π / 16) by norm_num; ring, cos_neg]

theorem resFactor_eight : resFactor 8 = cos (3 * π / 64) ^ 2 := by
  unfold resFactor
  rw [show π * (4 * (5 - ((8 : ℕ) : ℝ)) / 2 ^ 8) = -(3 * π / 64) by norm_num; ring, cos_neg]

/-- The tail `∏_{e=9}^{Q}` of the factors is at least `1 - 173π²/110592`. -/
theorem prod_resFactor_tail (Q : ℕ) :
    1 - π ^ 2 * (173 / 110592) ≤ ∏ e ∈ Icc 9 Q, resFactor e := by
  have h := one_sub_sum_sq_le_prod_cos_sq (Icc 9 Q) (fun e => π * (4 * (5 - (e : ℝ)) / 2 ^ e))
  have hsum : ∑ e ∈ Icc 9 Q, (π * (4 * (5 - (e : ℝ)) / 2 ^ e)) ^ 2 =
      π ^ 2 * ∑ e ∈ Icc 9 Q, ((e : ℝ) - 5) ^ 2 / 4 ^ (e - 2) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun e he => ?_
    have he' : 2 ≤ e := by have := (mem_Icc.mp he).1; omega
    have hp : (4 : ℝ) ^ e = 16 * 4 ^ (e - 2) := by
      rw [show e = (e - 2) + 2 by omega, pow_add]; norm_num; ring
    have hp2 : ((2 : ℝ) ^ e) ^ 2 = 4 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, div_pow, hp2, hp]
    field_simp
    ring
  rw [hsum] at h
  have hle := sum_tail_le Q
  have hpi : 0 ≤ π ^ 2 := sq_nonneg _
  unfold resFactor
  nlinarith

/-- `∏_{e=6}^{Q} resFactor e ≥ cos⁴(π/16) cos²(3π/64) (1 - 173π²/110592)` for `Q ≥ 8`. -/
theorem prod_resFactor_six {Q : ℕ} (hQ : 8 ≤ Q) :
    cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 * (1 - π ^ 2 * (173 / 110592)) ≤
      ∏ e ∈ Icc 6 Q, resFactor e := by
  have hsplit : Icc 6 Q = {6, 7, 8} ∪ Icc 9 Q := by
    ext x; simp only [mem_Icc, mem_union, mem_insert, mem_singleton]; omega
  have hdisj : Disjoint ({6, 7, 8} : Finset ℕ) (Icc 9 Q) := by
    rw [Finset.disjoint_left]; intro x hx; simp only [mem_insert, mem_singleton] at hx
    simp only [mem_Icc]; omega
  rw [hsplit, prod_union hdisj]
  simp only [prod_insert (show (6 : ℕ) ∉ ({7, 8} : Finset ℕ) by decide),
    prod_insert (show (7 : ℕ) ∉ ({8} : Finset ℕ) by decide), prod_singleton]
  rw [resFactor_six, resFactor_seven, resFactor_eight]
  have ht := prod_resFactor_tail Q
  have h1 : 0 ≤ cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 := by positivity
  calc cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 * (1 - π ^ 2 * (173 / 110592))
      ≤ cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 * ∏ e ∈ Icc 9 Q, resFactor e :=
        mul_le_mul_of_nonneg_left ht h1
    _ = _ := by ring

theorem fineFloorTerm_neg (n D : ℕ) (t : ℤ) : fineFloorTerm n D (-t) = fineFloorTerm n D t := by
  unfold fineFloorTerm
  congr 1
  · congr 1
    rw [show π * (((-t : ℤ) : ℝ) * (n : ℝ) / 2 ^ (D + 2)) = -(π * ((t : ℝ) * n / 2 ^ (D + 2))) by
      push_cast; ring, Real.sinc_neg]
  · refine prod_congr rfl fun e _ => ?_
    rw [show π * ((-t : ℤ) : ℝ) * ((n + D + 1 - e : ℕ) : ℝ) / 2 ^ e =
      -(π * (t : ℝ) * ((n + D + 1 - e : ℕ) : ℝ) / 2 ^ e) by push_cast; ring, cos_neg]

/-- `F(n, D) ≥ 2 · (term t)` for every `t ≠ 0` (the terms `t` and `-t` are equal). -/
theorem two_mul_fineFloorTerm_le {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) {t : ℤ} (ht : t ≠ 0) :
    2 * fineFloorTerm n D t ≤ fineFloor n D := by
  have hs := summable_fineFloorTerm hn hD
  have h := hs.sum_le_tsum {t, -t} (fun i _ => by
    split_ifs
    · exact le_rfl
    · exact fineFloorTerm_nonneg _ _ _)
  rw [sum_pair (show t ≠ -t by omega)] at h
  simp only [ht, neg_eq_zero, ↓reduceIte, fineFloorTerm_neg] at h
  unfold fineFloor; linarith

/-- The term `t = 4` of `F(2^q - q + 2, q + 2)`: the cosine factors are `resFactor e`, those with
`e ≤ 5` multiply to `1/2`. -/
theorem fineFloorTerm_resonance {q : ℕ} (hq : 6 ≤ q) :
    fineFloorTerm (2 ^ q - q + 2) (q + 2) 4 =
      Real.sinc (π * (((4 : ℤ) : ℝ) * ((2 ^ q - q + 2 : ℕ) : ℝ) / 2 ^ (q + 2 + 2))) ^ 4 *
        (1 / 2 * ∏ e ∈ Icc 6 (q + 2), resFactor e) := by
  unfold fineFloorTerm
  congr 1
  rw [prod_congr rfl fun e he => resFactor_eq hq (mem_Icc.mp he).2]
  have hsplit : Icc 1 (q + 2) = Icc 1 5 ∪ Icc 6 (q + 2) := by
    ext x; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 5) (Icc 6 (q + 2)) := by
    rw [Finset.disjoint_left]; intro x hx hx'; simp only [mem_Icc] at hx hx'; omega
  rw [hsplit, prod_union hdisj, prod_resFactor_one_five]

/-- The sinc factor of the resonant term is at least `64/π⁴`. -/
theorem sinc_resonance_ge {q : ℕ} (hq : 6 ≤ q) :
    64 / π ^ 4 ≤ Real.sinc (π * (((4 : ℤ) : ℝ) * ((2 ^ q - q + 2 : ℕ) : ℝ) / 2 ^ (q + 2 + 2))) ^ 4 := by
  have hqle : q < 2 ^ q := Nat.lt_two_pow_self
  apply sinc_pow_four_ge
  · have : (0 : ℝ) < ((2 ^ q - q + 2 : ℕ) : ℝ) := by positivity
    positivity
  · have hn : ((2 ^ q - q + 2 : ℕ) : ℝ) ≤ 2 ^ q := by
      have : 2 ^ q - q + 2 ≤ 2 ^ q := by omega
      exact_mod_cast this
    have h4 : (((4 : ℤ) : ℝ)) = 4 := by norm_num
    rw [h4, div_le_iff₀ (by positivity), show q + 2 + 2 = q + 4 by ring, pow_add]
    nlinarith

/-- Numerical lower bounds for the constants. -/
theorem resonance_constants :
    (0.585 : ℝ) < 64 / π ^ 4 * (cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 *
      (1 - π ^ 2 * (173 / 110592))) := by
  have hpi : π < 3.141593 := pi_lt_d6
  have hpi0 : 3 < π := pi_gt_three
  have hA : (0.657022 : ℝ) ≤ 64 / π ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    have h4 : π ^ 4 ≤ 3.141593 ^ 4 := pow_le_pow_left₀ (by linarith) hpi.le 4
    nlinarith
  have hC1 : (0.96193975 : ℝ) ≤ cos (π / 16) ^ 2 := by
    rw [cos_sq, show 2 * (π / 16) = π / 8 by ring, cos_pi_div_eight]
    have h2 : (1.41421356 : ℝ) ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h3 : (1.847759 : ℝ) ≤ √(2 + √2) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
    linarith
  have hC2 : (0.9784 : ℝ) ≤ cos (3 * π / 64) ^ 2 := by
    have h := one_sub_sq_div_two_le_cos (x := 3 * π / 64)
    have hx : 3 * π / 64 ≤ 0.1472624 := by linarith
    have hx0 : 0 ≤ 3 * π / 64 := by linarith
    have hsq : (3 * π / 64) ^ 2 ≤ 0.1472624 ^ 2 := pow_le_pow_left₀ hx0 hx 2
    have hpos : (0.98915 : ℝ) ≤ 1 - (3 * π / 64) ^ 2 / 2 := by nlinarith
    have : (1 - (3 * π / 64) ^ 2 / 2) ^ 2 ≤ cos (3 * π / 64) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h 2
    nlinarith
  have hT : (0.98456 : ℝ) ≤ 1 - π ^ 2 * (173 / 110592) := by nlinarith
  calc (0.585 : ℝ) < 0.657022 * (0.96193975 * 0.96193975 * 0.9784 * 0.98456) := by norm_num
    _ ≤ 64 / π ^ 4 * (cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 *
      (1 - π ^ 2 * (173 / 110592))) := by gcongr

/-- **`F(2^q - q + 2, q + 2) > 0.585`** for every `q ≥ 6` (even or odd). -/
theorem fineFloor_resonance_gt {q : ℕ} (hq : 6 ≤ q) :
    (0.585 : ℝ) < fineFloor (2 ^ q - q + 2) (q + 2) := by
  have hqle : q < 2 ^ q := Nat.lt_two_pow_self
  have h2 := two_mul_fineFloorTerm_le (n := 2 ^ q - q + 2) (D := q + 2) (by omega) (by omega)
    (t := 4) (by norm_num)
  rw [fineFloorTerm_resonance hq] at h2
  have hs := sinc_resonance_ge hq
  have hp := prod_resFactor_six (Q := q + 2) (by omega)
  have hc := resonance_constants
  have hT : 0 ≤ 1 - π ^ 2 * (173 / 110592) := by nlinarith [pi_lt_d6, pi_gt_three]
  have hB : 0 ≤ cos (π / 16) ^ 2 * cos (π / 16) ^ 2 * cos (3 * π / 64) ^ 2 *
      (1 - π ^ 2 * (173 / 110592)) := by positivity
  have hsinc0 : 0 ≤ 64 / π ^ 4 := by positivity
  have := mul_le_mul hs hp hB (by positivity)
  have e : 2 * (Real.sinc (π * (((4 : ℤ) : ℝ) * ((2 ^ q - q + 2 : ℕ) : ℝ) / 2 ^ (q + 2 + 2))) ^ 4 *
      (1 / 2 * ∏ e ∈ Icc 6 (q + 2), resFactor e)) =
      Real.sinc (π * (((4 : ℤ) : ℝ) * ((2 ^ q - q + 2 : ℕ) : ℝ) / 2 ^ (q + 2 + 2))) ^ 4 *
      ∏ e ∈ Icc 6 (q + 2), resFactor e := by ring
  rw [e] at h2
  linarith

/-- **Proposition 7.13** (with the constant `0.585` in place of `0.551`). Let `a = 1`, `q ≥ 6`
even, `k ≥ 1` with `3k ≤ 2^q + 4`, and `m = 2^q + k + 3`. Then `k ∈ 𝒦`, `κ_1(k) = k + q + 2`,
`n_{κ_1(k)} = 2^q - q + 2`, and `V^{(1)}_k ≥ F_k > 0.585`. -/
theorem resonance_class {q k : ℕ} (hq : 6 ≤ q) (hqe : Even q) (hk : 1 ≤ k)
    (hk3 : 3 * k ≤ 2 ^ q + 4) :
    k ∈ coarseZone (2 ^ q + k + 3) ∧
    cancellerBelow (2 ^ q + k + 3) 1 k = k + q + 2 ∧
    (2 ^ q + k + 3) - cancellerBelow (2 ^ q + k + 3) 1 k + 1 = 2 ^ q - q + 2 ∧
    fineFloorK (2 ^ q + k + 3) k (cancellerBelow (2 ^ q + k + 3) 1 k) ≤
      relVarianceA (2 ^ q + k + 3) 1 k ∧
    (0.585 : ℝ) < fineFloorK (2 ^ q + k + 3) k (cancellerBelow (2 ^ q + k + 3) 1 k) := by
  have hκ := cancellerBelow_resonance hq hqe hk3
  have hqle : q < 2 ^ q := Nat.lt_two_pow_self
  refine ⟨coarseZone_resonance hk hk3, hκ, by omega, ?_, ?_⟩
  · unfold relVarianceA; rw [hκ]; exact fineFloorK_le_relVariance hk (by omega)
  · rw [hκ, fineFloorK_eq hk (by omega) (by omega),
      show 2 ^ q + k + 3 - (k + q + 2) + 1 = 2 ^ q - q + 2 by omega,
      show k + q + 2 - k = q + 2 by omega]
    exact fineFloor_resonance_gt hq

/-- **Proposition 7.13** as stated: `V^{(1)}_k ≥ F_k > 0.551`. -/
theorem resonance_class_paper {q k : ℕ} (hq : 6 ≤ q) (hqe : Even q) (hk : 1 ≤ k)
    (hk3 : 3 * k ≤ 2 ^ q + 4) :
    k ∈ coarseZone (2 ^ q + k + 3) ∧
    cancellerBelow (2 ^ q + k + 3) 1 k = k + q + 2 ∧
    (2 ^ q + k + 3) - cancellerBelow (2 ^ q + k + 3) 1 k + 1 = 2 ^ q - q + 2 ∧
    fineFloorK (2 ^ q + k + 3) k (cancellerBelow (2 ^ q + k + 3) 1 k) ≤
      relVarianceA (2 ^ q + k + 3) 1 k ∧
    (0.551 : ℝ) < fineFloorK (2 ^ q + k + 3) k (cancellerBelow (2 ^ q + k + 3) 1 k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := resonance_class hq hqe hk hk3
  exact ⟨h1, h2, h3, h4, by linarith⟩

end MergeDepth
