import MergeDepth.SkeletonWalk

/-!
# Few coarse walks (Lemma 4.14)

* `sum_choose_le`: `∑_{i ≤ m} C(n, i) ≤ (e n / m)^m` for `1 ≤ m ≤ n`.
* `rpow_mono_of_le`: `y ↦ (A e / y)^y` increases on `(0, A]`.
* `card_coarse_le`: Lemma 4.14(a). The coarse walks `⌊x/w⌋` on `[0, T)` of walks `x` with
  `x 0 = 0` that enter every cell at most `V` times are at most `(e w / V)^{m₁}` in number,
  `m₁ = 2V(T/w + 2)`, for `w ≥ 4V` and `T ≥ 16V`.
* `card_monotone_le`: Lemma 4.14(b). The maps `s` on `[0, T)` with `s 0 = 0`, steps in `{0, 1}`
  and `s (T - 1) ≤ m` are at most `(e T / y)^y` in number for `m ≤ y ≤ T`.

A walk with unit steps and `s 0 = 0` is determined by its set of change times and the set of its
up-steps (`changes`, `ups`), so the count is a sum of binomial coefficients times powers of two.
-/

namespace MergeDepth

open Finset BoundedNesting Real

/-! ### Binomial sums -/

/-- `∑_{i ≤ m} C(n, i) ≤ (e n / m)^m` for `1 ≤ m ≤ n`. -/
theorem sum_choose_le {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ i ∈ range (m + 1), (n.choose i : ℝ)) ≤ (exp 1 * n / m) ^ m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set p : ℝ := m / n with hp
  have hp0 : 0 < p := div_pos hm' hn'
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hn']; exact_mod_cast hmn
  -- `∑_{i ≤ m} C(n,i) p^m ≤ ∑_{i ≤ n} C(n,i) p^i = (1 + p)^n ≤ e^{pn} = e^m`
  have h1 : (∑ i ∈ range (m + 1), (n.choose i : ℝ)) * p ^ m ≤
      ∑ i ∈ range (n + 1), p ^ i * (n.choose i : ℝ) := by
    rw [sum_mul]
    calc ∑ i ∈ range (m + 1), (n.choose i : ℝ) * p ^ m
        ≤ ∑ i ∈ range (m + 1), p ^ i * (n.choose i : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          rw [mul_comm]
          have hi' : i ≤ m := by simp at hi; omega
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hp0.le hp1 hi') (by positivity)
      _ ≤ ∑ i ∈ range (n + 1), p ^ i * (n.choose i : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
            (fun _ _ _ => by positivity)
  have h2 : ∑ i ∈ range (n + 1), p ^ i * (n.choose i : ℝ) = (p + 1) ^ n := by
    rw [add_pow]
    simp
  have h3 : (p + 1) ^ n ≤ exp m := by
    calc (p + 1) ^ n ≤ (exp p) ^ n := pow_le_pow_left₀ (by positivity) (add_one_le_exp p) n
      _ = exp (p * n) := by rw [← exp_nat_mul]; ring_nf
      _ = exp m := by rw [hp, div_mul_cancel₀ _ hn'.ne']
  have h4 : (∑ i ∈ range (m + 1), (n.choose i : ℝ)) ≤ exp m / p ^ m := by
    rw [le_div_iff₀ (pow_pos hp0 m)]
    linarith
  calc (∑ i ∈ range (m + 1), (n.choose i : ℝ)) ≤ exp m / p ^ m := h4
    _ = (exp 1 * n / m) ^ m := by
        rw [hp, div_pow, div_div_eq_mul_div, mul_div_assoc, ← exp_one_pow, div_pow, mul_pow]
        ring

/-- `y ↦ (A e / y)^y` increases on `(0, A]`. -/
theorem rpow_mono_of_le {A y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hzA : z ≤ A) :
    (A * exp 1 / y) ^ y ≤ (A * exp 1 / z) ^ z := by
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hA : 0 < A := lt_of_lt_of_le hz hzA
  have hb1 : 0 < A * exp 1 / y := by positivity
  have hb2 : 0 < A * exp 1 / z := by positivity
  rw [← exp_log (rpow_pos_of_pos hb1 y), ← exp_log (rpow_pos_of_pos hb2 z), exp_le_exp,
    log_rpow hb1, log_rpow hb2]
  -- `y log(Ae/y) ≤ z log(Ae/z)`, using `y log(z/y) ≤ z - y` and `log(A/z) ≥ 0`
  have hlog1 : log (A * exp 1 / y) = log A + 1 - log y := by
    rw [log_div (by positivity) hy.ne', log_mul hA.ne' (exp_pos 1).ne', log_exp]
  have hlog2 : log (A * exp 1 / z) = log A + 1 - log z := by
    rw [log_div (by positivity) hz.ne', log_mul hA.ne' (exp_pos 1).ne', log_exp]
  rw [hlog1, hlog2]
  have h1 : log (z / y) ≤ z / y - 1 := log_le_sub_one_of_pos (div_pos hz hy)
  have h1' : y * log (z / y) ≤ z - y := by
    have := mul_le_mul_of_nonneg_left h1 hy.le
    rwa [mul_sub, mul_div_cancel₀ _ hy.ne', mul_one] at this
  have h2 : log (z / y) = log z - log y := log_div hz.ne' hy.ne'
  have h3 : 0 ≤ log A - log z := by
    have := log_le_log hz hzA
    linarith
  nlinarith

/-! ### Encoding walks with unit steps -/

/-- The change times of `s` in `[1, T)`. -/
def changes (s : ℕ → ℤ) (T : ℕ) : Finset ℕ := (Ico 1 T).filter fun t => s t ≠ s (t - 1)

/-- The up-steps of `s` in `[1, T)`. -/
def ups (s : ℕ → ℤ) (T : ℕ) : Finset ℕ := (Ico 1 T).filter fun t => s t = s (t - 1) + 1

/-- A unit-step map with `s 0 = 0` is determined on `[0, T)` by its changes and up-steps. -/
theorem eq_of_changes_ups {s s' : ℕ → ℤ} {T : ℕ} (h0 : s 0 = 0) (h0' : s' 0 = 0)
    (hs : ∀ t, t + 1 < T → |s (t + 1) - s t| ≤ 1) (hs' : ∀ t, t + 1 < T → |s' (t + 1) - s' t| ≤ 1)
    (hc : changes s T = changes s' T) (hu : ups s T = ups s' T) : ∀ t < T, s t = s' t := by
  intro t ht
  induction t with
  | zero => rw [h0, h0']
  | succ t ih =>
    have ih' := ih (by omega)
    have h1 := abs_le.mp (hs t ht)
    have h2 := abs_le.mp (hs' t ht)
    have hmemc : (t + 1 ∈ changes s T) ↔ (t + 1 ∈ changes s' T) := by rw [hc]
    have hmemu : (t + 1 ∈ ups s T) ↔ (t + 1 ∈ ups s' T) := by rw [hu]
    simp only [changes, ups, mem_filter, mem_Ico, Nat.add_sub_cancel] at hmemc hmemu
    have hT : 1 ≤ t + 1 ∧ t + 1 < T := ⟨by omega, ht⟩
    simp only [hT, true_and] at hmemc hmemu
    rw [ih'] at hmemc hmemu h1
    by_cases hch : s (t + 1) = s' t
    · have : s' (t + 1) = s' t := by
        by_contra hne
        exact (hmemc.mpr hne) hch
      rw [hch, this]
    · have hch' : s' (t + 1) ≠ s' t := hmemc.mp hch
      by_cases hup : s (t + 1) = s' t + 1
      · rw [hup, hmemu.mp hup]
      · have hup' : s' (t + 1) ≠ s' t + 1 := fun h => hup (hmemu.mpr h)
        omega

/-- Pairs `(C, U)` with `U ⊆ C ⊆ [1, T)` and `|C| ≤ m₀` number at most `∑_{i ≤ m₀} C(T - 1, i) 2^i`. -/
theorem card_pairs_le (T m₀ : ℕ) :
    (((Ico 1 T).powerset.filter fun C => C.card ≤ m₀).sigma fun C => C.powerset).card =
      ∑ i ∈ range (m₀ + 1), (T - 1).choose i * 2 ^ i := by
  classical
  rw [card_sigma]
  simp only [card_powerset]
  rw [show (Ico 1 T).powerset.filter (fun C => C.card ≤ m₀) =
      (range (m₀ + 1)).biUnion fun i => (Ico 1 T).powersetCard i by
    ext C
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨C.card, by omega, h1, rfl⟩
    · rintro ⟨i, hi, h1, rfl⟩; exact ⟨h1, by omega⟩]
  rw [sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_congr rfl fun C hC => by rw [(mem_powersetCard.mp hC).2], sum_const,
      card_powersetCard, Nat.card_Ico, smul_eq_mul]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [disjoint_left]
    intro C h1 h2
    exact hij ((mem_powersetCard.mp h1).2.symm.trans (mem_powersetCard.mp h2).2)

/-- The extension by zero of a map on `[0, T)`. -/
def ext0 {T : ℕ} (σ : Fin T → ℤ) : ℕ → ℤ := fun t => if h : t < T then σ ⟨t, h⟩ else 0

theorem ext0_apply {T : ℕ} (σ : Fin T → ℤ) (t : Fin T) : ext0 σ t = σ t := by simp [ext0]

theorem ups_subset_changes (s : ℕ → ℤ) (T : ℕ) : ups s T ⊆ changes s T := fun t ht => by
  obtain ⟨h1, h2⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨h1, by omega⟩

/-- Unit-step maps on `[0, T)` with `s 0 = 0` and at most `m₀` changes number at most
`∑_{i ≤ m₀} C(T - 1, i) 2^i`. -/
theorem card_unit_le {T m₀ : ℕ} (S : Finset (Fin T → ℤ))
    (hS : ∀ σ ∈ S, ext0 σ 0 = 0 ∧ (∀ t, t + 1 < T → |ext0 σ (t + 1) - ext0 σ t| ≤ 1) ∧
      (changes (ext0 σ) T).card ≤ m₀) :
    S.card ≤ ∑ i ∈ range (m₀ + 1), (T - 1).choose i * 2 ^ i := by
  classical
  rw [← card_pairs_le]
  let enc : (Fin T → ℤ) → (Σ _ : Finset ℕ, Finset ℕ) := fun σ =>
    ⟨changes (ext0 σ) T, ups (ext0 σ) T⟩
  refine card_le_card_of_injOn enc (fun σ hσ => ?_) (fun σ hσ σ' hσ' he => ?_)
  · obtain ⟨-, -, hc⟩ := hS σ hσ
    refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), hc⟩,
      mem_powerset.mpr (ups_subset_changes _ _)⟩
  · obtain ⟨h0, hs, -⟩ := hS σ hσ
    obtain ⟨h0', hs', -⟩ := hS σ' hσ'
    simp only [enc, Sigma.mk.injEq, heq_eq_eq] at he
    funext t
    have := eq_of_changes_ups h0 h0' hs hs' he.1 he.2 t t.2
    rwa [ext0_apply, ext0_apply] at this

/-- **Lemma 4.14(a).** -/
theorem card_coarse_le {V w T : ℕ} (hV : 1 ≤ V) (hw : 4 * V ≤ w) (hT : 16 * V ≤ T)
    (S : Finset (Fin T → ℤ))
    (hS : ∀ σ ∈ S, ∃ x : ℕ → ℤ, IsWalk x ∧ x 0 = 0 ∧ (∀ c, (entries x c (T - 1)).card ≤ V) ∧
      ∀ t : Fin T, σ t = x t / w) :
    (S.card : ℝ) ≤ (exp 1 * w / V) ^ ((2 * V * (T / w + 2) : ℝ)) := by
  have hw0 : 0 < w := by omega
  have hwz : (0 : ℤ) < w := by exact_mod_cast hw0
  set q := (T - 1) / w
  set m₀ := 2 * V * (q + 2) - 1
  -- the coarse walks have unit steps and at most `m₀` changes
  have hS' : ∀ σ ∈ S, ext0 σ 0 = 0 ∧ (∀ t, t + 1 < T → |ext0 σ (t + 1) - ext0 σ t| ≤ 1) ∧
      (changes (ext0 σ) T).card ≤ m₀ := by
    intro σ hσ
    obtain ⟨x, hx, h0, hV', hσx⟩ := hS σ hσ
    have hT1 : 1 ≤ T := by omega
    have heq : ∀ t, t < T → ext0 σ t = skel w x t := fun t ht => by
      simp only [ext0, ht, ↓reduceDIte, hσx, skel]
    refine ⟨by rw [heq 0 (by omega)]; simp [skel, h0], fun t ht => ?_, ?_⟩
    · rw [heq t (by omega), heq (t + 1) ht]
      exact isWalk_skel hwz hx t
    · have hcount := card_block_changes_le hw0 hx h0 hT1 hV'
      have hsub : changes (ext0 σ) T =
          (Ico 1 T).filter fun t => skel w x t ≠ skel w x (t - 1) := by
        refine filter_congr fun t ht => ?_
        obtain ⟨h1, h2⟩ := mem_Ico.mp ht
        rw [heq t h2, heq (t - 1) (by omega)]
      rw [hsub]
      exact hcount
  have hcard := card_unit_le S hS'
  -- the numerical bounds on `m₀`
  have hq : 4 * V * q ≤ T - 1 := by
    calc 4 * V * q ≤ w * q := Nat.mul_le_mul_right _ hw
      _ ≤ T - 1 := Nat.mul_div_le (T - 1) w
  have e : 2 * V * (q + 2) = 2 * (V * q) + 4 * V := by ring
  have hq' : 4 * (V * q) ≤ T - 1 := by linarith [hq, show 4 * V * q = 4 * (V * q) by ring]
  have hm₀1 : 1 ≤ m₀ := by simp only [m₀]; omega
  have hm₀T : m₀ ≤ T - 1 := by simp only [m₀]; omega
  have hsum := sum_choose_le hm₀1 hm₀T
  -- `∑_{i ≤ m₀} C(T - 1, i) 2^i ≤ 2^{m₀} ∑_{i ≤ m₀} C(T - 1, i)`
  have h2 : ((∑ i ∈ range (m₀ + 1), (T - 1).choose i * 2 ^ i : ℕ) : ℝ) ≤
      2 ^ m₀ * ∑ i ∈ range (m₀ + 1), ((T - 1).choose i : ℝ) := by
    push_cast
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [mul_comm]
    have : (2 : ℝ) ^ i ≤ 2 ^ m₀ := pow_le_pow_right₀ (by norm_num) (by simp at hi; omega)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hm₀pos : (0 : ℝ) < m₀ := by exact_mod_cast hm₀1
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw0
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  set m₁ : ℝ := 2 * V * (T / w + 2)
  -- `m₀ ≤ m₁ ≤ 2T`
  have hqr : (q : ℝ) ≤ (T - 1 : ℕ) / w := by
    rw [le_div_iff₀ hwr]
    have := Nat.div_mul_le_self (T - 1) w
    exact_mod_cast this
  have hTsub : ((T - 1 : ℕ) : ℝ) = T - 1 := by push_cast [show 1 ≤ T by omega]; ring
  have hm₀m₁ : (m₀ : ℝ) ≤ m₁ := by
    have : (m₀ : ℝ) ≤ 2 * V * (q + 2) := by
      have : m₀ ≤ 2 * V * (q + 2) := Nat.sub_le _ _
      exact_mod_cast this
    have hTw : (T - 1 : ℝ) / w ≤ T / w := div_le_div_of_nonneg_right (by linarith) hwr.le
    rw [hTsub] at hqr
    simp only [m₁]
    nlinarith
  have hm₁T : m₁ ≤ 2 * T := by
    have hw' : (4 * V : ℝ) ≤ w := by exact_mod_cast hw
    have hT' : (16 * V : ℝ) ≤ T := by exact_mod_cast hT
    have : (2 * V * (T / w) : ℝ) ≤ T / 2 := by
      rw [show (2 * V * (T / w) : ℝ) = (2 * V * T) / w by ring, div_le_iff₀ hwr]
      nlinarith
    simp only [m₁]
    nlinarith
  calc (S.card : ℝ) ≤ ((∑ i ∈ range (m₀ + 1), (T - 1).choose i * 2 ^ i : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ 2 ^ m₀ * ∑ i ∈ range (m₀ + 1), ((T - 1).choose i : ℝ) := h2
    _ ≤ 2 ^ m₀ * (exp 1 * (T - 1 : ℕ) / m₀) ^ m₀ := by gcongr
    _ ≤ 2 ^ m₀ * (exp 1 * T / m₀) ^ m₀ := by
        gcongr
        exact_mod_cast Nat.sub_le T 1
    _ = ((2 * T) * exp 1 / m₀) ^ (m₀ : ℝ) := by
        rw [Real.rpow_natCast, ← mul_pow]; ring_nf
    _ ≤ ((2 * T) * exp 1 / m₁) ^ m₁ := rpow_mono_of_le hm₀pos hm₀m₁ hm₁T
    _ ≤ (exp 1 * w / V) ^ m₁ := by
        have hm₁pos : 0 < m₁ := lt_of_lt_of_le hm₀pos hm₀m₁
        refine Real.rpow_le_rpow (by positivity) ?_ hm₁pos.le
        rw [div_le_div_iff₀ hm₁pos (by positivity)]
        simp only [m₁]
        have : (2 * T : ℝ) * V ≤ 2 * V * (T / w + 2) * w := by
          rw [show 2 * (V : ℝ) * (T / w + 2) * w = 2 * V * T + 4 * V * w by field_simp; ring]
          nlinarith
        nlinarith [exp_pos 1]

/-- A map with steps in `{0, 1}` counts its up-steps. -/
theorem eq_card_ups {s : ℕ → ℤ} {T : ℕ} (h0 : s 0 = 0)
    (hs : ∀ t, t + 1 < T → s (t + 1) = s t ∨ s (t + 1) = s t + 1) :
    ∀ t < T, s t = ((ups s T).filter (· ≤ t)).card := by
  intro t ht
  induction t with
  | zero =>
    rw [h0]
    have : (ups s T).filter (· ≤ 0) = ∅ := by
      ext u
      simp only [ups, mem_filter, mem_Ico, Finset.notMem_empty, iff_false, not_and, not_le]
      omega
    rw [this]
    simp
  | succ t ih =>
    have ih' := ih (by omega)
    have hsplit : (ups s T).filter (· ≤ t + 1) =
        (if t + 1 ∈ ups s T then insert (t + 1) ((ups s T).filter (· ≤ t))
          else (ups s T).filter (· ≤ t)) := by
      ext u
      by_cases hu : t + 1 ∈ ups s T
      · simp only [hu, ↓reduceIte, mem_insert, mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge u (t + 1) with h | h
          · exact Or.inr ⟨h1, by omega⟩
          · exact Or.inl (by omega)
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hu, le_rfl⟩
          · exact ⟨h1, by omega⟩
      · simp only [hu, ↓reduceIte, mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases Nat.lt_or_ge u (t + 1) with h | h
          · omega
          · have : u = t + 1 := by omega
            subst this; exact absurd h1 hu
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    rw [hsplit]
    have hmem : t + 1 ∈ ups s T ↔ s (t + 1) = s t + 1 := by
      simp only [ups, mem_filter, mem_Ico, Nat.add_sub_cancel]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨by omega, ht⟩, h⟩
    rcases hs t ht with h | h
    · have hn : t + 1 ∉ ups s T := fun hu => by have := hmem.mp hu; omega
      simp only [hn, ↓reduceIte]
      rw [h, ih']
    · have hu : t + 1 ∈ ups s T := hmem.mpr h
      have hnot : t + 1 ∉ (ups s T).filter (· ≤ t) := by simp
      simp only [hu, ↓reduceIte, card_insert_of_notMem hnot]
      rw [h, ih']
      push_cast
      ring

/-- **Lemma 4.14(b).** -/
theorem card_monotone_le {T m : ℕ} (hm : 1 ≤ m) (hmT : m ≤ T - 1) {y : ℝ} (hmy : (m : ℝ) ≤ y)
    (hyT : y ≤ T) (S : Finset (Fin T → ℤ))
    (hS : ∀ σ ∈ S, ext0 σ 0 = 0 ∧
      (∀ t, t + 1 < T → ext0 σ (t + 1) = ext0 σ t ∨ ext0 σ (t + 1) = ext0 σ t + 1) ∧
      ext0 σ (T - 1) ≤ m) :
    (S.card : ℝ) ≤ (exp 1 * T / y) ^ y := by
  classical
  have hT : 2 ≤ T := by omega
  -- encode by the up-steps, of which there are at most `m`
  have hcard : S.card ≤ ∑ i ∈ range (m + 1), (T - 1).choose i := by
    have hpow : ((Ico 1 T).powerset.filter fun C => C.card ≤ m).card =
        ∑ i ∈ range (m + 1), (T - 1).choose i := by
      rw [show (Ico 1 T).powerset.filter (fun C => C.card ≤ m) =
          (range (m + 1)).biUnion fun i => (Ico 1 T).powersetCard i by
        ext C
        simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨C.card, by omega, h1, rfl⟩
        · rintro ⟨i, hi, h1, rfl⟩; exact ⟨h1, by omega⟩]
      rw [card_biUnion]
      · refine sum_congr rfl fun i _ => ?_
        rw [card_powersetCard, Nat.card_Ico]
      · intro i _ j _ hij
        simp only [Function.onFun]
        rw [disjoint_left]
        intro C h1 h2
        exact hij ((mem_powersetCard.mp h1).2.symm.trans (mem_powersetCard.mp h2).2)
    rw [← hpow]
    refine card_le_card_of_injOn (fun σ => ups (ext0 σ) T) (fun σ hσ => ?_)
      (fun σ hσ σ' hσ' he => ?_)
    · obtain ⟨h0, hs, hlast⟩ := hS σ hσ
      have heq := eq_card_ups h0 hs (T - 1) (by omega)
      refine mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), ?_⟩
      have hall : (ups (ext0 σ) T).filter (· ≤ T - 1) = ups (ext0 σ) T := by
        refine filter_true_of_mem fun u hu => ?_
        have := (mem_Ico.mp (mem_filter.mp hu).1).2
        omega
      rw [hall] at heq
      have : ((ups (ext0 σ) T).card : ℤ) ≤ m := by rw [← heq]; exact hlast
      exact_mod_cast this
    · obtain ⟨h0, hs, -⟩ := hS σ hσ
      obtain ⟨h0', hs', -⟩ := hS σ' hσ'
      simp only at he
      have hunit : ∀ (f : ℕ → ℤ), (∀ t, t + 1 < T → f (t + 1) = f t ∨ f (t + 1) = f t + 1) →
          ∀ t, t + 1 < T → |f (t + 1) - f t| ≤ 1 := by
        intro f hf t ht
        rcases hf t ht with h | h <;> rw [h] <;> simp
      have hch : ∀ (f : ℕ → ℤ), (∀ t, t + 1 < T → f (t + 1) = f t ∨ f (t + 1) = f t + 1) →
          changes f T = ups f T := by
        intro f hf
        refine filter_congr fun t ht => ?_
        obtain ⟨h1, h2⟩ := mem_Ico.mp ht
        have := hf (t - 1) (by omega)
        rw [Nat.sub_add_cancel h1] at this
        constructor
        · intro hne; rcases this with h | h
          · exact absurd h hne
          · exact h
        · intro h; omega
      funext t
      have := eq_of_changes_ups h0 h0' (hunit _ hs) (hunit _ hs')
        (by rw [hch _ hs, hch _ hs', he]) he t t.2
      rwa [ext0_apply, ext0_apply] at this
  have hsum := sum_choose_le hm hmT
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  calc (S.card : ℝ) ≤ ((∑ i ∈ range (m + 1), (T - 1).choose i : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ∑ i ∈ range (m + 1), ((T - 1).choose i : ℝ) := by push_cast; rfl
    _ ≤ (exp 1 * (T - 1 : ℕ) / m) ^ m := hsum
    _ ≤ (exp 1 * T / m) ^ m := by
        gcongr
        exact_mod_cast Nat.sub_le T 1
    _ = (T * exp 1 / m) ^ (m : ℝ) := by rw [Real.rpow_natCast]; ring_nf
    _ ≤ (T * exp 1 / y) ^ y := rpow_mono_of_le hmpos hmy hyT
    _ = (exp 1 * T / y) ^ y := by ring_nf

end MergeDepth
