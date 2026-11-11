import AdaptiveTransfer.CarrierBudgetRates

/-! Exact reference and historical-cache bills. Every finite field in the
written compiler is included here; these estimates do not construct that
compiler or assume its final state-bit budget. -/

namespace AdaptiveTransfer
open LeanMachine Finset

def referenceHashMultiplier (k ell T : ℕ) : ℕ := 2 * k * (T + 1) * ell

def referenceHashBits (k ell a T s : ℕ) : ℕ :=
  Nat.clog 2 (referenceHashMultiplier k ell T * blockSparseMenu (2 * T + 1) a s)

def referencePolynomial (k ell a P T : ℕ) : ℕ :=
  let n := 2 * T + 1
  k * (T + 1) * n ^ (k + 2) * (4 * T + 1) * (1 + n ^ 2) *
    (1 + T * (P + 1) ^ 2 * ell * n * 2 ^ a)

def referenceOverhead (k ell a P T s : ℕ) : ℕ :=
  let n := 2 * T + 1
  k * (T + 1) * n ^ (k + 2) * (4 * T + 1) * (1 + n ^ 2) *
    (1 + T * (P + 1) ^ 2 * ell * blockSparseMenu n a s * n * 2 ^ a)

def cacheOverhead (k ell P T : ℕ) : ℕ :=
  let n := 2 * T + 1
  k * (T + 1) * n ^ (k + 2) * (4 * T + 1) * (1 + n ^ 2) *
    (1 + (T + 1) * (P + 1) ^ 2 * ell) ^ k

def referenceStateBound (k ell a P T Q U s : ℕ) : ℕ :=
  2 + Q * U * referenceOverhead k ell a P T s *
    2 ^ (k * (ell + 1) * referenceHashBits k ell a T s)

def cacheStateBound (k ell a P T Q U s M : ℕ) : ℕ :=
  2 + Q * U * cacheOverhead k ell P T * blockSparseMenu (2 * T + 1) a M ^ k *
    2 ^ (k * (ell + 1) * referenceHashBits k ell a T s)

def referenceLabelBits (k ell a T s Z₀ : ℕ) : ℕ :=
  Z₀ + k * ell * referenceHashBits k ell a T s

theorem blockSparseMenu_mono {n a s t : ℕ} (hst : s ≤ t) :
    blockSparseMenu n a s ≤ blockSparseMenu n a t := by
  unfold blockSparseMenu
  apply sum_le_sum_of_subset
  exact range_mono (Nat.add_le_add_right (min_le_min_left n hst) 1)

theorem clog_two_mul_le (m n : ℕ) :
    Nat.clog 2 (m * n) ≤ Nat.clog 2 m + Nat.clog 2 n := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) m) (Nat.le_pow_clog (by decide) n)

theorem referenceHashBits_le (k ell a T s : ℕ) :
    referenceHashBits k ell a T s ≤
      Nat.clog 2 (blockSparseMenu (2 * T + 1) a s) +
        Nat.clog 2 (referenceHashMultiplier k ell T) := by
  exact (clog_two_mul_le _ _).trans_eq (Nat.add_comm _ _)

theorem referenceOverhead_le (k ell a P T s : ℕ) :
    referenceOverhead k ell a P T s ≤
      referencePolynomial k ell a P T * blockSparseMenu (2 * T + 1) a s := by
  have hp := blockSparseMenu_pos (2 * T + 1) a s
  let F := k * (T + 1) * (2 * T + 1) ^ (k + 2) * (4 * T + 1) * (1 + (2 * T + 1) ^ 2)
  let H := T * (P + 1) ^ 2 * ell * (2 * T + 1) * 2 ^ a
  let K := blockSparseMenu (2 * T + 1) a s
  have he : referenceOverhead k ell a P T s = F * (1 + H * K) := by
    dsimp [referenceOverhead, F, H, K]; ring
  rw [he]
  change F * (1 + H * K) ≤ F * (1 + H) * K
  have hh : F * 1 ≤ F * K := Nat.mul_le_mul_left F hp
  nlinarith only [hh]

/-- Both administrative states are paid, even when the product is zero. -/
theorem clog_two_state_product {Q U q u : ℕ} (hQ : Q ≤ 2 ^ q) (hU : U ≤ 2 ^ u)
    (menu bits : ℕ) :
    Nat.clog 2 (2 + Q * U * menu * 2 ^ bits) ≤
      q + u + Nat.clog 2 menu + bits + 2 := by
  apply Nat.clog_le_of_le_pow
  let e := q + u + Nat.clog 2 menu + bits
  have hp : Q * U * menu * 2 ^ bits ≤ 2 ^ e := by
    calc
      _ ≤ 2 ^ q * 2 ^ u * 2 ^ Nat.clog 2 menu * 2 ^ bits := by
        gcongr
        exact Nat.le_pow_clog (by decide) menu
      _ = _ := by dsimp [e]; simp only [pow_add]
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by decide)
  change 2 + Q * U * menu * 2 ^ bits ≤ 2 ^ (e + 2)
  rw [pow_add]
  norm_num
  omega

theorem reference_state_bits_le {k ell a P T Q U s q u : ℕ}
    (hQ : Q ≤ 2 ^ q) (hU : U ≤ 2 ^ u) :
    Nat.clog 2 (referenceStateBound k ell a P T Q U s) ≤ q + u +
      (k * (ell + 1) + 1) * Nat.clog 2 (blockSparseMenu (2 * T + 1) a s) +
      k * (ell + 1) * Nat.clog 2 (referenceHashMultiplier k ell T) +
      Nat.clog 2 (referencePolynomial k ell a P T) + 2 := by
  have hm := (Nat.clog_mono_right 2 (referenceOverhead_le k ell a P T s)).trans
    (clog_two_mul_le _ _)
  have hr := referenceHashBits_le k ell a T s
  have hr' := Nat.mul_le_mul_left (k * (ell + 1)) hr
  have hb := clog_two_state_product hQ hU (referenceOverhead k ell a P T s)
    (k * (ell + 1) * referenceHashBits k ell a T s)
  dsimp only [referenceStateBound]
  nlinarith only [hm, hr', hb]

theorem cache_state_bits_le {k ell a P T Q U s M q u : ℕ}
    (hQ : Q ≤ 2 ^ q) (hU : U ≤ 2 ^ u) (hsM : s ≤ M) :
    Nat.clog 2 (cacheStateBound k ell a P T Q U s M) ≤ q + u +
      k * (ell + 2) * Nat.clog 2 (blockSparseMenu (2 * T + 1) a M) +
      k * (ell + 1) * Nat.clog 2 (referenceHashMultiplier k ell T) +
      Nat.clog 2 (cacheOverhead k ell P T) + 2 := by
  have hs := Nat.clog_mono_right 2 (blockSparseMenu_mono (n := 2 * T + 1) (a := a) hsM)
  have hr := referenceHashBits_le k ell a T s
  have hm : Nat.clog 2 (cacheOverhead k ell P T * blockSparseMenu (2 * T + 1) a M ^ k) ≤
      Nat.clog 2 (cacheOverhead k ell P T) + k * Nat.clog 2 (blockSparseMenu (2 * T + 1) a M) := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add, Nat.mul_comm k, pow_mul]
    exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) _)
      (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) _) _)
  have hr' := Nat.mul_le_mul_left (k * (ell + 1))
    (hr.trans (Nat.add_le_add_right hs _))
  have hb := clog_two_state_product hQ hU
    (cacheOverhead k ell P T * blockSparseMenu (2 * T + 1) a M ^ k)
    (k * (ell + 1) * referenceHashBits k ell a T s)
  have he : Q * U * (cacheOverhead k ell P T * blockSparseMenu (2 * T + 1) a M ^ k) =
      Q * U * cacheOverhead k ell P T * blockSparseMenu (2 * T + 1) a M ^ k := by ring
  rw [he] at hb
  dsimp only [cacheStateBound]
  nlinarith only [hm, hr', hb]

theorem referencePolynomial_pos {k : ℕ} (hk : 1 ≤ k) (ell a P T : ℕ) :
    1 ≤ referencePolynomial k ell a P T := by
  have : 0 < k := by omega
  exact Nat.one_le_iff_ne_zero.mpr (by dsimp [referencePolynomial]; positivity)

theorem cacheOverhead_pos {k : ℕ} (hk : 1 ≤ k) (ell P T : ℕ) :
    1 ≤ cacheOverhead k ell P T := by
  have : 0 < k := by omega
  exact Nat.one_le_iff_ne_zero.mpr (by dsimp [cacheOverhead]; positivity)

theorem referenceHashMultiplier_pos {k ell : ℕ} (hk : 1 ≤ k) (hell : 1 ≤ ell) (T : ℕ) :
    1 ≤ referenceHashMultiplier k ell T := by
  have : 0 < k := by omega
  have : 0 < ell := by omega
  exact Nat.one_le_iff_ne_zero.mpr (by dsimp [referenceHashMultiplier]; positivity)

theorem referencePolynomial_polynomial (k ell a K P T : ℕ) (hT : T ≤ K * (P + 1)) :
    referencePolynomial k ell a P T ≤
      k * (1 + ell * 2 ^ a) * ((4 * K + 4) * (P + 1)) ^ (k + 10) := by
  let B := (4 * K + 4) * (P + 1)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have ht : T + 1 ≤ B := by dsimp [B]; nlinarith
  have hn : 2 * T + 1 ≤ B := by dsimp [B]; nlinarith
  have hn' : 2 * T + 2 ≤ B := by dsimp [B]; nlinarith
  have h4 : 4 * T + 1 ≤ B := by dsimp [B]; nlinarith
  have hs : 1 + (2 * T + 1) ^ 2 ≤ B ^ 2 := by nlinarith
  have hP : P + 1 ≤ B := by dsimp [B]; nlinarith
  have hinner : 1 + T * (P + 1) ^ 2 * ell * (2 * T + 1) * 2 ^ a ≤
      (1 + ell * 2 ^ a) * B ^ 4 := by
    have hm : T * (P + 1) ^ 2 * ell * (2 * T + 1) * 2 ^ a ≤ B * B ^ 2 * ell * B * 2 ^ a := by
      gcongr
      omega
    have hp : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ hB
    nlinarith
  dsimp only [referencePolynomial]
  calc
    _ ≤ k * B * B ^ (k + 2) * B * B ^ 2 * ((1 + ell * 2 ^ a) * B ^ 4) := by gcongr
    _ = _ := by dsimp [B]; simp only [pow_succ]; ring

theorem cacheOverhead_polynomial (k ell K P T : ℕ) (hT : T ≤ K * (P + 1)) :
    cacheOverhead k ell P T ≤
      k * (ell + 1) ^ k * ((4 * K + 4) * (P + 1)) ^ (4 * k + 6) := by
  let B := (4 * K + 4) * (P + 1)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have ht : T + 1 ≤ B := by dsimp [B]; nlinarith
  have hn : 2 * T + 1 ≤ B := by dsimp [B]; nlinarith
  have hn' : 2 * T + 2 ≤ B := by dsimp [B]; nlinarith
  have h4 : 4 * T + 1 ≤ B := by dsimp [B]; nlinarith
  have hs : 1 + (2 * T + 1) ^ 2 ≤ B ^ 2 := by nlinarith
  have hP : P + 1 ≤ B := by dsimp [B]; nlinarith
  have hinner : 1 + (T + 1) * (P + 1) ^ 2 * ell ≤ (ell + 1) * B ^ 3 := by
    have hm : (T + 1) * (P + 1) ^ 2 * ell ≤ B * B ^ 2 * ell := by gcongr
    have hp : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB
    nlinarith
  dsimp only [cacheOverhead]
  calc
    _ ≤ k * B * B ^ (k + 2) * B * B ^ 2 * ((ell + 1) * B ^ 3) ^ k := by gcongr
    _ = _ := by
      change k * B * B ^ (k + 2) * B * B ^ 2 * ((ell + 1) * B ^ 3) ^ k =
        k * (ell + 1) ^ k * B ^ (4 * k + 6)
      rw [mul_pow (ell + 1), ← pow_mul]
      rw [show 4 * k + 6 = (k + 2) + 1 + 1 + 2 + 3 * k by omega]
      simp only [pow_add, pow_one]
      ring

def referenceEnvelopeCoefficient (k ell a : ℕ) : ℕ :=
  k * (1 + ell * 2 ^ a) + k * (ell + 1) ^ k + 2 * k * ell + 1

theorem reference_polynomial_envelope (k ell a K P T : ℕ) (hT : T ≤ K * (P + 1)) :
    let B := (4 * K + 4) * (P + 1)
    let A := referenceEnvelopeCoefficient k ell a
    referencePolynomial k ell a P T ≤ A * B ^ (4 * k + 10) ∧
    cacheOverhead k ell P T ≤ A * B ^ (4 * k + 10) ∧
    referenceHashMultiplier k ell T ≤ A * B ^ (4 * k + 10) := by
  let B := (4 * K + 4) * (P + 1)
  let A := referenceEnvelopeCoefficient k ell a
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hA₁ : k * (1 + ell * 2 ^ a) ≤ A := by dsimp [A, referenceEnvelopeCoefficient]; omega
  have hA₂ : k * (ell + 1) ^ k ≤ A := by dsimp [A, referenceEnvelopeCoefficient]; omega
  have hA₃ : 2 * k * ell ≤ A := by dsimp [A, referenceEnvelopeCoefficient]; omega
  refine ⟨(referencePolynomial_polynomial k ell a K P T hT).trans ?_,
    (cacheOverhead_polynomial k ell K P T hT).trans ?_, ?_⟩
  · exact Nat.mul_le_mul hA₁ (pow_le_pow_right' hB (by omega))
  · exact Nat.mul_le_mul hA₂ (pow_le_pow_right' hB (by omega))
  · have ht : T + 1 ≤ B := by dsimp [B]; nlinarith
    calc
      referenceHashMultiplier k ell T = (2 * k * ell) * (T + 1) := by
        dsimp [referenceHashMultiplier]; ring
      _ ≤ A * B := Nat.mul_le_mul hA₃ ht
      _ ≤ A * B ^ (4 * k + 10) := Nat.mul_le_mul_left A (by
        simpa only [pow_one] using pow_le_pow_right' hB (show 1 ≤ 4 * k + 10 by omega))

/-- A single length threshold pays time, positions, frozen cutoff and output
ordinal, the whole observer, and both initial/reject states in either bill. -/
theorem reference_polynomial_bits_small (k ell a : ℕ) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    {C ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      ((k * (ell + 1) : ℕ) : ℝ) * Nat.clog 2 (referenceHashMultiplier k ell T) +
          Nat.clog 2 (referencePolynomial k ell a P T) + 2 ≤ ε * P ∧
      ((k * (ell + 1) : ℕ) : ℝ) * Nat.clog 2 (referenceHashMultiplier k ell T) +
          Nat.clog 2 (cacheOverhead k ell P T) + 2 ≤ ε * P := by
  let H := k * (ell + 1)
  let A := referenceEnvelopeCoefficient k ell a
  have hA : 1 ≤ A := by dsimp [A, referenceEnvelopeCoefficient]; omega
  have hε' : 0 < ε / (2 * ((H : ℝ) + 1)) := by positivity
  obtain ⟨P₁, hbits⟩ := polynomial_menu_clog_small (e := 4 * k + 10) hA
    (show 1 ≤ 4 * ⌈C⌉₊ + 4 by omega) hε'
  refine ⟨max P₁ ⌈4 / ε⌉₊, ?_⟩
  intro P hP T hT
  have hP₁ := (le_max_left P₁ ⌈4 / ε⌉₊).trans hP
  have hc : 4 / ε ≤ (P : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right P₁ ⌈4 / ε⌉₊).trans hP)
  have hconst : 2 ≤ ε * P / 2 := by
    have hh := (div_le_iff₀ hε).mp hc
    linarith
  have hT' : T ≤ ⌈C⌉₊ * (P + 1) := by
    exact_mod_cast hT.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity))
  obtain ⟨hpoly, hcache, hhash⟩ := reference_polynomial_envelope k ell a ⌈C⌉₊ P T hT'
  have hL := hbits P hP₁ _ (referenceHashMultiplier_pos hk hell T) hhash
  have hR := hbits P hP₁ _ (referencePolynomial_pos hk ell a P T) hpoly
  have hM := hbits P hP₁ _ (cacheOverhead_pos hk ell P T) hcache
  have hHL := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (α := ℝ) H)
  have he : (H : ℝ) * (ε / (2 * ((H : ℝ) + 1)) * P) +
      ε / (2 * ((H : ℝ) + 1)) * P = ε * P / 2 := by field_simp
  change (H : ℝ) * _ + _ + 2 ≤ ε * P ∧ (H : ℝ) * _ + _ + 2 ≤ ε * P
  constructor <;> nlinarith only [hHL, hR, hM, hconst, he]

/-- The source half-reserve, sparse quarter-reserve and explicit polynomial
quarter-reserve imply both enlarged-rule budgets. The immutable label is paid
once; its evolving hash copies are already in the controller bill. -/
theorem reference_reserves {P N D H A q lam L B Z r bits : ℕ}
    (hN : 1 ≤ N) (hD : 1 ≤ D) (hAD : A ≤ D) (hAH : A ≤ H)
    (hbits : bits ≤ q + D * lam + H * L + B + 2) (hr : r ≤ lam + L)
    (hq : (q : ℝ) ≤ (P : ℝ) / (128 * (N : ℝ) ^ 2))
    (hlam : (lam : ℝ) ≤ (P : ℝ) / (256 * D * (N : ℝ) ^ 2))
    (hpoly : (H : ℝ) * L + B + 2 ≤ (P : ℝ) / (256 * (N : ℝ) ^ 2))
    (hZ : (Z : ℝ) ≤ (P : ℝ) / (128 * (N : ℝ))) :
    (bits : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ) ^ 2) ∧
      ((Z + A * r : ℕ) : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDl : (D : ℝ) * lam ≤ (P : ℝ) / (256 * (N : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hlam hDr.le
    have he : (D : ℝ) * ((P : ℝ) / (256 * D * (N : ℝ) ^ 2)) =
        (P : ℝ) / (256 * (N : ℝ) ^ 2) := by field_simp
    exact he ▸ hh
  have hbitsr : (bits : ℝ) ≤ (q : ℝ) + (D : ℝ) * lam + (H : ℝ) * L + B + 2 := by
    exact_mod_cast hbits
  have hAl : (A : ℝ) * lam ≤ (D : ℝ) * lam := by exact_mod_cast Nat.mul_le_mul_right lam hAD
  have hAL : (A : ℝ) * L ≤ (H : ℝ) * L := by exact_mod_cast Nat.mul_le_mul_right L hAH
  have hAr : (A : ℝ) * r ≤ (A : ℝ) * lam + (A : ℝ) * L := by
    have hh := Nat.mul_le_mul_left A hr
    rw [Nat.mul_add] at hh
    exact_mod_cast hh
  have hsmall : (P : ℝ) / (128 * (N : ℝ) ^ 2) ≤ (P : ℝ) / (128 * (N : ℝ)) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg P) (by positivity)
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  constructor
  · ring_nf at hq hDl hpoly hbitsr ⊢
    linarith
  · push_cast
    have hBr : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have har : (A : ℝ) * r ≤ (P : ℝ) / (128 * (N : ℝ) ^ 2) := by
      ring_nf at hAl hAL hAr hDl hpoly ⊢
      linarith
    ring_nf at hZ har hsmall ⊢
    linarith

theorem reference_budgets_small (k ell a N : ℕ) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (hN : 1 ≤ N) (C : ℝ) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      ∀ Q U q u Z₀ s : ℕ, Q ≤ 2 ^ q → U ≤ 2 ^ u →
        ((q + u : ℕ) : ℝ) ≤ (P : ℝ) / (128 * (N : ℝ) ^ 2) →
        (Nat.clog 2 (blockSparseMenu (2 * T + 1) a s) : ℝ) ≤
          (P : ℝ) / (256 * (k * (ell + 1) + 1) * (N : ℝ) ^ 2) →
        (Z₀ : ℝ) ≤ (P : ℝ) / (128 * (N : ℝ)) →
        (Nat.clog 2 (referenceStateBound k ell a P T Q U s) : ℝ) ≤
          (P : ℝ) / (64 * (N : ℝ) ^ 2) ∧
        (referenceLabelBits k ell a T s Z₀ : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨P₀, hpoly⟩ := reference_polynomial_bits_small k ell a hk hell
    (C := C) (show 0 < 1 / (256 * (N : ℝ) ^ 2) by positivity)
  refine ⟨P₀, ?_⟩
  intro P hP T hT Q U q u Z₀ s hQ hU hqu hs hZ
  apply reference_reserves hN (by omega : 1 ≤ k * (ell + 1) + 1)
    (by nlinarith : k * ell ≤ k * (ell + 1) + 1) (by nlinarith : k * ell ≤ k * (ell + 1))
    (reference_state_bits_le hQ hU) (referenceHashBits_le k ell a T s) hqu
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hs
  · simpa only [one_div_mul_eq_div] using (hpoly P hP T hT).1
  · exact hZ

theorem cache_budgets_small (k ell a N : ℕ) (hk : 1 ≤ k) (hell : 1 ≤ ell)
    (hN : 1 ≤ N) (C : ℝ) :
    ∃ P₀ : ℕ, ∀ P, P₀ ≤ P → ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) →
      ∀ Q U q u Z₀ s M : ℕ, Q ≤ 2 ^ q → U ≤ 2 ^ u → s ≤ M →
        ((q + u : ℕ) : ℝ) ≤ (P : ℝ) / (128 * (N : ℝ) ^ 2) →
        (Nat.clog 2 (blockSparseMenu (2 * T + 1) a M) : ℝ) ≤
          (P : ℝ) / (256 * (k * (ell + 2)) * (N : ℝ) ^ 2) →
        (Z₀ : ℝ) ≤ (P : ℝ) / (128 * (N : ℝ)) →
        (Nat.clog 2 (cacheStateBound k ell a P T Q U s M) : ℝ) ≤
          (P : ℝ) / (64 * (N : ℝ) ^ 2) ∧
        (referenceLabelBits k ell a T s Z₀ : ℝ) ≤ (P : ℝ) / (64 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨P₀, hpoly⟩ := reference_polynomial_bits_small k ell a hk hell
    (C := C) (show 0 < 1 / (256 * (N : ℝ) ^ 2) by positivity)
  refine ⟨P₀, ?_⟩
  intro P hP T hT Q U q u Z₀ s M hQ hU hsM hqu hs hZ
  have hr := (referenceHashBits_le k ell a T s).trans
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (blockSparseMenu_mono (a := a) hsM)) _)
  apply reference_reserves hN (by nlinarith : 1 ≤ k * (ell + 2))
    (by nlinarith : k * ell ≤ k * (ell + 2)) (by nlinarith : k * ell ≤ k * (ell + 1))
    (cache_state_bits_le hQ hU hsM) hr hqu
  · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hs
  · simpa only [one_div_mul_eq_div] using (hpoly P hP T hT).2
  · exact hZ

/-- One positive density pays both the current sparse candidates and every
historical residual `s + floor(δP) + 1`, including the entering write. -/
theorem reference_cache_sparse_bits_small (a : ℕ) {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ P₀ : ℕ, ∀ P, P₀ ≤ P →
      ∀ T : ℕ, (T : ℝ) ≤ C * (P + 1) → ∀ s : ℕ, (s : ℝ) ≤ δ * P →
        (Nat.clog 2 (blockSparseMenu (2 * T + 1) a s) : ℝ) ≤ ε * P ∧
        (Nat.clog 2 (blockSparseMenu (2 * T + 1) a (s + ⌊δ * P⌋₊ + 1)) : ℝ) ≤ ε * P := by
  obtain ⟨δ, hδ, hδcap, P₀, hbits⟩ := carrier_hash_bits_small a hC hε
  refine ⟨δ, hδ, hδcap, P₀, ?_⟩
  intro P hP T hT s hs
  have hs' := Nat.le_floor hs
  have hm := hbits P hP T hT
  constructor
  · exact (show (Nat.clog 2 (blockSparseMenu (2 * T + 1) a s) : ℝ) ≤
        Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)) by
      exact_mod_cast Nat.clog_mono_right 2 (blockSparseMenu_mono (a := a) (by omega))).trans hm
  · exact (show (Nat.clog 2 (blockSparseMenu (2 * T + 1) a (s + ⌊δ * P⌋₊ + 1)) : ℝ) ≤
        Nat.clog 2 (blockSparseMenu (2 * T + 1) a (2 * ⌊δ * P⌋₊ + 2)) by
      exact_mod_cast Nat.clog_mono_right 2 (blockSparseMenu_mono (a := a) (by omega))).trans hm

end AdaptiveTransfer
