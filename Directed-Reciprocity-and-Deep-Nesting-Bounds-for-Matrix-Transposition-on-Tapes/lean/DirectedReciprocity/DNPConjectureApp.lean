import DirectedReciprocity.DNPFibonacci

/-!
# Block-Cancellation Laws, Prefix Lockstep, and Three-Regime Block-Pair Witnesses
(`Proposition OC` and `Theorem A`)

This module completes the formalization of the deep-nesting hierarchy results:

1. **Formal `Lemma block` & `Proposition OC` (`block_served_mass`, `block_canceller_mass`,
   `propOC_fwd_bounds`, `propOC_back_bounds`, `propOC_sum_all_paths`,
   `propOC_mersenne_straddle`)**:
   - Exact level-uniform stroke parameters `blockA`, `blockE`, `blockQ` of Paper 8's block labels
     `B(a, K)` and modular invariance under `K ↦ K % q`.
   - Across any complete `(a + 1)`-level block `(d_canc, d_srv) ∈ Bool × (Fin a → Bool)`:
     * forward canceller stroke (`d_canc = true`): path sum lies in `[-Q + a(1 + K), 0]`;
     * back canceller stroke (`d_canc = false`): path sum lies in `[1 + a(1 + K), Q + 1]`;
     * total path sum over all `2^(a + 1)` block paths equals `2^a · (a(K + 1) + 1) > 0`
       (exact positive mean drift `+(a(K + 1) + 1) / 2` per block).
   - Pure binary clock `B(∞, 0)` modulo any Mersenne number `q = 2^B - 1` (`B ≥ 2`): at every level
     `κ ≤ m` with `B ∣ (m - κ + 2)`, the `Theorem V*` straddle-pair lower bound equals `q - 1`.
2. **Prefix Lockstep (`apexOffset`, `apexOffset_diff_eq`, `apexOffset_diff_indep_prefix`)**:
   Inside any level-`0` stroke, the relative offset `α_κ(ε) - α_k(ε)` (`1 ≤ k ≤ κ`) depends only on
   the intermediate direction bits `ε(k), …, ε(κ - 1)` and is completely invariant under the
   `2^(k - 1)` prefix choices `(ε(1), …, ε(k - 1))`.
3. **Unconditional Odd-Shift Coarse Straddle Visibility (`periodVApices`,
   `sum_classStraddleCount_odd`, `reverse_markov_simultaneous`,
   `exists_oddShift_coarse_straddle`)**:
   Combining the `2^(κ + 1)` disjoint V-spans of level `κ` in `[0, P)` with
   `sum_straddleSet_card_parity` (`Theorem V*(d)`) and a pure `ℕ` Reverse-Markov simultaneous
   selection lemma, we prove that for `m < s₀` and `4 * (Nat.log 2 (m + 1) + 1 + a) ≤ m + 1`,
   there exists an odd shift `ξ ∈ oddRange P` (independent of `K` and `q`) at which at least `1/16`
   of the coarse zone `k ∈ [1, (m + 1) / 4]` has at least `(2^(k + 2) * R_k) / 2^(a + 7)` straddling
   apex half-widths against canceller `cancellerBelow m a k`.
4. **Three-Regime Mod-`q` Dichotomy & `Theorem A` (`block_straddle_residue_ge_half_q`,
   `block_overflow_band_witness`, `theoremA_three_regimes`, `theoremA_symmetric_blockPair`)**:
   Establishes three-regime blind-error and coarse-straddle failure witnesses for bounded-range
   block-label pairs `(B(a₁, K₁), B(a₂, K₂))` (`1 ≤ a₁, a₂ ≤ a₀`) at two fixed odd shifts (a single
   odd shift in the symmetric case `a₁ = a₂, K₁ = K₂`) across all `K₁, K₂ : ℤ` and all `q ≥ 3`
   with **zero logarithmic term** in `q`.
-/

namespace DirectedReciprocity

open Finset

/-! ### Part 1: Block Labels (`Lemma block`) and `Proposition OC` -/

/-- Whether level `l` is a canceller level of `B(a, K)` at nesting depth `m`, i.e.,
`(m - l) % (a + 1) = a`. -/
def isCanceller (m a l : ℕ) : Bool :=
  (m - l) % (a + 1) == a

/-- Block mass `Q(a, K) = (2^a - 1)(2K + 2)` of `B(a, K)`. -/
def blockQ (a : ℕ) (K : ℤ) : ℤ :=
  ((2 ^ a : ℤ) - 1) * (2 * K + 2)

/-- Apex parameter `A_l` of `B(a, K)` (`0` on cancellers, `K` on served levels). -/
def blockA (m a : ℕ) (K : ℤ) (l : ℕ) : ℤ :=
  if isCanceller m a l then 0 else K

/-- Valley parameter `E_l` of `B(a, K)` (`-Q - 2` on cancellers,
`K + (2^j - 1)(2K + 2)` on served levels with `j = (m - l) % (a + 1)` served levels below). -/
def blockE (m a : ℕ) (K : ℤ) (l : ℕ) : ℤ :=
  if isCanceller m a l then -blockQ a K - 2
  else K + ((2 ^ ((m - l) % (a + 1)) : ℤ) - 1) * (2 * K + 2)

theorem blockQ_nonneg (a : ℕ) {K : ℤ} (hK : 0 ≤ K) : 0 ≤ blockQ a K := by
  unfold blockQ
  have h1 : (1 : ℤ) ≤ 2 ^ a := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
  nlinarith

theorem blockQ_ge_two_K_add_two {a : ℕ} (ha : 1 ≤ a) {K : ℤ} (hK : 0 ≤ K) :
    2 * K + 2 ≤ blockQ a K := by
  unfold blockQ
  have hpow : (2 : ℤ) ≤ 2 ^ a := by
    have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
    exact_mod_cast this
  nlinarith

/-- Formal `Lemma block` (served level): when `¬ isCanceller m a l`, with
`j = (m - l) % (a + 1) < a`, `A_l + E_l + 2 = 2^j (2K + 2)`, `c_b(l) = 1 + K`, and
`c_f(l) = 2^j (2K + 2)`. -/
theorem block_served_mass (m a : ℕ) (K : ℤ) (l : ℕ) (hc : isCanceller m a l = false) :
    let j := (m - l) % (a + 1)
    blockA m a K l + blockE m a K l + 2 = (2 ^ j : ℤ) * (2 * K + 2) ∧
    pathSumBack (blockA m a K) l = 1 + K ∧
    pathSumFwd (blockA m a K) (blockE m a K) l = (2 ^ j : ℤ) * (2 * K + 2) := by
  have hA : blockA m a K l = K := by simp [blockA, hc]
  have hE : blockE m a K l = K + ((2 ^ ((m - l) % (a + 1)) : ℤ) - 1) * (2 * K + 2) := by
    simp [blockE, hc]
  refine ⟨?_, ?_, ?_⟩
  · change blockA m a K l + blockE m a K l + 2 = (2 ^ ((m - l) % (a + 1)) : ℤ) * (2 * K + 2)
    rw [hA, hE]; ring
  · change pathSumBack (blockA m a K) l = 1 + K
    rw [pathSumBack, hA]
  · change pathSumFwd (blockA m a K) (blockE m a K) l =
      (2 ^ ((m - l) % (a + 1)) : ℤ) * (2 * K + 2)
    rw [pathSumFwd, hA, hE]; ring

/-- Formal `Lemma block` (canceller level): when `isCanceller m a l = true`,
`A_l + E_l + 2 = -Q`, `c_b(l) = 1`, `c_f(l) = -Q`, and `c_f(l) - c_b(l) = -Q - 1`. -/
theorem block_canceller_mass (m a : ℕ) (K : ℤ) (l : ℕ) (hc : isCanceller m a l = true) :
    blockA m a K l + blockE m a K l + 2 = -blockQ a K ∧
    pathSumBack (blockA m a K) l = 1 ∧
    pathSumFwd (blockA m a K) (blockE m a K) l = -blockQ a K ∧
    pathSumFwd (blockA m a K) (blockE m a K) l - pathSumBack (blockA m a K) l =
      -blockQ a K - 1 := by
  simp only [blockA, blockE, pathSumBack, pathSumFwd, hc, ↓reduceIte]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- Modular invariance of `B(a, K)` under `K ↦ K % q`: for any `q > 0`, `blockA` and `blockE`
for `K` and `K % q` are congruent modulo `q`, hence have identical `blindApexErr` and
`blindBandErr`. -/
theorem block_blind_errors_mod_K (m a : ℕ) (K : ℤ) {q : ℤ} (_hq : 0 < q) :
    (∀ k, blindApexErr (blockA m a K) q k = blindApexErr (blockA m a (K % q)) q k) ∧
    (∀ k l, blindBandErr (blockA m a K) (blockE m a K) q k l =
      blindBandErr (blockA m a (K % q)) (blockE m a (K % q)) q k l) := by
  have hK_dvd : q ∣ K - K % q :=
    ⟨K / q, by have h := Int.emod_add_mul_ediv K q; linear_combination -h⟩
  have hA_dvd : ∀ i, q ∣ blockA m a K i - blockA m a (K % q) i := by
    intro i; unfold blockA
    cases isCanceller m a i <;> simp [hK_dvd]
  have hQ_dvd : q ∣ blockQ a K - blockQ a (K % q) := by
    unfold blockQ
    obtain ⟨t, ht⟩ := hK_dvd
    refine ⟨((2 ^ a : ℤ) - 1) * (2 * t), ?_⟩
    linear_combination ((2 ^ a : ℤ) - 1) * 2 * ht
  have hE_dvd : ∀ i, q ∣ blockE m a K i - blockE m a (K % q) i := by
    intro i; unfold blockE
    cases isCanceller m a i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨t, ht⟩ := hK_dvd
      set c := ((2 ^ ((m - i) % (a + 1)) : ℤ) - 1)
      refine ⟨t * (1 + 2 * c), ?_⟩
      linear_combination (1 + 2 * c) * ht
    · simp only [↓reduceIte]
      obtain ⟨t, ht⟩ := hQ_dvd
      exact ⟨-t, by linarith⟩
  have hmod_of_dvd : ∀ x y : ℤ, q ∣ x - y → x % q = y % q := by
    intro x y ⟨t, ht⟩
    have hxy : x = y + t * q := by linarith
    rw [hxy, Int.add_mul_emod_self_right]
  refine ⟨fun k => hmod_of_dvd _ _ (hA_dvd k), fun k l => hmod_of_dvd _ _ ?_⟩
  have hsum : q ∣ (∑ i ∈ Icc (k + 1) l, (blockA m a K i + blockE m a K i + 2)) -
      (∑ i ∈ Icc (k + 1) l, (blockA m a (K % q) i + blockE m a (K % q) i + 2)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    have hrew : (blockA m a K i + blockE m a K i + 2) -
        (blockA m a (K % q) i + blockE m a (K % q) i + 2) =
        (blockA m a K i - blockA m a (K % q) i) + (blockE m a K i - blockE m a (K % q) i) := by
      ring
    rw [hrew]
    exact dvd_add (hA_dvd i) (hE_dvd i)
  have htot : (blockE m a K k - ∑ i ∈ Icc (k + 1) l, (blockA m a K i + blockE m a K i + 2)) -
      (blockE m a (K % q) k -
        ∑ i ∈ Icc (k + 1) l, (blockA m a (K % q) i + blockE m a (K % q) i + 2)) =
      (blockE m a K k - blockE m a (K % q) k) -
      ((∑ i ∈ Icc (k + 1) l, (blockA m a K i + blockE m a K i + 2)) -
        (∑ i ∈ Icc (k + 1) l, (blockA m a (K % q) i + blockE m a (K % q) i + 2))) := by
    ring
  rw [htot]
  exact dvd_sub (hE_dvd k) hsum

/-- Geometric sum `∑_{j < a} 2^j = 2^a - 1` over `Fin a`. -/
theorem sum_fin_two_pow (a : ℕ) :
    ∑ j : Fin a, (2 ^ j.val : ℤ) = (2 ^ a : ℤ) - 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    ring

/-- Path sum across one complete `(a + 1)`-level block of `B(a, K)` along stroke-direction choices
`d_canc : Bool` (`false` = back stroke, `true` = forward stroke) at the canceller and
`d_srv : Fin a → Bool` at the `a` served levels indexed by `j ∈ {0, …, a - 1}` served levels below. -/
def blockPathSum (a : ℕ) (K : ℤ) (d_canc : Bool) (d_srv : Fin a → Bool) : ℤ :=
  (if d_canc then -blockQ a K else 1) +
    ∑ j : Fin a, if d_srv j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K

private theorem served_sum_bounds (a : ℕ) {K : ℤ} (hK : 0 ≤ K) (d_srv : Fin a → Bool) :
    (a : ℤ) * (1 + K) ≤
      (∑ j : Fin a, if d_srv j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K) ∧
    (∑ j : Fin a, if d_srv j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K) ≤ blockQ a K := by
  have hterm_ge : ∀ j : Fin a,
      1 + K ≤ (if d_srv j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K) := by
    intro j
    cases d_srv j
    · simp
    · simp only [↓reduceIte]
      have hp : (1 : ℤ) ≤ 2 ^ j.val := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
      nlinarith
  have hterm_le : ∀ j : Fin a,
      (if d_srv j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K) ≤
        (2 ^ j.val : ℤ) * (2 * K + 2) := by
    intro j
    cases d_srv j
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hp : (1 : ℤ) ≤ 2 ^ j.val := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
      nlinarith
    · simp
  constructor
  · have hlow := Finset.sum_le_sum (fun j (_ : j ∈ univ) => hterm_ge j)
    simpa [Finset.sum_const, nsmul_eq_mul] using hlow
  · have hhigh := Finset.sum_le_sum (fun j (_ : j ∈ univ) => hterm_le j)
    have hgeom : ∑ j : Fin a, (2 ^ j.val : ℤ) * (2 * K + 2) = blockQ a K := by
      rw [← Finset.sum_mul, sum_fin_two_pow]; rfl
    linarith

/-- **Proposition OC(a) (Forward-Canceller Block-Cancellation Bounds)**:
When the canceller V takes its forward stroke (`d_canc = true`), the block path sum lies in
`[-Q + a(1 + K), 0]`, achieving `0` when all `a` served levels also take their forward strokes. -/
theorem propOC_fwd_bounds (a : ℕ) {K : ℤ} (hK : 0 ≤ K) (d_srv : Fin a → Bool) :
    -blockQ a K + (a : ℤ) * (1 + K) ≤ blockPathSum a K true d_srv ∧
    blockPathSum a K true d_srv ≤ 0 ∧
    blockPathSum a K true (fun _ => true) = 0 := by
  obtain ⟨hlo, hhi⟩ := served_sum_bounds a hK d_srv
  refine ⟨by unfold blockPathSum; simp; linarith,
    by unfold blockPathSum; simp; linarith, ?_⟩
  unfold blockPathSum
  simp only [↓reduceIte, ← Finset.sum_mul, sum_fin_two_pow]
  unfold blockQ; ring

/-- **Proposition OC(b) (Back-Canceller Block-Cancellation Bounds)**:
When the canceller V takes its back stroke (`d_canc = false`), the block path sum lies in
`[1 + a(1 + K), Q + 1]`. -/
theorem propOC_back_bounds (a : ℕ) {K : ℤ} (hK : 0 ≤ K) (d_srv : Fin a → Bool) :
    1 + (a : ℤ) * (1 + K) ≤ blockPathSum a K false d_srv ∧
    blockPathSum a K false d_srv ≤ blockQ a K + 1 := by
  obtain ⟨hlo, hhi⟩ := served_sum_bounds a hK d_srv
  unfold blockPathSum
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact ⟨by linarith, by linarith⟩

/-- **Proposition OC(c) (Exact Positive Mean Drift Across All `2^(a + 1)` Block Paths)**:
Summing `blockPathSum a K` over all `2^(a + 1)` stroke-direction choices `(d_canc, d_srv)` yields
`2^a · (a(K + 1) + 1) > 0` (mean drift `+(a(K + 1) + 1) / 2` per block). -/
theorem propOC_sum_all_paths (a : ℕ) (K : ℤ) :
    ∑ p : Bool × (Fin a → Bool), blockPathSum a K p.1 p.2 =
      (2 ^ a : ℤ) * ((a : ℤ) * (K + 1) + 1) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hbool : ∀ f : Fin a → Bool,
      ∑ b : Bool, blockPathSum a K b f =
        (1 - blockQ a K) +
          ∑ j : Fin a, 2 * (if f j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K) := by
    intro f
    rw [Fintype.sum_bool, ← Finset.mul_sum]
    unfold blockPathSum
    simp only [↓reduceIte, Bool.false_eq_true]
    ring
  simp_rw [hbool]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Finset.sum_comm]
  have hflip : ∀ j : Fin a,
      ∑ f : Fin a → Bool, 2 * (if f j then (2 ^ j.val : ℤ) * (2 * K + 2) else 1 + K) =
        (2 ^ a : ℤ) * ((2 ^ j.val : ℤ) * (2 * K + 2) + (1 + K)) := by
    intro j
    set vT : ℤ := (2 ^ j.val : ℤ) * (2 * K + 2)
    set vF : ℤ := 1 + K
    let flip : (Fin a → Bool) → (Fin a → Bool) := fun f i => if i = j then !f i else f i
    have hbij : ∑ f : Fin a → Bool, (if (flip f) j then vT else vF) =
        ∑ f : Fin a → Bool, (if f j then vT else vF) := by
      refine Finset.sum_bij (fun f _ => flip f) ?_ ?_ ?_ ?_
      · intros; exact mem_univ _
      · intro f₁ _ f₂ _ heq
        funext i
        have hi := congrFun heq i
        dsimp [flip] at hi
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte] at hi
          exact Bool.not_inj hi
        · simp only [hij, ↓reduceIte] at hi; exact hi
      · intro g _
        refine ⟨flip g, mem_univ _, ?_⟩
        funext i; dsimp [flip]
        by_cases hij : i = j <;> simp [hij]
      · intros; rfl
    have h2 : ∑ f : Fin a → Bool, 2 * (if f j then vT else vF) =
        (∑ f : Fin a → Bool, (if f j then vT else vF)) +
          ∑ f : Fin a → Bool, (if (flip f) j then vT else vF) := by
      rw [hbij, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => by ring
    rw [h2, ← Finset.sum_add_distrib]
    have hconst : ∀ f : Fin a → Bool,
        (if f j then vT else vF) + (if (flip f) j then vT else vF) = vT + vF := by
      intro f
      dsimp [flip]
      simp only [↓reduceIte]
      cases f j <;> simp [add_comm]
    simp_rw [hconst]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul]
    push_cast; ring
  simp_rw [hflip, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, sum_fin_two_pow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold blockQ
  push_cast
  ring

private theorem pow_sub_one_dvd (x : ℤ) (t : ℕ) : (x - 1) ∣ (x ^ t - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨x * k + 1, ?_⟩
    rw [pow_succ']
    linear_combination x * hk

/-- **Proposition OC(d) (Mersenne Straddle Residue of the Pure Binary Clock `B(∞, 0)`)**:
Modulo any Mersenne number `q = 2^B - 1` (`B ≥ 2`), the pure binary clock (`c_b(κ) = 1`,
`c_f(κ) = 2^(m - κ + 1)`, `A' = 0`) has `Theorem V*` straddle-pair lower bound equal to `q - 1` at
every level `κ ≤ m` with `B ∣ (m - κ + 2)`. -/
theorem propOC_mersenne_straddle {B m κ : ℕ} (hB : 2 ≤ B) (hdvd : B ∣ (m - κ + 2)) :
    let q : ℤ := (2 ^ B : ℤ) - 1
    let cb : ℤ := 1
    let cf : ℤ := (2 ^ (m - κ + 1) : ℤ)
    (2 * (0 : ℤ) + 2 * (cf - cb)) % q = q - 1 := by
  intro q cb cf
  obtain ⟨t, ht⟩ := hdvd
  have hpow : 2 * (cf - cb) = ((2 ^ B : ℤ) ^ t) - 2 := by
    dsimp [cf, cb]
    have h1 : (2 : ℤ) * (2 ^ (m - κ + 1) : ℤ) = (2 ^ (m - κ + 2) : ℤ) := by
      rw [pow_succ']; ring
    have h2 : (2 ^ (m - κ + 2) : ℤ) = ((2 ^ B : ℤ) ^ t) := by
      rw [ht, pow_mul]
    linarith
  obtain ⟨u, hu⟩ := pow_sub_one_dvd (2 ^ B : ℤ) t
  have hq_ge : 3 ≤ q := by
    dsimp [q]
    have : (4 : ℤ) ≤ 2 ^ B := by
      have : 2 ^ 2 ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hB
      exact_mod_cast this
    linarith
  have hrew : 2 * (0 : ℤ) + 2 * (cf - cb) = (q - 1) + (u - 1) * q := by
    dsimp [q] at hu ⊢
    linarith
  rw [hrew, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]

/-! ### Part 2: Prefix Lockstep (`apexOffset_diff_indep_prefix`) -/

/-- Apex offset `α_k(ε)` inside a level-`0` stroke for the level-`k` V (`1 ≤ k ≤ m`) indexed by
stroke-direction choices `ε : ℕ → Bool` at enclosing levels `1, …, k - 1`. -/
def apexOffset (s0 m k : ℕ) (ε : ℕ → Bool) : ℕ :=
  scaleR s0 0 + ∑ i ∈ Icc 1 (k - 1), (scaleR s0 i + if ε i then strokeLen s0 m i else 0)

/-- Exact relative apex difference `α_κ(ε) - α_k(ε)` (`1 ≤ k ≤ κ`) inside a level-`0` stroke. -/
theorem apexOffset_diff_eq (s0 m : ℕ) {k κ : ℕ} (hk1 : 1 ≤ k) (hkκ : k ≤ κ)
    (ε : ℕ → Bool) :
    (apexOffset s0 m κ ε : ℤ) - (apexOffset s0 m k ε : ℤ) =
      ∑ i ∈ Icc k (κ - 1), ((scaleR s0 i : ℤ) + if ε i then (strokeLen s0 m i : ℤ) else 0) := by
  unfold apexOffset
  have hunion : Icc 1 (κ - 1) = Icc 1 (k - 1) ∪ Icc k (κ - 1) := by
    ext i; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 (k - 1)) (Icc k (κ - 1)) := by
    rw [Finset.disjoint_left]; intro i h1 h2; rw [mem_Icc] at h1 h2; omega
  push_cast
  rw [hunion, Finset.sum_union hdisj]
  ring

/-- **Prefix Lockstep (`Theorem A(a)`)**:
For `1 ≤ k ≤ κ`, if two stroke-direction words `ε₁, ε₂` agree on `Icc k (κ - 1)` (regardless of
their values on the `k - 1` prefix bits `1, …, k - 1`), their relative apex offsets
`α_κ - α_k` are identical. -/
theorem apexOffset_diff_indep_prefix (s0 m : ℕ) {k κ : ℕ} (hk1 : 1 ≤ k) (hkκ : k ≤ κ)
    (ε₁ ε₂ : ℕ → Bool) (hagree : ∀ i ∈ Icc k (κ - 1), ε₁ i = ε₂ i) :
    (apexOffset s0 m κ ε₁ : ℤ) - (apexOffset s0 m k ε₁ : ℤ) =
      (apexOffset s0 m κ ε₂ : ℤ) - (apexOffset s0 m k ε₂ : ℤ) := by
  rw [apexOffset_diff_eq s0 m hk1 hkκ ε₁, apexOffset_diff_eq s0 m hk1 hkκ ε₂]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hagree i hi]

/-! ### Part 3: Disjoint Period V-Spans, Exact Odd-Shift Straddle Sums, & Reverse Markov -/

/-- Recursive Finset of internal V-apex offsets at depth `d` inside a level-`i` stroke (giving the
`2^d` apices of level `i + 1 + d`). -/
def vApicesAux (s0 m : ℕ) : ℕ → ℕ → Finset ℕ
  | i, 0 => {scaleR s0 i}
  | i, d + 1 =>
    (vApicesAux s0 m (i + 1) d).image (fun β => scaleR s0 i + β) ∪
      (vApicesAux s0 m (i + 1) d).image (fun β => scaleR s0 i + strokeLen s0 m (i + 1) + β)

private theorem vApicesAux_span_le {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ (d i : ℕ), i + 1 + d ≤ m →
      ∀ α ∈ vApicesAux s0 m i d,
        scaleR s0 i ≤ α ∧ α + 2 * strokeLen s0 m (i + 1 + d) ≤ strokeLen s0 m i := by
  intro d
  induction d with
  | zero =>
    intro i hi α hα
    rw [vApicesAux, mem_singleton] at hα
    subst hα
    have hsp := strokeLen_succ (by omega : i < m) hms
    exact ⟨le_refl _, by simpa using le_of_eq hsp.symm⟩
  | succ d ih =>
    intro i hi α hα
    have hsp := strokeLen_succ (by omega : i < m) hms
    rw [vApicesAux, mem_union, mem_image, mem_image] at hα
    rcases hα with ⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩
    · obtain ⟨hβ1, hβ2⟩ := ih (i + 1) (by omega) β hβ
      rw [show i + 1 + (d + 1) = i + 1 + 1 + d by omega]
      exact ⟨by omega, by omega⟩
    · obtain ⟨hβ1, hβ2⟩ := ih (i + 1) (by omega) β hβ
      rw [show i + 1 + (d + 1) = i + 1 + 1 + d by omega]
      exact ⟨by omega, by omega⟩

private theorem vApicesAux_spans_disjoint {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ (d i : ℕ), i + 1 + d ≤ m →
      ∀ α₁ ∈ vApicesAux s0 m i d, ∀ α₂ ∈ vApicesAux s0 m i d,
        α₁ ≠ α₂ →
          α₁ + 2 * strokeLen s0 m (i + 1 + d) ≤ α₂ ∨
            α₂ + 2 * strokeLen s0 m (i + 1 + d) ≤ α₁ := by
  intro d
  induction d with
  | zero =>
    intro i _ α₁ h₁ α₂ h₂ hne
    rw [vApicesAux, mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  | succ d ih =>
    intro i hi α₁ h₁ α₂ h₂ hne
    rw [vApicesAux, mem_union, mem_image, mem_image] at h₁ h₂
    have hlev : i + 1 + (d + 1) = i + 1 + 1 + d := by omega
    rw [hlev]
    rcases h₁ with ⟨β₁, hβ₁, rfl⟩ | ⟨β₁, hβ₁, rfl⟩ <;>
      rcases h₂ with ⟨β₂, hβ₂, rfl⟩ | ⟨β₂, hβ₂, rfl⟩
    · rcases ih (i + 1) (by omega) β₁ hβ₁ β₂ hβ₂ (by omega) with h | h <;> [left; right] <;> omega
    · obtain ⟨_, hβ₁_le⟩ := vApicesAux_span_le hms d (i + 1) (by omega) β₁ hβ₁
      left; omega
    · obtain ⟨_, hβ₂_le⟩ := vApicesAux_span_le hms d (i + 1) (by omega) β₂ hβ₂
      right; omega
    · rcases ih (i + 1) (by omega) β₁ hβ₁ β₂ hβ₂ (by omega) with h | h <;> [left; right] <;> omega

private theorem card_vApicesAux {s0 m : ℕ} (hms : m ≤ s0) :
    ∀ (d i : ℕ), i + 1 + d ≤ m → (vApicesAux s0 m i d).card = 2 ^ d := by
  intro d
  induction d with
  | zero => intro i _; simp [vApicesAux]
  | succ d ih =>
    intro i hi
    unfold vApicesAux
    have hdisj : Disjoint
        ((vApicesAux s0 m (i + 1) d).image (fun β => scaleR s0 i + β))
        ((vApicesAux s0 m (i + 1) d).image
          (fun β => scaleR s0 i + strokeLen s0 m (i + 1) + β)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [mem_image] at hx1 hx2
      obtain ⟨β₁, hβ₁, rfl⟩ := hx1
      obtain ⟨β₂, hβ₂, heq⟩ := hx2
      obtain ⟨_, h1⟩ := vApicesAux_span_le hms d (i + 1) (by omega) β₁ hβ₁
      have hp := strokeLen_pos s0 m (i + 1 + 1 + d)
      omega
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_image_of_injective _ (fun a b h => by omega),
      ih (i + 1) (by omega), pow_succ]
    ring

private theorem even_of_mem_vApicesAux {s0 m : ℕ} (hms : m < s0) :
    ∀ (d i : ℕ), i + 1 + d ≤ m → ∀ α ∈ vApicesAux s0 m i d, α % 2 = 0 := by
  intro d
  induction d with
  | zero =>
    intro i hi α hα
    rw [vApicesAux, mem_singleton] at hα; subst hα
    exact Nat.dvd_iff_mod_eq_zero.mp (even_scaleR (by omega : i < s0))
  | succ d ih =>
    intro i hi α hα
    have hr : scaleR s0 i % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (even_scaleR (by omega))
    have hpi : strokeLen s0 m (i + 1) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (even_strokeLen (by omega))
    rw [vApicesAux, mem_union, mem_image, mem_image] at hα
    rcases hα with ⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩
    · have hβe := ih (i + 1) (by omega) β hβ; omega
    · have hβe := ih (i + 1) (by omega) β hβ; omega

/-- Finset of all `2^(κ + 1)` V-apex times of level `κ` (`1 ≤ κ ≤ m`) in one period `[0, P)` of
`U(s₀, m, 1)`. -/
def periodVApices (s0 m κ : ℕ) : Finset ℕ :=
  (range 4).biUnion fun q =>
    (vApicesAux s0 m 0 (κ - 1)).image (fun α => q * strokeLen s0 m 0 + α)

theorem periodVApices_span_subset {s0 m κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m ≤ s0)
    {α : ℕ} (hα : α ∈ periodVApices s0 m κ) :
    α + 2 * strokeLen s0 m κ ≤ dnpPeriod s0 m := by
  rw [periodVApices, mem_biUnion] at hα
  obtain ⟨q, hq, hα⟩ := hα
  rw [mem_range] at hq
  rw [mem_image] at hα
  obtain ⟨β, hβ, rfl⟩ := hα
  obtain ⟨_, hspan⟩ := vApicesAux_span_le hms (κ - 1) 0 (by omega) β hβ
  rw [show 0 + 1 + (κ - 1) = κ by omega] at hspan
  unfold dnpPeriod
  nlinarith

theorem periodVApices_spans_disjoint {s0 m κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m ≤ s0)
    {α₁ α₂ : ℕ} (h₁ : α₁ ∈ periodVApices s0 m κ) (h₂ : α₂ ∈ periodVApices s0 m κ)
    (hne : α₁ ≠ α₂) :
    α₁ + 2 * strokeLen s0 m κ ≤ α₂ ∨ α₂ + 2 * strokeLen s0 m κ ≤ α₁ := by
  rw [periodVApices, mem_biUnion] at h₁ h₂
  obtain ⟨q₁, _, h₁⟩ := h₁
  obtain ⟨q₂, _, h₂⟩ := h₂
  rw [mem_image] at h₁ h₂
  obtain ⟨β₁, hβ₁, rfl⟩ := h₁
  obtain ⟨β₂, hβ₂, rfl⟩ := h₂
  obtain ⟨_, hb₁⟩ := vApicesAux_span_le hms (κ - 1) 0 (by omega) β₁ hβ₁
  obtain ⟨_, hb₂⟩ := vApicesAux_span_le hms (κ - 1) 0 (by omega) β₂ hβ₂
  rw [show 0 + 1 + (κ - 1) = κ by omega] at hb₁ hb₂
  by_cases hq : q₁ = q₂
  · subst hq
    have hdis := vApicesAux_spans_disjoint hms (κ - 1) 0 (by omega) β₁ hβ₁ β₂ hβ₂ (by omega)
    rw [show 0 + 1 + (κ - 1) = κ by omega] at hdis
    rcases hdis with h | h <;> [left; right] <;> omega
  · rcases (show q₁ < q₂ ∨ q₂ < q₁ by omega) with hlt | hlt
    · left; nlinarith
    · right; nlinarith

theorem card_periodVApices {s0 m κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m ≤ s0) :
    (periodVApices s0 m κ).card = 2 ^ (κ + 1) := by
  unfold periodVApices
  rw [Finset.card_biUnion]
  · have hconst : ∀ q ∈ range 4,
        ((vApicesAux s0 m 0 (κ - 1)).image (fun α => q * strokeLen s0 m 0 + α)).card =
          2 ^ (κ - 1) := by
      intro q _
      rw [Finset.card_image_of_injective _ (fun a b h => by omega),
        card_vApicesAux hms (κ - 1) 0 (by omega)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [show κ + 1 = (κ - 1) + 2 by omega, pow_add]
    ring
  · intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [mem_image] at hx₁ hx₂
    obtain ⟨β₁, hβ₁, rfl⟩ := hx₁
    obtain ⟨β₂, hβ₂, heq⟩ := hx₂
    obtain ⟨_, hb₁⟩ := vApicesAux_span_le hms (κ - 1) 0 (by omega) β₁ hβ₁
    obtain ⟨_, hb₂⟩ := vApicesAux_span_le hms (κ - 1) 0 (by omega) β₂ hβ₂
    have hp := strokeLen_pos s0 m κ
    rw [show 0 + 1 + (κ - 1) = κ by omega] at hb₁ hb₂
    rcases (show q₁ < q₂ ∨ q₂ < q₁ by omega) with hlt | hlt <;> nlinarith

theorem even_of_mem_periodVApices {s0 m κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m < s0)
    {α : ℕ} (hα : α ∈ periodVApices s0 m κ) : α % 2 = 0 := by
  rw [periodVApices, mem_biUnion] at hα
  obtain ⟨q, _, hα⟩ := hα
  rw [mem_image] at hα
  obtain ⟨β, hβ, rfl⟩ := hα
  have hpi0 : strokeLen s0 m 0 % 2 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp (even_strokeLen (by omega))
  have hβe := even_of_mem_vApicesAux hms (κ - 1) 0 (by omega) β hβ
  have hmul : (q * strokeLen s0 m 0) % 2 = 0 := by
    rw [Nat.mul_mod, hpi0, mul_zero]; rfl
  omega

/-- Finset of odd residues in `[0, P)`. -/
def oddRange (P : ℕ) : Finset ℕ :=
  (range P).filter (fun x => x % 2 = 1)

theorem card_oddRange_two_mul (M : ℕ) : (oddRange (2 * M)).card = M := by
  induction M with
  | zero => simp [oddRange]
  | succ M ih =>
    have hset : oddRange (2 * (M + 1)) = insert (2 * M + 1) (oddRange (2 * M)) := by
      ext x; simp only [oddRange, mem_filter, mem_range, mem_insert]; omega
    rw [hset, Finset.card_insert_of_notMem (by rw [oddRange, mem_filter, mem_range]; omega), ih]

/-- Total straddling half-widths around center `c0` across all `2^(κ + 1)` level-`κ` V's in one
period `[0, P)` (at most one V-span contains `c0`). -/
def totalStraddleAtCenter (s0 m κ R_k c0 : ℕ) : ℕ :=
  ∑ α_V ∈ periodVApices s0 m κ,
    (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card

theorem totalStraddleAtCenter_le {s0 m κ R_k : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m ≤ s0)
    (c0 : ℕ) :
    totalStraddleAtCenter s0 m κ R_k c0 ≤ strokeLen s0 m κ := by
  classical
  unfold totalStraddleAtCenter
  set S_active := (periodVApices s0 m κ).filter fun α_V : ℕ =>
    (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).Nonempty
  have hsum_eq : ∑ α_V ∈ periodVApices s0 m κ,
      (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card =
    ∑ α_V ∈ S_active,
      (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (periodVApices s0 m κ)
      (fun α_V : ℕ => (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).Nonempty)]
    have h0 : ∑ α_V ∈ (periodVApices s0 m κ).filter
        (fun α_V : ℕ => ¬(straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).Nonempty),
        (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card = 0 := by
      apply Finset.sum_eq_zero
      intro α_V hα
      rw [mem_filter, Finset.not_nonempty_iff_eq_empty] at hα
      simp [hα.2]
    rw [h0, add_zero]
  rw [hsum_eq]
  have hcard_le_one : S_active.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro α₁ h₁ α₂ h₂
    by_contra hne
    rw [mem_filter] at h₁ h₂
    have hc1 := center_mem_span_of_straddleSet_nonempty h₁.2
    have hc2 := center_mem_span_of_straddleSet_nonempty h₂.2
    have hdis := periodVApices_spans_disjoint hκ1 hκm hms h₁.1 h₂.1 hne
    rcases hdis with h | h <;> omega
  have hterm_le : ∀ α_V ∈ S_active,
      (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card ≤ strokeLen s0 m κ := by
    intro α_V _
    have hsub : straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k ⊆
        Icc 1 (strokeLen s0 m κ - 1) := by
      intro d hd
      have h := lt_pi_of_mem_straddleSet hd
      rw [mem_Icc]; omega
    calc (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card
        ≤ (Icc 1 (strokeLen s0 m κ - 1)).card := Finset.card_le_card hsub
      _ ≤ strokeLen s0 m κ := by rw [Nat.card_Icc]; omega
  calc ∑ α_V ∈ S_active, (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card
      ≤ ∑ _α_V ∈ S_active, strokeLen s0 m κ := Finset.sum_le_sum hterm_le
    _ = S_active.card * strokeLen s0 m κ := by simp [Finset.sum_const, smul_eq_mul]
    _ ≤ 1 * strokeLen s0 m κ := Nat.mul_le_mul_right _ hcard_le_one
    _ = strokeLen s0 m κ := one_mul _

theorem sum_totalStraddleAtCenter_odd {s0 m κ R_k : ℕ}
    (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m < s0)
    (hpi : strokeLen s0 m κ ≤ R_k) :
    ∑ c0 ∈ oddRange (dnpPeriod s0 m), totalStraddleAtCenter s0 m κ R_k c0 =
      2 ^ (κ + 1) * (strokeLen s0 m κ / 2) ^ 2 := by
  classical
  unfold totalStraddleAtCenter
  rw [Finset.sum_comm]
  set L := strokeLen s0 m κ / 2
  have heven_pi : strokeLen s0 m κ = 2 * L := by
    obtain ⟨t, ht⟩ := even_strokeLen (s0 := s0) (m := m) (by omega : κ < s0)
    omega
  have hper_V : ∀ α_V ∈ periodVApices s0 m κ,
      ∑ c0 ∈ oddRange (dnpPeriod s0 m),
        (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card = L ^ 2 := by
    intro α_V hα
    have hspan := periodVApices_span_subset hκ1 hκm (by omega) hα
    set subOdd := (Ico α_V (α_V + 2 * strokeLen s0 m κ)).filter (fun c0 => c0 % 2 = 1)
    have hsub : subOdd ⊆ oddRange (dnpPeriod s0 m) := by
      intro c0 hc0
      rw [mem_filter, mem_Ico] at hc0
      rw [oddRange, mem_filter, mem_range]
      exact ⟨by omega, hc0.2⟩
    have hzero : ∀ c0 ∈ oddRange (dnpPeriod s0 m), c0 ∉ subOdd →
        (straddleSet (c0 : ℤ) (α_V : ℤ) (strokeLen s0 m κ) R_k).card = 0 := by
      intro c0 hc0 hnot
      rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
      intro hne
      have hmem := center_mem_span_of_straddleSet_nonempty hne
      rw [oddRange, mem_filter] at hc0
      apply hnot
      rw [mem_filter, mem_Ico]
      exact ⟨⟨by omega, by omega⟩, hc0.2⟩
    rw [← Finset.sum_subset hsub hzero, heven_pi]
    have hparity := sum_straddleSet_card_parity (α_V : ℤ) L R_k (by omega : 2 * L ≤ R_k)
      (Or.inr rfl : (1 : ℤ) = 0 ∨ (1 : ℤ) = 1)
    rw [← hparity]
    refine Finset.sum_bij (fun (c0 : ℕ) _ => (c0 : ℤ)) ?_ ?_ ?_ ?_
    · intro c0 hc0
      rw [mem_filter, mem_Ico] at hc0
      rw [mem_filter, mem_Ico]
      refine ⟨⟨by omega, by push_cast; omega⟩, ?_⟩
      omega
    · intro a _ b _ h; exact Int.ofNat.inj h
    · intro cz hcz
      rw [mem_filter, mem_Ico] at hcz
      refine ⟨cz.toNat, ?_, Int.toNat_of_nonneg (by omega)⟩
      rw [mem_filter, mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      omega
    · intros; rfl
  rw [Finset.sum_congr rfl hper_V, Finset.sum_const,
    card_periodVApices hκ1 hκm (by omega), smul_eq_mul]

/-- Total straddling apex half-widths of coarse class `k` (`dir = true` for head `1` at `(c + ξ) % P`,
`dir = false` for head `2` at `(c + P - ξ) % P`) against level-`κ` V's at shift `ξ`. -/
def classStraddleCount (s0 m k κ : ℕ) (dir : Bool) (ξ : ℕ) : ℕ :=
  let P := dnpPeriod s0 m
  ∑ c ∈ periodVApices s0 m k,
    totalStraddleAtCenter s0 m κ (scaleR s0 k) (if dir then (c + ξ) % P else (c + P - ξ) % P)

theorem classStraddleCount_le {s0 m k κ : ℕ}
    (hk1 : 1 ≤ k) (hkm : k ≤ m) (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m ≤ s0)
    (dir : Bool) (ξ : ℕ) :
    classStraddleCount s0 m k κ dir ξ ≤ 2 ^ (k + 1) * strokeLen s0 m κ := by
  unfold classStraddleCount
  calc ∑ c ∈ periodVApices s0 m k, _
      ≤ ∑ _c ∈ periodVApices s0 m k, strokeLen s0 m κ :=
        Finset.sum_le_sum (fun _ _ => totalStraddleAtCenter_le hκ1 hκm hms _)
    _ = 2 ^ (k + 1) * strokeLen s0 m κ := by
        rw [Finset.sum_const, card_periodVApices hk1 hkm hms, smul_eq_mul]

/-- **Exact Odd-Shift Straddle Sum (`Theorem A(b)`)**:
Summing `classStraddleCount` over all `P / 2` odd shifts `ξ ∈ oddRange P` (`m < s₀`, `Π_κ ≤ R_k`)
yields the exact value `2^(k + 1) · 2^(κ + 1) · (Π_κ / 2)^2` for **both** head directions `dir`. -/
theorem sum_classStraddleCount_odd {s0 m k κ : ℕ}
    (hk1 : 1 ≤ k) (hkm : k ≤ m) (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m < s0)
    (hpi : strokeLen s0 m κ ≤ scaleR s0 k) (dir : Bool) :
    ∑ ξ ∈ oddRange (dnpPeriod s0 m), classStraddleCount s0 m k κ dir ξ =
      2 ^ (k + 1) * (2 ^ (κ + 1) * (strokeLen s0 m κ / 2) ^ 2) := by
  unfold classStraddleCount
  rw [Finset.sum_comm]
  set P := dnpPeriod s0 m
  have hP_pos : 0 < P := by unfold P dnpPeriod; exact Nat.mul_pos (by omega) (strokeLen_pos s0 m 0)
  have hP_even : P % 2 = 0 := by
    unfold P dnpPeriod
    have := Nat.dvd_iff_mod_eq_zero.mp (even_strokeLen (s0 := s0) (m := m) (by omega : 0 < s0))
    omega
  have hper_c : ∀ c ∈ periodVApices s0 m k,
      ∑ ξ ∈ oddRange P, totalStraddleAtCenter s0 m κ (scaleR s0 k)
        (if dir then (c + ξ) % P else (c + P - ξ) % P) =
        2 ^ (κ + 1) * (strokeLen s0 m κ / 2) ^ 2 := by
    intro c hc
    have hc_lt : c < P := by
      have hsp := periodVApices_span_subset hk1 hkm (by omega) hc
      have hp := strokeLen_pos s0 m k
      omega
    have hc_even : c % 2 = 0 := even_of_mem_periodVApices hk1 hkm hms hc
    rw [← sum_totalStraddleAtCenter_odd hκ1 hκm hms hpi]
    cases dir
    · refine Finset.sum_bij (fun ξ _ => (c + P - ξ) % P) ?_ ?_ ?_ ?_
      · intro ξ hξ
        rw [oddRange, mem_filter, mem_range] at hξ ⊢
        refine ⟨Nat.mod_lt _ hP_pos, ?_⟩
        by_cases hle : ξ ≤ c
        · have heq : (c + P - ξ) % P = c - ξ := by
            rw [show c + P - ξ = (c - ξ) + P by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          rw [heq]; omega
        · have heq : (c + P - ξ) % P = c + P - ξ := Nat.mod_eq_of_lt (by omega)
          rw [heq]; omega
      · intro ξ₁ h₁ ξ₂ h₂ heq
        rw [oddRange, mem_filter, mem_range] at h₁ h₂
        by_cases ha : ξ₁ ≤ c <;> by_cases hb : ξ₂ ≤ c
        · rw [show c + P - ξ₁ = (c - ξ₁) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega),
            show c + P - ξ₂ = (c - ξ₂) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at heq
          omega
        · rw [show c + P - ξ₁ = (c - ξ₁) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega : c + P - ξ₂ < P)] at heq
          omega
        · rw [Nat.mod_eq_of_lt (by omega : c + P - ξ₁ < P),
            show c + P - ξ₂ = (c - ξ₂) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at heq
          omega
        · rw [Nat.mod_eq_of_lt (by omega : c + P - ξ₁ < P),
            Nat.mod_eq_of_lt (by omega : c + P - ξ₂ < P)] at heq
          omega
      · intro y hy
        rw [oddRange, mem_filter, mem_range] at hy
        refine ⟨(c + P - y) % P, ?_, ?_⟩
        · rw [oddRange, mem_filter, mem_range]
          refine ⟨Nat.mod_lt _ hP_pos, ?_⟩
          by_cases hle : y ≤ c
          · have heq : (c + P - y) % P = c - y := by
              rw [show c + P - y = (c - y) + P by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            rw [heq]; omega
          · have heq : (c + P - y) % P = c + P - y := Nat.mod_eq_of_lt (by omega)
            rw [heq]; omega
        · by_cases hle : y ≤ c
          · have h1 : (c + P - y) % P = c - y := by
              rw [show c + P - y = (c - y) + P by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            rw [h1, show c + P - (c - y) = y + P by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt hy.1]
          · have h1 : (c + P - y) % P = c + P - y := Nat.mod_eq_of_lt (by omega)
            rw [h1, show c + P - (c + P - y) = y by omega, Nat.mod_eq_of_lt hy.1]
      · intros; simp
    · refine Finset.sum_bij (fun ξ _ => (c + ξ) % P) ?_ ?_ ?_ ?_
      · intro ξ hξ
        rw [oddRange, mem_filter, mem_range] at hξ ⊢
        refine ⟨Nat.mod_lt _ hP_pos, ?_⟩
        by_cases hlt : c + ξ < P
        · have heq : (c + ξ) % P = c + ξ := Nat.mod_eq_of_lt hlt
          rw [heq]; omega
        · have heq : (c + ξ) % P = c + ξ - P := by
            conv_lhs => rw [show c + ξ = (c + ξ - P) + P by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [heq]; omega
      · intro ξ₁ h₁ ξ₂ h₂ heq
        rw [oddRange, mem_filter, mem_range] at h₁ h₂
        by_cases ha : c + ξ₁ < P <;> by_cases hb : c + ξ₂ < P
        · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at heq; omega
        · rw [Nat.mod_eq_of_lt ha, show c + ξ₂ = (c + ξ₂ - P) + P by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq; omega
        · rw [show c + ξ₁ = (c + ξ₁ - P) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb] at heq; omega
        · rw [show c + ξ₁ = (c + ξ₁ - P) + P by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega), show c + ξ₂ = (c + ξ₂ - P) + P by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq; omega
      · intro y hy
        rw [oddRange, mem_filter, mem_range] at hy
        refine ⟨(y + P - c) % P, ?_, ?_⟩
        · rw [oddRange, mem_filter, mem_range]
          refine ⟨Nat.mod_lt _ hP_pos, ?_⟩
          by_cases hle : c ≤ y
          · have heq : (y + P - c) % P = y - c := by
              rw [show y + P - c = (y - c) + P by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            rw [heq]; omega
          · have heq : (y + P - c) % P = y + P - c := Nat.mod_eq_of_lt (by omega)
            rw [heq]; omega
        · by_cases hle : c ≤ y
          · have h1 : (y + P - c) % P = y - c := by
              rw [show y + P - c = (y - c) + P by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            rw [h1, show c + (y - c) = y by omega, Nat.mod_eq_of_lt hy.1]
          · have h1 : (y + P - c) % P = y + P - c := Nat.mod_eq_of_lt (by omega)
            rw [h1, show c + (y + P - c) = y + P by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt hy.1]
      · intros; simp
  rw [Finset.sum_congr rfl hper_c, Finset.sum_const,
    card_periodVApices hk1 hkm (by omega), smul_eq_mul]

/-- Pure `ℕ` Reverse-Markov lemma (single bounded random variable):
if `X : α → ℕ` satisfies `X ξ ≤ M` (`0 < M`) on `Ω` and `num * |Ω| * M ≤ den * ∑_{ξ ∈ Ω} X ξ`,
then `num * |Ω| ≤ 2 * den * |{ξ ∈ Ω : num * M ≤ 2 * den * X ξ}|`. -/
theorem reverse_markov_single {α : Type*} [DecidableEq α] (Ω : Finset α) (X : α → ℕ)
    {M num den : ℕ} (hM : 0 < M)
    (hbound : ∀ ξ ∈ Ω, X ξ ≤ M)
    (hmean : num * Ω.card * M ≤ den * ∑ ξ ∈ Ω, X ξ) :
    num * Ω.card ≤ 2 * den * (Ω.filter (fun ξ => num * M ≤ 2 * den * X ξ)).card := by
  set G := Ω.filter (fun ξ => num * M ≤ 2 * den * X ξ)
  set B := Ω.filter (fun ξ => ¬(num * M ≤ 2 * den * X ξ))
  have hsplit : ∑ ξ ∈ Ω, 2 * den * X ξ =
      (∑ ξ ∈ G, 2 * den * X ξ) + ∑ ξ ∈ B, 2 * den * X ξ :=
    (Finset.sum_filter_add_sum_filter_not Ω (fun ξ => num * M ≤ 2 * den * X ξ) _).symm
  have hG_le : ∑ ξ ∈ G, 2 * den * X ξ ≤ G.card * (2 * den * M) := by
    calc ∑ ξ ∈ G, 2 * den * X ξ
        ≤ ∑ _ξ ∈ G, 2 * den * M :=
          Finset.sum_le_sum (fun ξ hξ => Nat.mul_le_mul_left _ (hbound ξ (mem_filter.mp hξ).1))
      _ = G.card * (2 * den * M) := by simp [Finset.sum_const, smul_eq_mul]
  have hB_le : ∑ ξ ∈ B, 2 * den * X ξ ≤ Ω.card * (num * M) := by
    have hB_card : B.card ≤ Ω.card := Finset.card_filter_le _ _
    calc ∑ ξ ∈ B, 2 * den * X ξ
        ≤ ∑ _ξ ∈ B, num * M :=
          Finset.sum_le_sum (fun ξ hξ => by have := (mem_filter.mp hξ).2; omega)
      _ = B.card * (num * M) := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ Ω.card * (num * M) := Nat.mul_le_mul_right _ hB_card
  have hsum2 : 2 * (den * ∑ ξ ∈ Ω, X ξ) = ∑ ξ ∈ Ω, 2 * den * X ξ := by
    rw [← Finset.mul_sum]; ring_nf
  have htot : 2 * (num * Ω.card * M) ≤ G.card * (2 * den * M) + Ω.card * (num * M) := by
    calc 2 * (num * Ω.card * M)
        ≤ 2 * (den * ∑ ξ ∈ Ω, X ξ) := Nat.mul_le_mul_left 2 hmean
      _ = ∑ ξ ∈ Ω, 2 * den * X ξ := hsum2
      _ ≤ G.card * (2 * den * M) + Ω.card * (num * M) := by linarith
  have hmul : (num * Ω.card) * M ≤ (2 * den * G.card) * M := by nlinarith
  exact Nat.le_of_mul_le_mul_right hmul hM

/-- **Simultaneous Reverse-Markov Shift Selection (`Theorem A(c)`)**:
Given a family `X : α → β → ℕ` over nonempty `Ω` and `Kset` with `X ξ k ≤ M k` (`0 < M k`) and
`num * |Ω| * M k ≤ den * ∑_{ξ ∈ Ω} X ξ k` for all `k ∈ Kset`, there exists a **single** `ξ ∈ Ω`
making `num * M k ≤ 2 * den * X ξ k` simultaneously for at least a `num / (2 * den)` fraction of
`k ∈ Kset`. -/
theorem reverse_markov_simultaneous {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Ω : Finset α) (Kset : Finset β) (X : α → β → ℕ) (M : β → ℕ) (num den : ℕ)
    (hΩ : Ω.Nonempty)
    (hbound : ∀ ξ ∈ Ω, ∀ k ∈ Kset, X ξ k ≤ M k)
    (hpos : ∀ k ∈ Kset, 0 < M k)
    (hmean : ∀ k ∈ Kset, num * Ω.card * M k ≤ den * ∑ ξ ∈ Ω, X ξ k) :
    ∃ ξ ∈ Ω,
      num * Kset.card ≤ 2 * den * (Kset.filter (fun k => num * M k ≤ 2 * den * X ξ k)).card := by
  let goodK : α → ℕ := fun ξ => (Kset.filter (fun k => num * M k ≤ 2 * den * X ξ k)).card
  have hswap : ∑ ξ ∈ Ω, goodK ξ =
      ∑ k ∈ Kset, (Ω.filter (fun ξ => num * M k ≤ 2 * den * X ξ k)).card := by
    simp only [goodK, Finset.card_filter]
    exact Finset.sum_comm
  have hsum_ge : Ω.card * (num * Kset.card) ≤ ∑ ξ ∈ Ω, 2 * den * goodK ξ := by
    rw [← Finset.mul_sum, hswap, Finset.mul_sum]
    calc Ω.card * (num * Kset.card)
        = ∑ _k ∈ Kset, num * Ω.card := by simp [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ ∑ k ∈ Kset, 2 * den * (Ω.filter (fun ξ => num * M k ≤ 2 * den * X ξ k)).card :=
          Finset.sum_le_sum (fun k hk =>
            reverse_markov_single Ω (fun ξ => X ξ k) (hpos k hk)
              (fun ξ hξ => hbound ξ hξ k hk) (hmean k hk))
  by_contra hno
  push Not at hno
  have hlt : ∑ ξ ∈ Ω, 2 * den * goodK ξ < Ω.card * (num * Kset.card) := by
    calc ∑ ξ ∈ Ω, 2 * den * goodK ξ
        < ∑ _ξ ∈ Ω, num * Kset.card :=
          Finset.sum_lt_sum_of_nonempty hΩ (fun ξ hξ => hno ξ hξ)
      _ = Ω.card * (num * Kset.card) := by simp [Finset.sum_const, smul_eq_mul]
  omega

/-- Explicit canceller level `κ(m, a, k)` below `k + (Nat.log 2 (m + 1) + 1)` with
`isCanceller m a κ = true` and `Π_κ ≤ R_k`. -/
def cancellerBelow (m a k : ℕ) : ℕ :=
  let base := k + (Nat.log 2 (m + 1) + 1)
  base + ((m - base) % (a + 1) + 1) % (a + 1)

theorem cancellerBelow_props {s0 m a k : ℕ} (_ha : 1 ≤ a) (hms : m ≤ s0)
    (hk1 : 1 ≤ k) (hfit : k + (Nat.log 2 (m + 1) + 1) + a ≤ m)
    (hcoarse : 2 * (k + (Nat.log 2 (m + 1) + 1) + a) ≤ m + 1) :
    let κ := cancellerBelow m a k
    1 ≤ κ ∧ κ ≤ m ∧
    isCanceller m a κ = true ∧
    strokeLen s0 m κ ≤ scaleR s0 k ∧
    scaleR s0 k ≤ 2 ^ (a + 2) * strokeLen s0 m κ ∧
    m + 1 ≤ 2 * (m - κ + 1) := by
  intro κ
  set j0 := Nat.log 2 (m + 1) + 1
  set base := k + j0
  set r := (m - base) % (a + 1)
  set δ := (r + 1) % (a + 1)
  have hκ_eq : κ = base + δ := rfl
  have hr_lt : r < a + 1 := Nat.mod_lt _ (by omega)
  have hδ_lt : δ < a + 1 := Nat.mod_lt _ (by omega)
  have hκ_le_m : κ ≤ m := by omega
  have hκ1 : 1 ≤ κ := by omega
  have hcanc : isCanceller m a κ = true := by
    unfold isCanceller
    rw [beq_iff_eq]
    have hdiv := Nat.div_add_mod (m - base) (a + 1)
    by_cases hra : r = a
    · have hδ0 : δ = 0 := by dsimp [δ]; rw [hra, Nat.mod_self]
      rw [hκ_eq, hδ0, add_zero]; exact hra
    · have hδ_val : δ = r + 1 := Nat.mod_eq_of_lt (by omega)
      set qd := (m - base) / (a + 1)
      have hdiv_eq : (a + 1) * qd + r = m - base := hdiv
      have hge : a + 1 ≤ (a + 1) * qd + r := by omega
      have hqd_pos : 1 ≤ qd := by
        rcases hy : qd with _ | qd'
        · rw [hy, mul_zero, zero_add] at hge; omega
        · omega
      have hmul_sub : (a + 1) * qd = (a + 1) * (qd - 1) + (a + 1) := by
        conv_lhs => rw [show qd = (qd - 1) + 1 by omega]
        ring
      have hsub : m - κ = a + (a + 1) * (qd - 1) := by
        rw [hκ_eq, hδ_val]
        omega
      rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hj0_pow : m + 1 < 2 ^ j0 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m + 1)
  have hj0_le : j0 ≤ κ - k := by omega
  have hpow_le : m - κ + 1 ≤ 2 ^ (κ - k) :=
    calc m - κ + 1 ≤ m + 1 := by omega
      _ ≤ 2 ^ j0 := Nat.le_of_lt hj0_pow
      _ ≤ 2 ^ (κ - k) := Nat.pow_le_pow_right (by omega) hj0_le
  have hrk_eq : scaleR s0 k = 2 ^ (κ - k) * scaleR s0 κ := by
    unfold scaleR
    rw [← Nat.pow_add, show κ - k + (s0 - κ) = s0 - k by omega]
  have hpi_le : strokeLen s0 m κ ≤ scaleR s0 k := by
    unfold strokeLen
    rw [hrk_eq]
    exact Nat.mul_le_mul_right _ hpow_le
  have hlog_low : 2 ^ (j0 - 1) ≤ m + 1 := by
    dsimp [j0]
    exact Nat.pow_log_le_self 2 (by omega)
  have hκk_le : κ - k ≤ (j0 - 1) + (a + 1) := by omega
  have hpow_hi : 2 ^ (κ - k) ≤ 2 ^ (a + 1) * (m + 1) := by
    calc 2 ^ (κ - k) ≤ 2 ^ ((j0 - 1) + (a + 1)) := Nat.pow_le_pow_right (by omega) hκk_le
      _ = 2 ^ (a + 1) * 2 ^ (j0 - 1) := by rw [pow_add, mul_comm]
      _ ≤ 2 ^ (a + 1) * (m + 1) := Nat.mul_le_mul_left _ hlog_low
  have hm_half : m + 1 ≤ 2 * (m - κ + 1) := by omega
  have hrk_bound : scaleR s0 k ≤ 2 ^ (a + 2) * strokeLen s0 m κ := by
    rw [hrk_eq]
    unfold strokeLen
    calc 2 ^ (κ - k) * scaleR s0 κ
        ≤ (2 ^ (a + 1) * (m + 1)) * scaleR s0 κ := Nat.mul_le_mul_right _ hpow_hi
      _ ≤ (2 ^ (a + 1) * (2 * (m - κ + 1))) * scaleR s0 κ :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm_half)
      _ = 2 ^ (a + 2) * ((m - κ + 1) * scaleR s0 κ) := by rw [pow_succ]; ring
  exact ⟨hκ1, hκ_le_m, hcanc, hpi_le, hrk_bound, hm_half⟩

/-- **Unconditional Single-Shift Coarse Straddle Visibility (`Theorem A(d)`)**:
When `m < s₀`, `1 ≤ a`, and `4 * (Nat.log 2 (m + 1) + 1 + a) ≤ m + 1`, for either head direction
`dir : Bool`, there exists a **single odd shift** `ξ ∈ oddRange (dnpPeriod s0 m)` (independent of
`K` and `q`) such that on at least `1 / 16` of the coarse zone `K_coarse = Icc 1 ((m + 1) / 4)`,
class `(dir, k)` has at least `(2^(k + 2) * R_k) / 2^(a + 7)` straddling apex half-widths against
canceller `cancellerBelow m a k`. -/
theorem exists_oddShift_coarse_straddle {s0 m a : ℕ}
    (ha : 1 ≤ a) (hms : m < s0)
    (hcoarse_m : 4 * (Nat.log 2 (m + 1) + 1 + a) ≤ m + 1)
    (dir : Bool) :
    let Ω := oddRange (dnpPeriod s0 m)
    let Kset := Icc 1 ((m + 1) / 4)
    ∃ ξ ∈ Ω,
      Kset.card ≤ 16 * (Kset.filter (fun k =>
        2 ^ (k + 2) * scaleR s0 k ≤
          2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) dir ξ)).card := by
  intro Ω Kset
  set P := dnpPeriod s0 m
  have heven_pi0 : 2 ∣ strokeLen s0 m 0 := even_strokeLen (by omega : 0 < s0)
  obtain ⟨M0, hM0⟩ := heven_pi0
  have hP_2 : P = 2 * (4 * M0) := by unfold P dnpPeriod; rw [hM0]; ring
  have hΩ_card : Ω.card = 4 * M0 := by
    change (oddRange P).card = 4 * M0
    rw [hP_2]
    exact card_oddRange_two_mul _
  have hM0_pos : 0 < M0 := by have := strokeLen_pos s0 m 0; omega
  have hΩ_ne : Ω.Nonempty := Finset.card_pos.mp (by omega)
  let κf : ℕ → ℕ := fun k => cancellerBelow m a k
  let M : ℕ → ℕ := fun k => 2 ^ (k + 1) * strokeLen s0 m (κf k)
  have hk_props : ∀ k ∈ Kset,
      1 ≤ κf k ∧ κf k ≤ m ∧
      isCanceller m a (κf k) = true ∧
      strokeLen s0 m (κf k) ≤ scaleR s0 k ∧
      scaleR s0 k ≤ 2 ^ (a + 2) * strokeLen s0 m (κf k) ∧
      m + 1 ≤ 2 * (m - κf k + 1) := by
    intro k hk
    rw [mem_Icc] at hk
    exact @cancellerBelow_props s0 m a k ha (by omega) hk.1 (by omega) (by omega)
  have hbound : ∀ ξ ∈ Ω, ∀ k ∈ Kset, classStraddleCount s0 m k (κf k) dir ξ ≤ M k := by
    intro ξ _ k hk
    rw [mem_Icc] at hk
    obtain ⟨hκ1, hκm, _⟩ := hk_props k (mem_Icc.mpr hk)
    exact classStraddleCount_le hk.1 (by omega) hκ1 hκm (by omega) dir ξ
  have hpos : ∀ k ∈ Kset, 0 < M k := by
    intro k _
    exact Nat.mul_pos (by positivity) (strokeLen_pos s0 m (κf k))
  have hmean : ∀ k ∈ Kset,
      1 * Ω.card * M k ≤ 8 * ∑ ξ ∈ Ω, classStraddleCount s0 m k (κf k) dir ξ := by
    intro k hk
    obtain ⟨hκ1, hκm, -, hpi, -, hm_half⟩ := hk_props k hk
    have hk_mem := mem_Icc.mp hk
    rw [sum_classStraddleCount_odd hk_mem.1 (by omega) hκ1 hκm hms hpi dir]
    obtain ⟨L, hL⟩ := even_strokeLen (s0 := s0) (m := m) (by omega : κf k < s0)
    have hL_div : strokeLen s0 m (κf k) / 2 = L := by omega
    rw [hL_div]
    have hr0_eq : scaleR s0 0 = 2 ^ (κf k) * scaleR s0 (κf k) := by
      unfold scaleR
      rw [← Nat.pow_add, Nat.sub_zero, show κf k + (s0 - κf k) = s0 by omega]
    have hP_eq : P = 2 * (2 * (m + 1) * (2 ^ (κf k) * scaleR s0 (κf k))) := by
      unfold P dnpPeriod strokeLen
      rw [Nat.sub_zero, hr0_eq]
      ring
    have hΩ_eq : Ω.card = 2 * (m + 1) * (2 ^ (κf k) * scaleR s0 (κf k)) := by
      change (oddRange P).card = _
      rw [hP_eq]
      exact card_oddRange_two_mul _
    have h2L : (m - κf k + 1) * scaleR s0 (κf k) = 2 * L := hL
    dsimp [M]
    rw [hΩ_eq, hL]
    have hstep : (m + 1) * scaleR s0 (κf k) ≤ 4 * L := by
      calc (m + 1) * scaleR s0 (κf k)
          ≤ 2 * (m - κf k + 1) * scaleR s0 (κf k) := Nat.mul_le_mul_right _ hm_half
        _ = 2 * ((m - κf k + 1) * scaleR s0 (κf k)) := by ring
        _ = 4 * L := by rw [h2L]; ring
    calc 1 * (2 * (m + 1) * (2 ^ κf k * scaleR s0 (κf k))) * (2 ^ (k + 1) * (2 * L))
        = ((m + 1) * scaleR s0 (κf k)) * (4 * 2 ^ κf k * 2 ^ (k + 1) * L) := by ring
      _ ≤ (4 * L) * (4 * 2 ^ κf k * 2 ^ (k + 1) * L) := Nat.mul_le_mul_right _ hstep
      _ = 8 * (2 ^ (k + 1) * (2 ^ (κf k + 1) * L ^ 2)) := by rw [pow_succ]; ring
  obtain ⟨ξ, hξ, hcard⟩ := reverse_markov_simultaneous Ω Kset
    (fun ξ k => classStraddleCount s0 m k (κf k) dir ξ) M 1 8 hΩ_ne hbound hpos hmean
  refine ⟨ξ, hξ, ?_⟩
  have hsub : Kset.filter (fun k => 1 * M k ≤ 2 * 8 * classStraddleCount s0 m k (κf k) dir ξ) ⊆
      Kset.filter (fun k =>
        2 ^ (k + 2) * scaleR s0 k ≤
          2 ^ (a + 7) * classStraddleCount s0 m k (κf k) dir ξ) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    obtain ⟨_, _, _, _, hrk_le, _⟩ := hk_props k hk.1
    have hMk : 2 ^ (k + 1) * strokeLen s0 m (κf k) ≤
        16 * classStraddleCount s0 m k (κf k) dir ξ := by
      dsimp [M] at hk; omega
    calc 2 ^ (k + 2) * scaleR s0 k
        = 2 * (2 ^ (k + 1) * scaleR s0 k) := by rw [pow_succ]; ring
      _ ≤ 2 * (2 ^ (k + 1) * (2 ^ (a + 2) * strokeLen s0 m (κf k))) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hrk_le)
      _ = 2 ^ (a + 3) * (2 ^ (k + 1) * strokeLen s0 m (κf k)) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (a + 3) * (16 * classStraddleCount s0 m k (κf k) dir ξ) :=
          Nat.mul_le_mul_left _ hMk
      _ = 2 ^ (a + 7) * classStraddleCount s0 m k (κf k) dir ξ := by
          rw [show a + 7 = (a + 3) + 4 by omega, pow_add]; ring
  have hle := Finset.card_le_card hsub
  dsimp [κf] at hcard hle
  omega

/-! ### Part 4: Three-Regime Mod-`q` Completeness & `Theorem A` -/

/-- **Small-`Q̃` Mod-`q` Straddle Residue Lower Bound (`Theorem A(e)`)**:
Let `q > 0`, `1 ≤ a₁`, `K̃₁ = K₁ % q`, `K̃₂ = K₂ % q`, `Q̃₁ = blockQ a₁ K̃₁`, and `Q̃₂ = blockQ a₂ K̃₂`.
Whenever `Q̃₁ ≤ Q̃₂` and `4 * Q̃₂ + 4 ≤ q`, for **every** level `k` of head `1` and **every**
canceller level `κ` of `B(a₂, K₂)`, the `Theorem V*` straddle-pair lower bound satisfies
`q ≤ 2 * ((2 * blockA m a₁ K₁ k + 2 * (c_f(κ) - c_b(κ))) % q)` (i.e. residue `≥ q / 2`). -/
theorem block_straddle_residue_ge_half_q (m a1 a2 : ℕ) (K1 K2 : ℤ) {q : ℤ}
    (hq : 0 < q) (ha1 : 1 ≤ a1) (k κ : ℕ)
    (hcanc : isCanceller m a2 κ = true)
    (hQle : blockQ a1 (K1 % q) ≤ blockQ a2 (K2 % q))
    (hQsmall : 4 * blockQ a2 (K2 % q) + 4 ≤ q) :
    let cb2 := pathSumBack (blockA m a2 K2) κ
    let cf2 := pathSumFwd (blockA m a2 K2) (blockE m a2 K2) κ
    q ≤ 2 * ((2 * blockA m a1 K1 k + 2 * (cf2 - cb2)) % q) := by
  intro cb2 cf2
  set K1m := K1 % q
  set K2m := K2 % q
  have hK1_0 : 0 ≤ K1m := Int.emod_nonneg K1 (by omega)
  have hK2_0 : 0 ≤ K2m := Int.emod_nonneg K2 (by omega)
  set Q1m := blockQ a1 K1m
  set Q2m := blockQ a2 K2m
  have hQ1_ge : 2 * K1m + 2 ≤ Q1m := blockQ_ge_two_K_add_two ha1 hK1_0
  have hQ2_0 : 0 ≤ Q2m := blockQ_nonneg a2 hK2_0
  have hc_diff : cf2 - cb2 = -blockQ a2 K2 - 1 :=
    (block_canceller_mass m a2 K2 κ hcanc).2.2.2
  -- Reduce `K1 ↦ K1m` and `K2 ↦ K2m` modulo `q`
  have hdvd_expr : q ∣ (2 * blockA m a1 K1 k + 2 * (cf2 - cb2)) -
      (2 * blockA m a1 K1m k + 2 * (-Q2m - 1)) := by
    rw [hc_diff]
    have hK1_dvd : q ∣ K1 - K1m :=
      ⟨K1 / q, by have h := Int.emod_add_mul_ediv K1 q; linear_combination -h⟩
    have hK2_dvd : q ∣ K2 - K2m :=
      ⟨K2 / q, by have h := Int.emod_add_mul_ediv K2 q; linear_combination -h⟩
    have hA_dvd : q ∣ blockA m a1 K1 k - blockA m a1 K1m k := by
      unfold blockA; cases isCanceller m a1 k <;> simp [hK1_dvd]
    have hQ_dvd : q ∣ blockQ a2 K2 - Q2m := by
      dsimp [Q2m]; unfold blockQ
      obtain ⟨t, ht⟩ := hK2_dvd
      refine ⟨((2 ^ a2 : ℤ) - 1) * (2 * t), ?_⟩
      linear_combination ((2 ^ a2 : ℤ) - 1) * 2 * ht
    obtain ⟨t1, ht1⟩ := hA_dvd
    obtain ⟨t2, ht2⟩ := hQ_dvd
    exact ⟨2 * t1 - 2 * t2, by linarith⟩
  obtain ⟨u, hu⟩ := hdvd_expr
  set W := 2 * blockA m a1 K1m k + 2 * (-Q2m - 1)
  have hmod_eq : (2 * blockA m a1 K1 k + 2 * (cf2 - cb2)) % q = W % q := by
    have hrew : 2 * blockA m a1 K1 k + 2 * (cf2 - cb2) = W + u * q := by linarith
    rw [hrew, Int.add_mul_emod_self_right]
  rw [hmod_eq]
  have hA_bounds : 0 ≤ blockA m a1 K1m k ∧ blockA m a1 K1m k ≤ K1m := by
    unfold blockA
    cases isCanceller m a1 k <;> simp [hK1_0]
  have hW_neg : W < 0 := by dsimp [W]; linarith
  have h2W_ge : -q ≤ 2 * W := by dsimp [W]; linarith
  have hqW_nonneg : 0 ≤ q + W := by linarith
  have hqW_lt : q + W < q := by linarith
  have hW_mod : W % q = q + W := by
    conv_lhs => rw [show W = (q + W) + (-1) * q by ring]
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt hqW_nonneg hqW_lt]
  rw [hW_mod]
  linarith

private theorem exists_first_gt_Icc {a : ℕ} (ha : 1 ≤ a) (f : ℕ → ℤ) (q : ℤ)
    (hlast : q < f a) :
    ∃ r, 1 ≤ r ∧ r ≤ a ∧ q < f r ∧ ∀ r', 1 ≤ r' → r' < r → f r' ≤ q := by
  classical
  have hex : ∃ r, 1 ≤ r ∧ r ≤ a ∧ q < f r := ⟨a, ha, le_refl a, hlast⟩
  let r := Nat.find hex
  obtain ⟨hr1, hra, hgt⟩ := Nat.find_spec hex
  refine ⟨r, hr1, hra, hgt, ?_⟩
  intro r' hr'1 hr'lt
  have hnot := Nat.find_min hex hr'lt
  push Not at hnot
  exact hnot hr'1 (by omega)

/-- **Large-`Q̃` Blind Fine Overflow Witness (`Theorem A(f)`)**:
Let `a ≥ 1`, `q ≥ 32`, and `K : ℤ`. Whenever `q < 4 * blockQ a (K % q) + 4`, there exists a served
residue `rem < a` such that **every** level `k < m` with `(m - k) % (a + 1) = rem` (`1` in every
`a + 1` consecutive levels) has a single-head reduced apex, band-`0`, or band-`1` error at least
`q / 16`:
`q ≤ 16 * blindApexErr ... k ∨ q ≤ 8 * blindBandErr ... k k ∨ q ≤ 8 * blindBandErr ... k (k + 1)`. -/
theorem block_overflow_band_witness (m a : ℕ) (K : ℤ) {q : ℤ}
    (ha : 1 ≤ a) (hq : 32 ≤ q)
    (hover : q < 4 * blockQ a (K % q) + 4) :
    ∃ rem < a, ∀ k < m, (m - k) % (a + 1) = rem →
      q ≤ 16 * blindApexErr (blockA m a K) q k ∨
      q ≤ 8 * blindBandErr (blockA m a K) (blockE m a K) q k k ∨
      q ≤ 8 * blindBandErr (blockA m a K) (blockE m a K) q k (k + 1) := by
  have hq_pos : 0 < q := by omega
  obtain ⟨hap_mod, hbd_mod⟩ := block_blind_errors_mod_K m a K hq_pos
  set Km := K % q
  have hKm0 : 0 ≤ Km := Int.emod_nonneg K (by omega)
  have hKm_lt : Km < q := Int.emod_lt_of_pos K hq_pos
  by_cases hK_big : q ≤ 16 * Km
  · refine ⟨0, by omega, ?_⟩
    intro k _ hrem
    left
    rw [hap_mod k]
    have hc : isCanceller m a k = false := by
      unfold isCanceller; rw [beq_eq_false_iff_ne]; omega
    unfold blindApexErr blockA
    rw [hc]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.emod_eq_of_lt hKm0 hKm_lt]
    exact hK_big
  · push Not at hK_big
    let T : ℕ → ℤ := fun r => ((2 ^ r : ℤ) - 1) * (2 * Km + 2)
    have hTa : T a = blockQ a Km := rfl
    have h8Ta : q < 8 * T a := by rw [hTa]; linarith
    have h4T1 : 4 * T 1 < q := by
      dsimp [T]; norm_num; linarith
    obtain ⟨r, hr1, hra, hr_gt, hr_min⟩ := exists_first_gt_Icc ha (fun r => 8 * T r) q h8Ta
    have hTr0 : 0 ≤ T r := by
      dsimp [T]
      have : (1 : ℤ) ≤ 2 ^ r := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
      nlinarith
    have h2Tr_lt : 2 * T r < q := by
      by_cases hr_eq1 : r = 1
      · subst hr_eq1; linarith
      · have hprev := hr_min (r - 1) (by omega) (by omega)
        have hrec : T r = 2 * T (r - 1) + T 1 := by
          dsimp [T]
          conv_lhs => rw [show r = (r - 1) + 1 by omega]
          rw [pow_succ]
          ring
        linarith
    have hsum_nonneg : 0 ≤ Km + T r := by linarith
    have hsum_lt_q : Km + T r < q := by linarith
    have h8sum : q ≤ 8 * ((Km + T r) % q) := by
      rw [Int.emod_eq_of_lt hsum_nonneg hsum_lt_q]
      linarith
    by_cases hr_lt_a : r < a
    · refine ⟨r, hr_lt_a, ?_⟩
      intro k _ hrem
      right; left
      rw [hbd_mod k k, blindBandErr_self]
      have hc : isCanceller m a k = false := by
        unfold isCanceller; rw [beq_eq_false_iff_ne]; omega
      unfold blockE
      rw [hc]
      simp only [Bool.false_eq_true, ↓reduceIte, hrem]
      exact h8sum
    · have hr_eq_a : r = a := by omega
      subst r
      refine ⟨0, by omega, ?_⟩
      intro k hkm hrem
      right; right
      rw [hbd_mod k (k + 1)]
      have hc_k : isCanceller m a k = false := by
        unfold isCanceller; rw [beq_eq_false_iff_ne]; omega
      have hc_next : isCanceller m a (k + 1) = true := by
        unfold isCanceller; rw [beq_iff_eq]
        have hdiv := Nat.div_add_mod (m - k) (a + 1)
        rw [hrem, add_zero] at hdiv
        set qd := (m - k) / (a + 1)
        have hdiv_eq : (a + 1) * qd = m - k := hdiv
        have hqd1 : 1 ≤ qd := by
          rcases hy : qd with _ | qd'
          · rw [hy, mul_zero] at hdiv_eq; omega
          · omega
        have hmul_sub : (a + 1) * qd = (a + 1) * (qd - 1) + (a + 1) := by
          conv_lhs => rw [show qd = (qd - 1) + 1 by omega]
          ring
        have hsub : m - (k + 1) = a + (a + 1) * (qd - 1) := by omega
        rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hEk : blockE m a Km k = Km := by
        unfold blockE; rw [hc_k]; simp [hrem]
      have hAnext := (block_canceller_mass m a Km (k + 1) hc_next).1
      have hIcc : Icc (k + 1) (k + 1) = {k + 1} := by
        ext i; simp only [mem_Icc, mem_singleton]; omega
      unfold blindBandErr
      rw [hIcc, Finset.sum_singleton, hEk, hAnext]
      have hrew : Km - -blockQ a Km = Km + T a := by dsimp [T]; unfold blockQ; ring
      rw [hrew]
      exact h8sum

/-- **Theorem A (`Three-Regime Witnesses for Bounded-Range Block Pairs`)**:
Let `1 ≤ a₁, a₂`, `m < s₀`, `4 * (Nat.log 2 (m + 1) + 1 + max a₁ a₂) ≤ m + 1`, and choose once
and for all the two canonical odd shifts `ξ₁ ∈ oddRange P` (for `dir = true` against `a₂`) and
`ξ₂ ∈ oddRange P` (for `dir = false` against `a₁`), independent of `K₁, K₂, q`. Then for **every**
`K₁, K₂ : ℤ` and **every** modulus `q ≥ 3`, one of the following three failure witnesses holds:

1. **Small-`q` Super-Fibonacci Regime (`3 ≤ q < 32`)**: On head `1`, in **every** run `[k₀, k₀ + 11)`
   of `11` consecutive levels, at least one level has a single-head reduced apex or band-`0, 1, 2`
   error strictly exceeding `q / 8`;
2. **Large-`Q̃` Blind Fine Overflow Regime (`32 ≤ q` and `q < 4 * Q̃_h + 4` for some `h ∈ {1, 2}`)**:
   On head `h`, there is a served residue `rem < a_h` such that **every** level `k < m` with
   `(m - k) % (a_h + 1) = rem` has a single-head reduced apex, band-`0`, or band-`1` error at least
   `q / 16`;
3. **Small-`Q̃` Coarse Straddle Regime (`32 ≤ q`, `4 * Q̃₁ + 4 ≤ q`, and `4 * Q̃₂ + 4 ≤ q`)**:
   - if `Q̃₁ ≤ Q̃₂`, then at odd shift `ξ₁`, at least `1 / 16` of the coarse zone
     `k ∈ Icc 1 ((m + 1) / 4)` of head `1` has straddle count
     `≥ (2^(k + 2) * R_k) / 2^(a₂ + 7)` AND mod-`q` straddle-pair residue `≥ q / 2`;
   - if `Q̃₂ < Q̃₁`, then at odd shift `ξ₂`, at least `1 / 16` of the coarse zone
     `k ∈ Icc 1 ((m + 1) / 4)` of head `2` has straddle count
     `≥ (2^(k + 2) * R_k) / 2^(a₁ + 7)` AND mod-`q` straddle-pair residue `≥ q / 2`. -/
theorem theoremA_three_regimes {s0 m a1 a2 : ℕ}
    (ha1 : 1 ≤ a1) (ha2 : 1 ≤ a2) (hms : m < s0)
    (hcoarse_m : 4 * (Nat.log 2 (m + 1) + 1 + max a1 a2) ≤ m + 1) :
    let Ω := oddRange (dnpPeriod s0 m)
    let Kset := Icc 1 ((m + 1) / 4)
    ∃ ξ₁ ∈ Ω, ∃ ξ₂ ∈ Ω,
      ∀ (K1 K2 q : ℤ), 3 ≤ q →
        -- Regime 1 (`3 ≤ q < 32`): every 11 consecutive levels have a single-head error > q / 8
        ((q < 32 ∧ ∀ k0 : ℕ, ∃ i < 11,
            q < 8 * blindApexErr (blockA m a1 K1) q (k0 + i) ∨
            q < 8 * blindBandErr (blockA m a1 K1) (blockE m a1 K1) q (k0 + i) (k0 + i) ∨
            q < 8 * blindBandErr (blockA m a1 K1) (blockE m a1 K1) q (k0 + i) (k0 + i + 1) ∨
            q < 8 * blindBandErr (blockA m a1 K1) (blockE m a1 K1) q (k0 + i) (k0 + i + 2)) ∨
        -- Regime 2a (`32 ≤ q` & head 1 overflows): 1 in every `a1 + 1` levels has error ≥ q / 16
        (32 ≤ q ∧ ∃ rem < a1, ∀ k < m, (m - k) % (a1 + 1) = rem →
            q ≤ 16 * blindApexErr (blockA m a1 K1) q k ∨
            q ≤ 8 * blindBandErr (blockA m a1 K1) (blockE m a1 K1) q k k ∨
            q ≤ 8 * blindBandErr (blockA m a1 K1) (blockE m a1 K1) q k (k + 1)) ∨
        -- Regime 2b (`32 ≤ q` & head 2 overflows): 1 in every `a2 + 1` levels has error ≥ q / 16
        (32 ≤ q ∧ ∃ rem < a2, ∀ k < m, (m - k) % (a2 + 1) = rem →
            q ≤ 16 * blindApexErr (blockA m a2 K2) q k ∨
            q ≤ 8 * blindBandErr (blockA m a2 K2) (blockE m a2 K2) q k k ∨
            q ≤ 8 * blindBandErr (blockA m a2 K2) (blockE m a2 K2) q k (k + 1)) ∨
        -- Regime 3a (`32 ≤ q`, small Q̃, `Q̃₁ ≤ Q̃₂` at shift `ξ₁`)
        (Kset.card ≤ 16 * (Kset.filter (fun k =>
            let κ := cancellerBelow m a2 k
            2 ^ (k + 2) * scaleR s0 k ≤
              2 ^ (a2 + 7) * classStraddleCount s0 m k κ true ξ₁ ∧
            q ≤ 2 * ((2 * blockA m a1 K1 k +
              2 * (pathSumFwd (blockA m a2 K2) (blockE m a2 K2) κ -
                pathSumBack (blockA m a2 K2) κ)) % q))).card) ∨
        -- Regime 3b (`32 ≤ q`, small Q̃, `Q̃₂ < Q̃₁` at shift `ξ₂`)
        (Kset.card ≤ 16 * (Kset.filter (fun k =>
            let κ := cancellerBelow m a1 k
            2 ^ (k + 2) * scaleR s0 k ≤
              2 ^ (a1 + 7) * classStraddleCount s0 m k κ false ξ₂ ∧
            q ≤ 2 * ((2 * blockA m a2 K2 k +
              2 * (pathSumFwd (blockA m a1 K1) (blockE m a1 K1) κ -
                pathSumBack (blockA m a1 K1) κ)) % q))).card)) := by
  intro Ω Kset
  have hm_a2 : 4 * (Nat.log 2 (m + 1) + 1 + a2) ≤ m + 1 := by
    have : a2 ≤ max a1 a2 := le_max_right a1 a2; omega
  have hm_a1 : 4 * (Nat.log 2 (m + 1) + 1 + a1) ≤ m + 1 := by
    have : a1 ≤ max a1 a2 := le_max_left a1 a2; omega
  obtain ⟨ξ₁, hξ₁, hstr₁⟩ := exists_oddShift_coarse_straddle ha2 hms hm_a2 true
  obtain ⟨ξ₂, hξ₂, hstr₂⟩ := exists_oddShift_coarse_straddle ha1 hms hm_a1 false
  refine ⟨ξ₁, hξ₁, ξ₂, hξ₂, ?_⟩
  intro K1 K2 q hq3
  by_cases hq32 : q < 32
  · -- Regime 1: `3 ≤ q < 32` via `Theorem LU` (`s = 11`, `2 * Nat.log 2 q.toNat + 2 ≤ 10 < 11`)
    left
    refine ⟨hq32, fun k0 => ?_⟩
    by_contra hall
    push Not at hall
    have hlog_le : Nat.log 2 q.toNat ≤ 4 := by
      by_contra hgt
      push Not at hgt
      have hpow : 2 ^ 5 ≤ q.toNat :=
        le_trans (Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ Nat.log 2 q.toNat))
          (Nat.pow_log_le_self 2 (by omega))
      omega
    have hLU := theoremLU_consecutive (blockA m a1 K1) (blockE m a1 K1) hq3 (k0 := k0) (s := 11)
      (by omega)
      (fun i hi => (hall i hi).1)
      (fun i hi => (hall i hi).2.1)
      (fun i hi => (hall i (by omega)).2.2.1)
      (fun i hi => (hall i (by omega)).2.2.2)
    have hs_bound := hLU.2.2
    omega
  · push Not at hq32
    by_cases hov1 : q < 4 * blockQ a1 (K1 % q) + 4
    · right; left
      exact ⟨hq32, block_overflow_band_witness m a1 K1 ha1 hq32 hov1⟩
    · by_cases hov2 : q < 4 * blockQ a2 (K2 % q) + 4
      · right; right; left
        exact ⟨hq32, block_overflow_band_witness m a2 K2 ha2 hq32 hov2⟩
      · push Not at hov1 hov2
        by_cases hQcmp : blockQ a1 (K1 % q) ≤ blockQ a2 (K2 % q)
        · right; right; right; left
          have hsub : Kset.filter (fun k =>
              2 ^ (k + 2) * scaleR s0 k ≤
                2 ^ (a2 + 7) * classStraddleCount s0 m k (cancellerBelow m a2 k) true ξ₁) ⊆
            Kset.filter (fun k =>
              let κ := cancellerBelow m a2 k
              2 ^ (k + 2) * scaleR s0 k ≤
                2 ^ (a2 + 7) * classStraddleCount s0 m k κ true ξ₁ ∧
              q ≤ 2 * ((2 * blockA m a1 K1 k +
                2 * (pathSumFwd (blockA m a2 K2) (blockE m a2 K2) κ -
                  pathSumBack (blockA m a2 K2) κ)) % q)) := by
            intro k hk
            rw [mem_filter] at hk ⊢
            have hk_mem := mem_Icc.mp hk.1
            have hcanc := (@cancellerBelow_props s0 m a2 k ha2 (by omega) hk_mem.1
              (by omega) (by omega)).2.2.1
            exact ⟨hk.1, hk.2,
              block_straddle_residue_ge_half_q m a1 a2 K1 K2 (by omega) ha1 k
                (cancellerBelow m a2 k) hcanc hQcmp hov2⟩
          have hle := Finset.card_le_card hsub
          dsimp only [Kset] at hstr₁ hle ⊢
          omega
        · push Not at hQcmp
          right; right; right; right
          have hsub : Kset.filter (fun k =>
              2 ^ (k + 2) * scaleR s0 k ≤
                2 ^ (a1 + 7) * classStraddleCount s0 m k (cancellerBelow m a1 k) false ξ₂) ⊆
            Kset.filter (fun k =>
              let κ := cancellerBelow m a1 k
              2 ^ (k + 2) * scaleR s0 k ≤
                2 ^ (a1 + 7) * classStraddleCount s0 m k κ false ξ₂ ∧
              q ≤ 2 * ((2 * blockA m a2 K2 k +
                2 * (pathSumFwd (blockA m a1 K1) (blockE m a1 K1) κ -
                  pathSumBack (blockA m a1 K1) κ)) % q)) := by
            intro k hk
            rw [mem_filter] at hk ⊢
            have hk_mem := mem_Icc.mp hk.1
            have hcanc := (@cancellerBelow_props s0 m a1 k ha1 (by omega) hk_mem.1
              (by omega) (by omega)).2.2.1
            exact ⟨hk.1, hk.2,
              block_straddle_residue_ge_half_q m a2 a1 K2 K1 (by omega) ha2 k
                (cancellerBelow m a1 k) hcanc (le_of_lt hQcmp) hov1⟩
          have hle := Finset.card_le_card hsub
          dsimp only [Kset] at hstr₂ hle ⊢
          omega

/-- **Single-Shift Specialization for All Symmetric Block Pairs (`Theorem A(g)`)**:
For any fixed block length `a ≥ 1`, there exists **one single odd shift** `ξ ∈ oddRange P` that
simultaneously witnesses failure across **all** symmetric block pairs `(B(a, K), B(a, K))`
(`K : ℤ`) and **all** moduli `q ≥ 3`. -/
theorem theoremA_symmetric_blockPair {s0 m a : ℕ}
    (ha : 1 ≤ a) (hms : m < s0)
    (hcoarse_m : 4 * (Nat.log 2 (m + 1) + 1 + a) ≤ m + 1) :
    let Ω := oddRange (dnpPeriod s0 m)
    let Kset := Icc 1 ((m + 1) / 4)
    ∃ ξ ∈ Ω,
      ∀ (K q : ℤ), 3 ≤ q →
        (q < 32 ∧ ∀ k0 : ℕ, ∃ i < 11,
            q < 8 * blindApexErr (blockA m a K) q (k0 + i) ∨
            q < 8 * blindBandErr (blockA m a K) (blockE m a K) q (k0 + i) (k0 + i) ∨
            q < 8 * blindBandErr (blockA m a K) (blockE m a K) q (k0 + i) (k0 + i + 1) ∨
            q < 8 * blindBandErr (blockA m a K) (blockE m a K) q (k0 + i) (k0 + i + 2)) ∨
        (32 ≤ q ∧ ∃ rem < a, ∀ k < m, (m - k) % (a + 1) = rem →
            q ≤ 16 * blindApexErr (blockA m a K) q k ∨
            q ≤ 8 * blindBandErr (blockA m a K) (blockE m a K) q k k ∨
            q ≤ 8 * blindBandErr (blockA m a K) (blockE m a K) q k (k + 1)) ∨
        (Kset.card ≤ 16 * (Kset.filter (fun k =>
            let κ := cancellerBelow m a k
            2 ^ (k + 2) * scaleR s0 k ≤
              2 ^ (a + 7) * classStraddleCount s0 m k κ true ξ ∧
            q ≤ 2 * ((2 * blockA m a K k +
              2 * (pathSumFwd (blockA m a K) (blockE m a K) κ -
                pathSumBack (blockA m a K) κ)) % q))).card) := by
  intro Ω Kset
  obtain ⟨ξ, hξ, hstr⟩ := exists_oddShift_coarse_straddle ha hms hcoarse_m true
  refine ⟨ξ, hξ, ?_⟩
  intro K q hq3
  by_cases hq32 : q < 32
  · left
    refine ⟨hq32, fun k0 => ?_⟩
    by_contra hall
    push Not at hall
    have hlog_le : Nat.log 2 q.toNat ≤ 4 := by
      by_contra hgt
      push Not at hgt
      have hpow : 2 ^ 5 ≤ q.toNat :=
        le_trans (Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ Nat.log 2 q.toNat))
          (Nat.pow_log_le_self 2 (by omega))
      omega
    have hLU := theoremLU_consecutive (blockA m a K) (blockE m a K) hq3 (k0 := k0) (s := 11)
      (by omega)
      (fun i hi => (hall i hi).1)
      (fun i hi => (hall i hi).2.1)
      (fun i hi => (hall i (by omega)).2.2.1)
      (fun i hi => (hall i (by omega)).2.2.2)
    have := hLU.2.2
    omega
  · push Not at hq32
    by_cases hov : q < 4 * blockQ a (K % q) + 4
    · right; left
      exact ⟨hq32, block_overflow_band_witness m a K ha hq32 hov⟩
    · push Not at hov
      right; right
      have hsub : Kset.filter (fun k =>
          2 ^ (k + 2) * scaleR s0 k ≤
            2 ^ (a + 7) * classStraddleCount s0 m k (cancellerBelow m a k) true ξ) ⊆
        Kset.filter (fun k =>
          let κ := cancellerBelow m a k
          2 ^ (k + 2) * scaleR s0 k ≤
            2 ^ (a + 7) * classStraddleCount s0 m k κ true ξ ∧
          q ≤ 2 * ((2 * blockA m a K k +
            2 * (pathSumFwd (blockA m a K) (blockE m a K) κ -
              pathSumBack (blockA m a K) κ)) % q)) := by
        intro k hk
        rw [mem_filter] at hk ⊢
        have hk_mem := mem_Icc.mp hk.1
        have hcanc := (@cancellerBelow_props s0 m a k ha (by omega) hk_mem.1
          (by omega) (by omega)).2.2.1
        exact ⟨hk.1, hk.2,
          block_straddle_residue_ge_half_q m a a K K (by omega) ha k
            (cancellerBelow m a k) hcanc (le_refl _) hov⟩
      have hle := Finset.card_le_card hsub
      dsimp only [Kset] at hstr hle ⊢
      omega

end DirectedReciprocity
