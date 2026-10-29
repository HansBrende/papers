import DirectedReciprocity.DNPStraddle

/-!
# Super-Fibonacci Unwrapping for Level-Uniform Labels (`Theorem LU`)

On the deep-nesting walk `U(s₀, m, 1)`, any turn-supported label whose stroke increments
`c_b(l) = 1 + A_l` and `c_f(l) = 2 + A_l + E_l` depend only on the level `l` has single-head
(`F = 0`) reduced mod-`q` hop errors:

- Apex hop of level `k` (`1 ≤ d < R_k`): `blindApexErr A q k = A_k % q`;
- Valley hop of level `k` in band `b = l - k` (`k ≤ l ≤ m`, `R_{l+1} < x < R_l`):
  `blindBandErr A E q k l = (E_k - ∑_{i = k + 1}^l (A_i + E_i + 2)) % q`.

In this file we prove:

1. **Formal band formulas from `strokePhiRec` (`strokePhiRec_apex_hop`,
   `strokePhiRec_valley_band_hop`)**: Direct derivation of the single-head apex and valley-band
   formulas for level-uniform potentials from the recursive stroke evaluator of `DNPStrokes.lean`.
2. **Exact modular-to-integer band unwrapping (`unwrap_blindBand_step`)**: For `q ≥ 3`, whenever
   `8 * blindBandErr A E q k (l + 1) ≤ q`, `8 * blindApexErr A q (l + 1) ≤ q`, and
   `8 * blindBandErr A E q (l + 1) (l + 1) ≤ q`, the modular identity between consecutive bands
   has zero wrap mod `q`:
   `blindBandErr A E q k l - blindBandErr A E q k (l + 1) =
     blindApexErr A q (l + 1) + blindBandErr A E q (l + 1) (l + 1) + 2`.
3. **Super-Fibonacci recurrence & logarithmic run bound (`superFib_lower_bound`,
   `theoremLU_consecutive`, `theoremLU_served_run`)**: Across any run of `s ≥ 1` consecutive levels
   `k₀, …, k₀ + s - 1` whose blind apex and band-`0, 1, 2` errors are at most `q / 8` (certified
   via Markov by `blind_error_le_div_eight` whenever each class has total error
   `≤ |class| · q / 256` and at least `|class| / 32` blind hops in each relevant band), the
   band-`0` errors satisfy `b₀(l) ≥ b₀(l + 1) + b₀(l + 2) + 4`, forcing
   `4 * ((Nat.fib s : ℤ) - 1) ≤ blindBandErr A E q k₀ k₀`,
   `32 * ((Nat.fib s : ℤ) - 1) ≤ q`, and `s ≤ 2 * Nat.log 2 q.toNat + 2`.
   In particular, no single-head cancellation mechanism with level-uniform path sums can serve more
   than `O(log q)` consecutive blind fine levels.
-/

namespace DirectedReciprocity

open Finset

/-! ### Part 1: Single-head apex and valley-band formulas from `strokePhiRec` -/

/-- Inside a level-`κ` stroke (`κ ≤ m`), the initial plain segment `[0, R_κ)` has zero recursive
turn potential. -/
theorem strokePhiRec_lt_scaleR {s0 m : ℕ} (cb cf : ℕ → ℤ) {κ o : ℕ}
    (_hκ : κ ≤ m) (ho : o < scaleR s0 κ) :
    strokePhiRec s0 m cb cf κ o = 0 := by
  unfold strokePhiRec
  cases m - κ with
  | zero => rfl
  | succ d => simp [strokePhiAux, ho]

/-- Stroke length `Π_i` decreases weakly (in fact strictly) with level `i ≤ j ≤ m ≤ s₀`. -/
theorem strokeLen_anti {s0 m i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hms : m ≤ s0) :
    strokeLen s0 m j ≤ strokeLen s0 m i := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction t with
  | zero => simp
  | succ t ih =>
    have hlt : i + t < m := by omega
    have hsp := strokeLen_succ hlt hms
    have hle := ih (by omega)
    rw [← Nat.add_assoc]
    omega

/-- Along the trailing forward-stroke chain of a level-`k` stroke (`k ≤ l ≤ m ≤ s₀`), for any
positive distance `0 < y ≤ Π_l` from the end of the stroke, `strokePhiRec` accumulates
`∑_{i = k + 1}^l cf(i)` plus the level-`l` residual `strokePhiRec ... l (Π_l - y)`. -/
theorem strokePhiRec_tail_fwd_chain {s0 m : ℕ} (cb cf : ℕ → ℤ) {k l y : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) (hms : m ≤ s0)
    (hy0 : 0 < y) (hyl : y ≤ strokeLen s0 m l) :
    strokePhiRec s0 m cb cf k (strokeLen s0 m k - y) =
      (∑ i ∈ Icc (k + 1) l, cf i) + strokePhiRec s0 m cb cf l (strokeLen s0 m l - y) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  induction d generalizing k with
  | zero =>
    simp
  | succ d ih =>
    have hk_lt : k < m := by omega
    have hsp := strokeLen_succ hk_lt hms
    have hy_le_next : y ≤ strokeLen s0 m (k + 1) :=
      le_trans hyl (strokeLen_anti (by omega : k + 1 ≤ k + (d + 1)) hlm hms)
    have hrew : strokeLen s0 m k - y =
        scaleR s0 k + strokeLen s0 m (k + 1) + (strokeLen s0 m (k + 1) - y) := by omega
    have ho_lt : strokeLen s0 m (k + 1) - y < strokeLen s0 m (k + 1) := by omega
    have hstep := strokePhiRec_fwd (s0 := s0) (m := m) cb cf
      (κ := k + 1) (o := strokeLen s0 m (k + 1) - y) (by omega) (by omega) ho_lt
    simp only [Nat.add_sub_cancel] at hstep
    rw [hrew, hstep, show k + (d + 1) = (k + 1) + d by omega,
      ih (k := k + 1) (by omega) (by omega) (by rwa [show k + 1 + d = k + (d + 1) by omega])]
    have hset : Icc (k + 1) (k + 1 + d) = insert (k + 1) (Icc (k + 1 + 1) (k + 1 + d)) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    rw [hset, Finset.sum_insert (by rw [mem_Icc]; omega)]
    ring

/-- **Formal Single-Head Apex Formula (`Lemma band(a)` on level-uniform strokes)**:
Inside a level-`(k - 1)` stroke (`1 ≤ k ≤ m ≤ s₀`), for every half-width `1 ≤ d < R_k` around the
level-`k` apex `α = R_{k - 1}`, the single-head increment minus `1` equals `A_k`. -/
theorem strokePhiRec_apex_hop {s0 m : ℕ} (A E : ℕ → ℤ) {k d : ℕ}
    (hk1 : 1 ≤ k) (hkm : k ≤ m) (hms : m ≤ s0)
    (hd1 : 1 ≤ d) (hd2 : d < scaleR s0 k) :
    let cb := pathSumBack A
    let cf := pathSumFwd A E
    let α := scaleR s0 (k - 1)
    strokePhiRec s0 m cb cf (k - 1) (α + d) -
      strokePhiRec s0 m cb cf (k - 1) (α - d) - 1 = A k := by
  intro cb cf α
  have hr_split : scaleR s0 (k - 1) = 2 * scaleR s0 k := by
    simpa [Nat.sub_add_cancel hk1] using scaleR_succ (i := k - 1) (by omega : k - 1 < s0)
  have hd_pi : d < strokeLen s0 m k := by
    unfold strokeLen
    have : 1 ≤ m - k + 1 := by omega
    nlinarith
  have hright : strokePhiRec s0 m cb cf (k - 1) (α + d) = cb k := by
    rw [strokePhiRec_back cb cf hk1 hkm hd_pi, strokePhiRec_lt_scaleR cb cf hkm hd2, add_zero]
  have hleft_lt : α - d < scaleR s0 (k - 1) := by dsimp [α]; omega
  have hleft : strokePhiRec s0 m cb cf (k - 1) (α - d) = 0 :=
    strokePhiRec_lt_scaleR cb cf (by omega : k - 1 ≤ m) hleft_lt
  rw [hright, hleft]
  dsimp [cb, pathSumBack]
  ring

/-- **Formal Single-Head Valley Band Formula (`Lemma band(b)` on level-uniform strokes)**:
Inside a level-`(k - 1)` stroke (`1 ≤ k ≤ l ≤ m ≤ s₀`), for every `1 ≤ x < R_l` in band `l - k`
around the level-`k` valley `ν = R_{k - 1} + Π_k`, the hop `(ν - (m - l) R_l - x, ν + x)` has
single-head increment minus `1` equal to `E_k - ∑_{i = k + 1}^l (A_i + E_i + 2)`. -/
theorem strokePhiRec_valley_band_hop {s0 m : ℕ} (A E : ℕ → ℤ) {k l x : ℕ}
    (hk1 : 1 ≤ k) (hkl : k ≤ l) (hlm : l ≤ m) (hms : m ≤ s0)
    (hx1 : 1 ≤ x) (hx2 : x < scaleR s0 l) :
    let cb := pathSumBack A
    let cf := pathSumFwd A E
    let ν := scaleR s0 (k - 1) + strokeLen s0 m k
    let y := (m - l) * scaleR s0 l + x
    strokePhiRec s0 m cb cf (k - 1) (ν + x) -
      strokePhiRec s0 m cb cf (k - 1) (ν - y) - 1 =
      E k - ∑ i ∈ Icc (k + 1) l, (A i + E i + 2) := by
  intro cb cf ν y
  have hrl_le_rk : scaleR s0 l ≤ scaleR s0 k := by
    unfold scaleR
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hx_lt_rk : x < scaleR s0 k := lt_of_lt_of_le hx2 hrl_le_rk
  have hx_lt_pik : x < strokeLen s0 m k := by
    unfold strokeLen
    have : 1 ≤ m - k + 1 := by omega
    nlinarith
  have hu : strokePhiRec s0 m cb cf (k - 1) (ν + x) = cf k := by
    dsimp [ν]
    rw [strokePhiRec_fwd cb cf hk1 (by omega) hx_lt_pik,
      strokePhiRec_lt_scaleR cb cf (by omega) hx_lt_rk, add_zero]
  have hy_pos : 0 < y := by dsimp [y]; omega
  have hy_lt_pil : y < strokeLen s0 m l := by
    dsimp [y]
    unfold strokeLen
    nlinarith
  have hy_le_pik : y ≤ strokeLen s0 m k :=
    le_trans (Nat.le_of_lt hy_lt_pil) (strokeLen_anti hkl hlm hms)
  have hp_rew : ν - y = scaleR s0 (k - 1) + (strokeLen s0 m k - y) := by
    dsimp [ν]; omega
  have hp_lt : strokeLen s0 m k - y < strokeLen s0 m k := by
    have := strokeLen_pos s0 m k; omega
  have hres_lt : strokeLen s0 m l - y < scaleR s0 l := by
    dsimp [y]; unfold strokeLen
    have : (m - l + 1) * scaleR s0 l = (m - l) * scaleR s0 l + scaleR s0 l := by ring
    omega
  have hp : strokePhiRec s0 m cb cf (k - 1) (ν - y) =
      cb k + ∑ i ∈ Icc (k + 1) l, cf i := by
    rw [hp_rew, strokePhiRec_back cb cf hk1 (by omega) hp_lt,
      strokePhiRec_tail_fwd_chain cb cf hkl hlm hms hy_pos (Nat.le_of_lt hy_lt_pil),
      strokePhiRec_lt_scaleR cb cf hlm hres_lt, add_zero]
  rw [hu, hp]
  have hcf_eq : ∑ i ∈ Icc (k + 1) l, cf i = ∑ i ∈ Icc (k + 1) l, (A i + E i + 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [cf, pathSumFwd]; ring
  rw [hcf_eq]
  dsimp [cb, cf, pathSumBack, pathSumFwd]
  ring

/-! ### Part 2: Reduced mod-`q` band errors and exact integer unwrapping -/

/-- Single-head (`F = 0`) reduced mod-`q` apex error at level `k`. -/
def blindApexErr (A : ℕ → ℤ) (q : ℤ) (k : ℕ) : ℤ :=
  (A k) % q

/-- Single-head (`F = 0`) reduced mod-`q` valley error at level `k` in band `l - k` (`k ≤ l`). -/
def blindBandErr (A E : ℕ → ℤ) (q : ℤ) (k l : ℕ) : ℤ :=
  (E k - ∑ i ∈ Icc (k + 1) l, (A i + E i + 2)) % q

theorem blindBandErr_self (A E : ℕ → ℤ) (q : ℤ) (k : ℕ) :
    blindBandErr A E q k k = (E k) % q := by
  unfold blindBandErr
  simp

theorem blindApexErr_nonneg (A : ℕ → ℤ) {q : ℤ} (hq : 0 < q) (k : ℕ) :
    0 ≤ blindApexErr A q k :=
  Int.emod_nonneg _ (by omega)

theorem blindBandErr_nonneg (A E : ℕ → ℤ) {q : ℤ} (hq : 0 < q) (k l : ℕ) :
    0 ≤ blindBandErr A E q k l :=
  Int.emod_nonneg _ (by omega)

theorem blindBandErr_lt (A E : ℕ → ℤ) {q : ℤ} (hq : 0 < q) (k l : ℕ) :
    blindBandErr A E q k l < q :=
  Int.emod_lt_of_pos _ hq

/-- **Exact Modular-to-Integer Band Unwrapping (`Theorem LU(a)`)**:
For `q ≥ 3` and `k ≤ l`, if the reduced mod-`q` errors `blindBandErr A E q k (l + 1)`,
`blindApexErr A q (l + 1)`, and `blindBandErr A E q (l + 1) (l + 1)` are each at most `q / 8`
(`8 * e ≤ q`), then the modular relation between bands `l - k` and `l + 1 - k` unwraps with
**zero** wrap-around in `ℤ`:
`blindBandErr A E q k l - blindBandErr A E q k (l + 1) =
  blindApexErr A q (l + 1) + blindBandErr A E q (l + 1) (l + 1) + 2`. -/
theorem unwrap_blindBand_step (A E : ℕ → ℤ) {q : ℤ} (hq : 3 ≤ q) {k l : ℕ} (hkl : k ≤ l)
    (hbNext : 8 * blindBandErr A E q k (l + 1) ≤ q)
    (hap : 8 * blindApexErr A q (l + 1) ≤ q)
    (hb0 : 8 * blindBandErr A E q (l + 1) (l + 1) ≤ q) :
    blindBandErr A E q k l - blindBandErr A E q k (l + 1) =
      blindApexErr A q (l + 1) + blindBandErr A E q (l + 1) (l + 1) + 2 := by
  have hq_pos : 0 < q := by omega
  set X : ℤ := E k - ∑ i ∈ Icc (k + 1) l, (A i + E i + 2)
  set Y : ℤ := E k - ∑ i ∈ Icc (k + 1) (l + 1), (A i + E i + 2)
  have hsum_split : ∑ i ∈ Icc (k + 1) (l + 1), (A i + E i + 2) =
      (∑ i ∈ Icc (k + 1) l, (A i + E i + 2)) + (A (l + 1) + E (l + 1) + 2) := by
    have hset : Icc (k + 1) (l + 1) = insert (l + 1) (Icc (k + 1) l) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    rw [hset, Finset.sum_insert (by rw [mem_Icc]; omega)]
    ring
  have hXY : X - Y = A (l + 1) + E (l + 1) + 2 := by
    dsimp [X, Y]; rw [hsum_split]; ring
  set ex := blindBandErr A E q k l
  set ey := blindBandErr A E q k (l + 1)
  set ea := blindApexErr A q (l + 1)
  set ee := blindBandErr A E q (l + 1) (l + 1)
  have hex_def : ex = X % q := rfl
  have hey_def : ey = Y % q := rfl
  have hea_def : ea = (A (l + 1)) % q := rfl
  have hee_def : ee = (E (l + 1)) % q := blindBandErr_self A E q (l + 1)
  set D : ℤ := (ex - ey) - (ea + ee + 2)
  have hdvd : q ∣ D := by
    have hD_eq : D = (X % q - X) - (Y % q - Y) - ((A (l + 1)) % q - A (l + 1)) -
        ((E (l + 1)) % q - E (l + 1)) := by
      dsimp [D]
      rw [hex_def, hey_def, hea_def, hee_def]
      linarith [hXY]
    rw [hD_eq]
    have hd1 : q ∣ X % q - X :=
      ⟨-(X / q), by have h := Int.emod_add_mul_ediv X q; linear_combination h⟩
    have hd2 : q ∣ Y % q - Y :=
      ⟨-(Y / q), by have h := Int.emod_add_mul_ediv Y q; linear_combination h⟩
    have hd3 : q ∣ (A (l + 1)) % q - A (l + 1) :=
      ⟨-(A (l + 1) / q), by have h := Int.emod_add_mul_ediv (A (l + 1)) q; linear_combination h⟩
    have hd4 : q ∣ (E (l + 1)) % q - E (l + 1) :=
      ⟨-(E (l + 1) / q), by have h := Int.emod_add_mul_ediv (E (l + 1)) q; linear_combination h⟩
    exact dvd_sub (dvd_sub (dvd_sub hd1 hd2) hd3) hd4
  have hex0 : 0 ≤ ex := blindBandErr_nonneg A E hq_pos k l
  have hex_lt : ex < q := blindBandErr_lt A E hq_pos k l
  have hey0 : 0 ≤ ey := blindBandErr_nonneg A E hq_pos k (l + 1)
  have hea0 : 0 ≤ ea := blindApexErr_nonneg A hq_pos (l + 1)
  have hee0 : 0 ≤ ee := blindBandErr_nonneg A E hq_pos (l + 1) (l + 1)
  have hD_lt : D < q := by dsimp [D]; linarith
  have hD_gt : -q < D := by
    rcases (show q < 8 ∨ 8 ≤ q by omega) with hq8 | hq8
    · have hey_z : ey = 0 := by omega
      have hea_z : ea = 0 := by omega
      have hee_z : ee = 0 := by omega
      dsimp [D]; omega
    · dsimp [D]; linarith
  obtain ⟨m_div, hm_div⟩ := hdvd
  have hm0 : m_div = 0 := by nlinarith
  have hD0 : D = 0 := by rw [hm_div, hm0, mul_zero]
  dsimp [D] at hD0
  linarith

/-- **Super-Fibonacci Two-Step Inequality (`Theorem LU(b)`)**:
When `q ≥ 3` and bands `1` and `2` of level `k` together with the apex and band-`0` errors of
levels `k + 1` and `k + 2` are each at most `q / 8`, the band-`0` errors satisfy
`b₀(k + 1) + b₀(k + 2) + 4 ≤ b₀(k)`. -/
theorem superFib_step (A E : ℕ → ℤ) {q : ℤ} (hq : 3 ≤ q) (k : ℕ)
    (hb1 : 8 * blindBandErr A E q k (k + 1) ≤ q)
    (hb2 : 8 * blindBandErr A E q k (k + 2) ≤ q)
    (hap1 : 8 * blindApexErr A q (k + 1) ≤ q)
    (hb0_1 : 8 * blindBandErr A E q (k + 1) (k + 1) ≤ q)
    (hap2 : 8 * blindApexErr A q (k + 2) ≤ q)
    (hb0_2 : 8 * blindBandErr A E q (k + 2) (k + 2) ≤ q) :
    blindBandErr A E q (k + 1) (k + 1) + blindBandErr A E q (k + 2) (k + 2) + 4 ≤
      blindBandErr A E q k k := by
  have hstep1 := unwrap_blindBand_step A E hq (le_refl k) hb1 hap1 hb0_1
  have hstep2 := unwrap_blindBand_step A E hq (Nat.le_succ k) hb2 hap2 hb0_2
  have hb2_0 : 0 ≤ blindBandErr A E q k (k + 2) := blindBandErr_nonneg A E (by omega) k (k + 2)
  have hap1_0 : 0 ≤ blindApexErr A q (k + 1) := blindApexErr_nonneg A (by omega) (k + 1)
  have hap2_0 : 0 ≤ blindApexErr A q (k + 2) := blindApexErr_nonneg A (by omega) (k + 2)
  linarith

/-! ### Part 3: Super-Fibonacci growth, Markov bridge, and `O(log q)` run bound -/

/-- Exact super-Fibonacci lower bound: any sequence `b : ℕ → ℤ` of non-negative integers on
`[k₀, k₀ + s)` (`s ≥ 1`) satisfying `b(l + 1) + b(l + 2) + 4 ≤ b(l)` whenever `l + 2 < k₀ + s`
obeys `4 * ((Nat.fib s : ℤ) - 1) ≤ b k₀`. -/
theorem superFib_lower_bound (b : ℕ → ℤ) :
    ∀ {s : ℕ} (_hs : 1 ≤ s) (k0 : ℕ),
      (∀ i < s, 0 ≤ b (k0 + i)) →
      (∀ i, i + 2 < s → b (k0 + i + 1) + b (k0 + i + 2) + 4 ≤ b (k0 + i)) →
      4 * ((Nat.fib s : ℤ) - 1) ≤ b k0 := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro hs k0 hnonneg hrec
    rcases s with _ | _ | _ | s'
    · omega
    · simpa using hnonneg 0 (by omega)
    · have hf2 : Nat.fib 2 = 1 := rfl
      rw [hf2]
      simpa using hnonneg 0 (by omega)
    · have h1 := ih (s' + 2) (by omega) (by omega) (k0 + 1)
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hnonneg (i + 1) (by omega))
        (fun i hi => by
          have hr := hrec (i + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1] using hr)
      have h2 := ih (s' + 1) (by omega) (by omega) (k0 + 2)
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 2 i] using hnonneg (i + 2) (by omega))
        (fun i hi => by
          have hr := hrec (i + 2) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 2] using hr)
      have h0 := hrec 0 (by omega)
      simp only [Nat.add_zero] at h0
      have hfib : (Nat.fib (s' + 3) : ℤ) = (Nat.fib (s' + 1) : ℤ) + (Nat.fib (s' + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := s' + 1)
      linarith

/-- Exponential lower bound on odd-indexed Fibonacci numbers: `2^k + 1 ≤ F_{2k+3}` for all `k`. -/
theorem two_pow_add_one_le_fib (k : ℕ) : 2 ^ k + 1 ≤ Nat.fib (2 * k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hidx : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by omega
    rw [hidx, Nat.fib_add_two]
    have hmono : Nat.fib (2 * k + 3) ≤ Nat.fib (2 * k + 3 + 1) :=
      Nat.fib_mono (by omega)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- Explicit `O(log q)` run bound deduced from `32 * ((Nat.fib s : ℤ) - 1) ≤ q` (`q ≥ 3`):
`s ≤ 2 * Nat.log 2 q.toNat + 2` (and in fact `s ≤ 2 * Nat.log 2 q.toNat` whenever `s ≥ 3`). -/
theorem log_bound_of_fib_le {s : ℕ} {q : ℤ} (hq : 3 ≤ q)
    (hfib : 32 * ((Nat.fib s : ℤ) - 1) ≤ q) :
    s ≤ 2 * Nat.log 2 q.toNat + 2 := by
  by_cases hs : s ≤ 2
  · omega
  · push Not at hs
    set k := (s - 3) / 2
    have hk_le : 2 * k + 3 ≤ s := by omega
    have hs_le : s ≤ 2 * k + 4 := by omega
    have hfib_mono : Nat.fib (2 * k + 3) ≤ Nat.fib s := Nat.fib_mono hk_le
    have hpow_fib : 2 ^ k + 1 ≤ Nat.fib s := le_trans (two_pow_add_one_le_fib k) hfib_mono
    have hpow_int : (2 ^ (k + 5) : ℤ) ≤ q := by
      have h1 : (2 ^ k : ℤ) + 1 ≤ (Nat.fib s : ℤ) := by exact_mod_cast hpow_fib
      have h32 : (2 ^ (k + 5) : ℤ) = 32 * (2 ^ k : ℤ) := by ring
      linarith
    have hpow_nat : 2 ^ (k + 5) ≤ q.toNat := by
      have hq_eq : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      exact_mod_cast (by rwa [hq_eq] : (2 ^ (k + 5) : ℤ) ≤ (q.toNat : ℤ))
    have hlog : k + 5 ≤ Nat.log 2 q.toNat :=
      Nat.le_log_of_pow_le (by decide : 1 < 2) hpow_nat
    omega

/-- Markov bridge from class total error and blind-band count to `8 * e ≤ q`:
if a class of positive size `classSize` has total non-negative hop error `errSum` satisfying
`256 * errSum ≤ classSize * q` (i.e. `θ`-served with `θ ≤ 1 / 256`), and a band contains `B`
blind hops (`32 * B ≥ classSize`, holding whenever at least half of apex or band `0, 1, 2` is blind
with `R_{l+2} ≥ 2`) each carrying reduced error `e ≥ 0` (`B * e ≤ errSum`), then `8 * e ≤ q`. -/
theorem blind_error_le_div_eight {classSize B : ℕ} {errSum e q : ℤ}
    (hc : 0 < classSize) (he0 : 0 ≤ e)
    (hband : classSize ≤ 32 * B)
    (hsub : (B : ℤ) * e ≤ errSum)
    (hserv : 256 * errSum ≤ (classSize : ℤ) * q) :
    8 * e ≤ q := by
  have hc_int : (0 : ℤ) < (classSize : ℤ) := by exact_mod_cast hc
  have hband_int : (classSize : ℤ) ≤ 32 * (B : ℤ) := by exact_mod_cast hband
  nlinarith

/-- **Theorem LU (`Super-Fibonacci Unwrapping for Level-Uniform Labels`)**:
Let `A, E : ℕ → ℤ` be the level parameters of any level-uniform turn-supported label modulo
`q ≥ 3`. Suppose `s ≥ 1` consecutive levels `k₀, …, k₀ + s - 1` have single-head reduced apex and
band-`0, 1, 2` errors bounded by `q / 8` across the run (`8 * e ≤ q`, certified via
`blind_error_le_div_eight` whenever those levels are `1/256`-served and at least half-blind in
their apex and first three valley bands). Then:
1. `4 * ((Nat.fib s : ℤ) - 1) ≤ blindBandErr A E q k₀ k₀`;
2. `32 * ((Nat.fib s : ℤ) - 1) ≤ q`;
3. `s ≤ 2 * Nat.log 2 q.toNat + 2`. -/
theorem theoremLU_consecutive (A E : ℕ → ℤ) {q : ℤ} (hq : 3 ≤ q) {k0 s : ℕ} (hs : 1 ≤ s)
    (hap : ∀ i < s, 8 * blindApexErr A q (k0 + i) ≤ q)
    (hb0 : ∀ i < s, 8 * blindBandErr A E q (k0 + i) (k0 + i) ≤ q)
    (hb1 : ∀ i, i + 1 < s → 8 * blindBandErr A E q (k0 + i) (k0 + i + 1) ≤ q)
    (hb2 : ∀ i, i + 2 < s → 8 * blindBandErr A E q (k0 + i) (k0 + i + 2) ≤ q) :
    4 * ((Nat.fib s : ℤ) - 1) ≤ blindBandErr A E q k0 k0 ∧
    32 * ((Nat.fib s : ℤ) - 1) ≤ q ∧
    s ≤ 2 * Nat.log 2 q.toNat + 2 := by
  have hq_pos : 0 < q := by omega
  let b : ℕ → ℤ := fun l => blindBandErr A E q l l
  have hnonneg : ∀ i < s, 0 ≤ b (k0 + i) :=
    fun i _ => blindBandErr_nonneg A E hq_pos (k0 + i) (k0 + i)
  have hrec : ∀ i, i + 2 < s → b (k0 + i + 1) + b (k0 + i + 2) + 4 ≤ b (k0 + i) := by
    intro i hi
    exact superFib_step A E hq (k0 + i)
      (hb1 i (by omega))
      (hb2 i hi)
      (hap (i + 1) (by omega))
      (hb0 (i + 1) (by omega))
      (hap (i + 2) (by omega))
      (hb0 (i + 2) (by omega))
  have hlow : 4 * ((Nat.fib s : ℤ) - 1) ≤ blindBandErr A E q k0 k0 :=
    superFib_lower_bound b hs k0 hnonneg hrec
  have hb0_top : 8 * blindBandErr A E q k0 k0 ≤ q := by
    simpa using hb0 0 (by omega)
  have h32 : 32 * ((Nat.fib s : ℤ) - 1) ≤ q := by linarith
  exact ⟨hlow, h32, log_bound_of_fib_le hq h32⟩

end DirectedReciprocity
