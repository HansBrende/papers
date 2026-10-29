import DirectedReciprocity.DNPStrokes

/-!
# Generalized Mod-`q` Straddle Involution and Odd-Shift Visibility (`Theorem V*`)

For any level-uniform turn-supported label on the deep-nesting walk `U(s₀, m, 1)` with back-stroke
and forward-stroke path-sum increments `cb κ = 1 + A κ` and `cf κ = 2 + A κ + E κ`
(`Δ κ := cf κ - cb κ = 1 + E κ`), we prove:

1. **Straddle involution (`mem_straddleSet_sub_iff`, `straddle_involution`)**:
   Whenever `Π_κ ≤ R_k`, `d ↦ Π_κ - d` is a fixed-point-free-or-midpoint involution on
   `straddleSet c0 α_V Π_κ R_k` swapping the back-stroke offset `o_p = c₀ - d - α_V` and the
   forward-stroke offset `o_u = c₀ + d - (α_V + Π_κ)`.
2. **Exact cancellation of nested stroke potentials (`straddle_otherHeadInc_sum`)**:
   Along any potential `Φ : ℤ → ℤ` satisfying the level-uniform V decomposition on
   `[α_V, α_V + 2 Π_κ)` (instantiated directly by `strokePhiRec_back` and `strokePhiRec_fwd` of
   `DNPStrokes.lean`), every `d ∈ straddleSet c0 α_V Π_κ R_k` satisfies
   `F(d) + F(Π_κ - d) = 2 (cf - cb)` in `ℤ`, cancelling `Y(o_u) - Y(o_p)` identically.
3. **Unconditional mod-`q` straddle pair & set bounds (`theoremVStar_pair`, `theoremVStar_sum`)**:
   For every modulus `q > 0` and apex parameter `A' : ℤ`, the reduced mod-`q` apex hop errors
   `e(d) = (A' + F(d)) % q ∈ [0, q)` satisfy
   `(2 A' + 2 (cf - cb)) % q ≤ e(d) + e(Π_κ - d)`,
   and summing over `d ∈ straddleSet c0 α_V Π_κ R_k` (`Π_κ ≤ R_k`) yields
   `|straddleSet| · ((2 A' + 2 (cf - cb)) % q) ≤ 2 ∑_{d ∈ straddleSet} e(d)`,
   with **zero dependence on `m` or on the integer magnitude of `F(d)`**.
4. **Exact odd-centre & even-centre straddle counts (`sum_straddleSet_card_parity`)**:
   When `Π_κ = 2 L` is even (`m < s₀`) and `Π_κ ≤ R_k`, summing `|straddleSet c0 α_V Π_κ R_k|`
   over centers `c0 ∈ [α_V, α_V + 2 Π_κ)` of **either** fixed parity (`c0 % 2 = 0` or `c0 % 2 = 1`)
   gives **exact** count `L ^ 2 = Π_κ ^ 2 / 4`, lifting visibility on average over shifts directly
   to **odd** shifts `ξ`.
-/

namespace DirectedReciprocity

open Finset

/-- Level-uniform back-stroke path-sum increment `c_b(κ) = 1 + A_κ`. -/
def pathSumBack (A : ℕ → ℤ) (κ : ℕ) : ℤ := 1 + A κ

/-- Level-uniform forward-stroke path-sum increment `c_f(κ) = 2 + A_κ + E_κ`. -/
def pathSumFwd (A E : ℕ → ℤ) (κ : ℕ) : ℤ := 2 + A κ + E κ

/-- Stroke-difference parameter `Δ(κ) = c_f(κ) - c_b(κ) = 1 + E_κ`. -/
def deltaLevel (A E : ℕ → ℤ) (κ : ℕ) : ℤ := pathSumFwd A E κ - pathSumBack A κ

theorem deltaLevel_eq (A E : ℕ → ℤ) (κ : ℕ) :
    deltaLevel A E κ = 1 + E κ := by
  unfold deltaLevel pathSumFwd pathSumBack; ring

/-- The set `𝒟(c₀, V)` of half-widths `d ∈ [1, R_k - 1]` for which `(c₀ - d, c₀ + d]` straddles
a V with apex `α_V` and stroke length `Π_κ` (`ν_V = α_V + Π_κ`). -/
def straddleSet (c0 α_V : ℤ) (pi_κ R_k : ℕ) : Finset ℕ :=
  (Icc 1 (R_k - 1)).filter fun d =>
    α_V ≤ c0 - (d : ℤ) ∧ c0 - (d : ℤ) < α_V + (pi_κ : ℤ) ∧
    α_V + (pi_κ : ℤ) ≤ c0 + (d : ℤ) ∧ c0 + (d : ℤ) < α_V + 2 * (pi_κ : ℤ)

theorem lt_pi_of_mem_straddleSet {c0 α_V : ℤ} {pi_κ R_k d : ℕ}
    (hd : d ∈ straddleSet c0 α_V pi_κ R_k) :
    1 ≤ d ∧ d < pi_κ := by
  rw [straddleSet, mem_filter, mem_Icc] at hd
  omega

theorem center_mem_span_of_straddleSet_nonempty {c0 α_V : ℤ} {pi_κ R_k : ℕ}
    (hne : (straddleSet c0 α_V pi_κ R_k).Nonempty) :
    α_V < c0 ∧ c0 < α_V + 2 * (pi_κ : ℤ) := by
  obtain ⟨d, hd⟩ := hne
  rw [straddleSet, mem_filter, mem_Icc] at hd
  omega

/-- When `Π_κ ≤ R_k`, `d ↦ Π_κ - d` maps `straddleSet c0 α_V Π_κ R_k` to itself. -/
theorem mem_straddleSet_sub {c0 α_V : ℤ} {pi_κ R_k d : ℕ}
    (hpi : pi_κ ≤ R_k) (hd : d ∈ straddleSet c0 α_V pi_κ R_k) :
    pi_κ - d ∈ straddleSet c0 α_V pi_κ R_k := by
  rw [straddleSet, mem_filter, mem_Icc] at hd ⊢
  have hd_lt : d < pi_κ := by omega
  have hcast : ((pi_κ - d : ℕ) : ℤ) = (pi_κ : ℤ) - (d : ℤ) := Int.ofNat_sub (Nat.le_of_lt hd_lt)
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [hcast]
  omega

/-- Involution equivalence `d ∈ straddleSet ↔ Π_κ - d ∈ straddleSet` when `Π_κ ≤ R_k` and
`1 ≤ d < Π_κ`. -/
theorem mem_straddleSet_sub_iff {c0 α_V : ℤ} {pi_κ R_k d : ℕ}
    (hpi : pi_κ ≤ R_k) (hd1 : 1 ≤ d) (hd2 : d < pi_κ) :
    pi_κ - d ∈ straddleSet c0 α_V pi_κ R_k ↔ d ∈ straddleSet c0 α_V pi_κ R_k := by
  constructor
  · intro h
    have h' := mem_straddleSet_sub hpi h
    rwa [show pi_κ - (pi_κ - d) = d by omega] at h'
  · exact mem_straddleSet_sub hpi

/-- Predicate that a potential `Φ : ℤ → ℤ` decomposes on the back and forward strokes of a V
starting at `α_V` with stroke length `pi_κ` into `C_V + cb + Y(o)` and `C_V + cf + Y(o)`. -/
def HasLevelUniformVDecomp (Φ : ℤ → ℤ) (α_V : ℤ) (pi_κ : ℕ) (C_V cb cf : ℤ)
    (Y : ℕ → ℤ) : Prop :=
  ∀ o : ℕ, o < pi_κ →
    Φ (α_V + (o : ℤ)) = C_V + cb + Y o ∧
    Φ (α_V + (pi_κ : ℤ) + (o : ℤ)) = C_V + cf + Y o

/-- Direct instantiation of `HasLevelUniformVDecomp` from `strokePhiRec_back` and
`strokePhiRec_fwd` inside a level-`(κ - 1)` stroke (`1 ≤ κ ≤ m`). -/
theorem strokePhiRec_hasLevelUniformVDecomp {s0 m : ℕ} (cb cf : ℕ → ℤ) (base_t : ℤ) (C₀ : ℤ)
    {κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) :
    HasLevelUniformVDecomp
      (fun t => C₀ + strokePhiRec s0 m cb cf (κ - 1) (t - base_t).toNat)
      (base_t + (scaleR s0 (κ - 1) : ℤ))
      (strokeLen s0 m κ)
      C₀ (cb κ) (cf κ)
      (strokePhiRec s0 m cb cf κ) := by
  intro o ho
  have hb : (base_t + (scaleR s0 (κ - 1) : ℤ) + (o : ℤ) - base_t).toNat =
      scaleR s0 (κ - 1) + o := by omega
  have hf : (base_t + (scaleR s0 (κ - 1) : ℤ) + (strokeLen s0 m κ : ℤ) + (o : ℤ) - base_t).toNat =
      scaleR s0 (κ - 1) + strokeLen s0 m κ + o := by omega
  constructor
  · dsimp only; rw [hb, strokePhiRec_back cb cf hκ1 hκm ho]; ring
  · dsimp only; rw [hf, strokePhiRec_fwd cb cf hκ1 hκm ho]; ring

/-- Other-head potential increment `F(d) = Φ(c₀ + d) - Φ(c₀ - d)` across `(c₀ - d, c₀ + d]`. -/
def otherHeadInc (Φ : ℤ → ℤ) (c0 : ℤ) (d : ℕ) : ℤ :=
  Φ (c0 + (d : ℤ)) - Φ (c0 - (d : ℤ))

/-- **Exact Integer Involution Sum (`Theorem V*(a)`)**:
On any straddling half-width `d ∈ straddleSet c0 α_V pi_κ R_k`, the nested stroke potentials `Y(o_u)`
and `Y(o_p)` cancel identically across `(d, pi_κ - d)`, leaving
`F(d) + F(pi_κ - d) = 2 * (cf - cb)`. -/
theorem straddle_otherHeadInc_sum {Φ : ℤ → ℤ} {c0 α_V C_V cb cf : ℤ} {pi_κ R_k d : ℕ}
    {Y : ℕ → ℤ} (hΦ : HasLevelUniformVDecomp Φ α_V pi_κ C_V cb cf Y)
    (hd : d ∈ straddleSet c0 α_V pi_κ R_k) :
    otherHeadInc Φ c0 d + otherHeadInc Φ c0 (pi_κ - d) = 2 * (cf - cb) := by
  rw [straddleSet, mem_filter, mem_Icc] at hd
  obtain ⟨-, h1, h2, h3, h4⟩ := hd
  have hd_lt : d < pi_κ := by omega
  let o_p : ℕ := (c0 - (d : ℤ) - α_V).toNat
  let o_u : ℕ := (c0 + (d : ℤ) - (α_V + (pi_κ : ℤ))).toNat
  have hop_lt : o_p < pi_κ := by omega
  have hou_lt : o_u < pi_κ := by omega
  have hc_sub_d : c0 - (d : ℤ) = α_V + (o_p : ℤ) := by omega
  have hc_add_d : c0 + (d : ℤ) = α_V + (pi_κ : ℤ) + (o_u : ℤ) := by omega
  have hcast : ((pi_κ - d : ℕ) : ℤ) = (pi_κ : ℤ) - (d : ℤ) := Int.ofNat_sub (Nat.le_of_lt hd_lt)
  have hc_sub_d' : c0 - ((pi_κ - d : ℕ) : ℤ) = α_V + (o_u : ℤ) := by rw [hcast]; omega
  have hc_add_d' : c0 + ((pi_κ - d : ℕ) : ℤ) = α_V + (pi_κ : ℤ) + (o_p : ℤ) := by
    rw [hcast]; omega
  obtain ⟨hback_p, hfwd_p⟩ := hΦ o_p hop_lt
  obtain ⟨hback_u, hfwd_u⟩ := hΦ o_u hou_lt
  unfold otherHeadInc
  rw [hc_add_d, hc_sub_d, hc_add_d', hc_sub_d', hfwd_u, hback_p, hfwd_p, hback_u]
  ring

/-- Subadditivity of non-negative Euclidean remainders modulo `q > 0`:
for all `x, y : ℤ`, `(x + y) % q ≤ (x % q) + (y % q)`. -/
theorem emod_add_emod_ge (x y : ℤ) {q : ℤ} (hq : 0 < q) :
    (x + y) % q ≤ (x % q) + (y % q) := by
  have hx0 : 0 ≤ x % q := Int.emod_nonneg x (by omega)
  have hy0 : 0 ≤ y % q := Int.emod_nonneg y (by omega)
  set s := x % q + y % q
  have hs0 : 0 ≤ s := add_nonneg hx0 hy0
  rw [Int.add_emod]
  have hdiv := Int.emod_add_mul_ediv s q
  have hqdiv : 0 ≤ q * (s / q) := mul_nonneg (by omega) (Int.ediv_nonneg hs0 (by omega))
  linarith

/-- **Theorem V\*(b) (Unconditional Mod-`q` Straddle Pair Bound)**:
For any modulus `q > 0`, apex parameter `A' : ℤ`, and `d ∈ straddleSet c0 α_V pi_κ R_k`,
the reduced mod-`q` apex hop errors satisfy
`(2 * A' + 2 * (cf - cb)) % q ≤ ((A' + F(d)) % q) + ((A' + F(pi_κ - d)) % q)`. -/
theorem theoremVStar_pair {Φ : ℤ → ℤ} {c0 α_V C_V cb cf A' q : ℤ} {pi_κ R_k d : ℕ}
    {Y : ℕ → ℤ} (hq : 0 < q) (hΦ : HasLevelUniformVDecomp Φ α_V pi_κ C_V cb cf Y)
    (hd : d ∈ straddleSet c0 α_V pi_κ R_k) :
    (2 * A' + 2 * (cf - cb)) % q ≤
      (A' + otherHeadInc Φ c0 d) % q + (A' + otherHeadInc Φ c0 (pi_κ - d)) % q := by
  have hsum : (A' + otherHeadInc Φ c0 d) + (A' + otherHeadInc Φ c0 (pi_κ - d)) =
      2 * A' + 2 * (cf - cb) := by
    have h := straddle_otherHeadInc_sum hΦ hd
    linarith
  rw [← hsum]
  exact emod_add_emod_ge _ _ hq

/-- **Theorem V\*(c) (Unconditional Mod-`q` Straddle Set Sum Bound)**:
When `pi_κ ≤ R_k` and `q > 0`, summing the mod-`q` apex hop error `(A' + F(d)) % q` over all
`d ∈ straddleSet c0 α_V pi_κ R_k` satisfies
`|straddleSet| · ((2 * A' + 2 * (cf - cb)) % q) ≤ 2 · ∑_{d ∈ straddleSet} ((A' + F(d)) % q)`. -/
theorem theoremVStar_sum {Φ : ℤ → ℤ} {c0 α_V C_V cb cf A' q : ℤ} {pi_κ R_k : ℕ}
    {Y : ℕ → ℤ} (hq : 0 < q) (hpi : pi_κ ≤ R_k)
    (hΦ : HasLevelUniformVDecomp Φ α_V pi_κ C_V cb cf Y) :
    (straddleSet c0 α_V pi_κ R_k).card * ((2 * A' + 2 * (cf - cb)) % q) ≤
      2 * ∑ d ∈ straddleSet c0 α_V pi_κ R_k, (A' + otherHeadInc Φ c0 d) % q := by
  set S := straddleSet c0 α_V pi_κ R_k
  let e : ℕ → ℤ := fun d => (A' + otherHeadInc Φ c0 d) % q
  have hbij : ∑ d ∈ S, e d = ∑ d ∈ S, e (pi_κ - d) := by
    refine Finset.sum_bij (fun d _ => pi_κ - d) ?_ ?_ ?_ ?_
    · intro d hd; exact mem_straddleSet_sub hpi hd
    · intro d₁ hd₁ d₂ hd₂ heq
      have h1 := lt_pi_of_mem_straddleSet hd₁
      have h2 := lt_pi_of_mem_straddleSet hd₂
      omega
    · intro d hd
      have h1 := lt_pi_of_mem_straddleSet hd
      exact ⟨pi_κ - d, mem_straddleSet_sub hpi hd, by omega⟩
    · intro d hd
      have h1 := lt_pi_of_mem_straddleSet hd
      rw [show pi_κ - (pi_κ - d) = d by omega]
  have h2sum : 2 * ∑ d ∈ S, e d = ∑ d ∈ S, (e d + e (pi_κ - d)) := by
    rw [two_mul, Finset.sum_add_distrib, ← hbij]
  rw [h2sum]
  have hle : ∑ _d ∈ S, ((2 * A' + 2 * (cf - cb)) % q) ≤ ∑ d ∈ S, (e d + e (pi_κ - d)) :=
    Finset.sum_le_sum (fun d hd => theoremVStar_pair hq hΦ hd)
  simpa [Finset.sum_const, nsmul_eq_mul] using hle

/-! ### Exact Parity-Conditioned Center Counts (`Odd-Shift Visibility`) -/

/-- In any integer interval `[a, a + 2 * m)` of even length `2 * m`, the number of integers `c`
with `c % 2 = p` (`p ∈ {0, 1}`) is **exactly `m`**. -/
theorem card_Ico_even_len_mod_two (a : ℤ) (m : ℕ) {p : ℤ} (hp : p = 0 ∨ p = 1) :
    ((Ico a (a + 2 * (m : ℤ))).filter (fun c => c % 2 = p)).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Ico a (a + 2 * ((m + 1 : ℕ) : ℤ)) =
        Ico a (a + 2 * (m : ℤ)) ∪ {a + 2 * (m : ℤ), a + 2 * (m : ℤ) + 1} := by
      ext c
      simp only [mem_Ico, mem_union, mem_insert, mem_singleton]
      push_cast; omega
    have hdisj : Disjoint (Ico a (a + 2 * (m : ℤ)))
        ({a + 2 * (m : ℤ), a + 2 * (m : ℤ) + 1} : Finset ℤ) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      simp only [mem_Ico, mem_insert, mem_singleton] at hc1 hc2
      omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (Disjoint.mono_left (filter_subset _ _)
        (Disjoint.mono_right (filter_subset _ _) hdisj)),
      ih]
    have hpair : (({a + 2 * (m : ℤ), a + 2 * (m : ℤ) + 1} : Finset ℤ).filter
        (fun c => c % 2 = p)).card = 1 := by
      set x := a + 2 * (m : ℤ)
      rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with hx | hx <;>
        rcases hp with rfl | rfl
      · have hfilt : ({x, x + 1} : Finset ℤ).filter (fun c => c % 2 = 0) = {x} := by
          ext c; simp only [mem_filter, mem_insert, mem_singleton]; omega
        rw [hfilt, card_singleton]
      · have hfilt : ({x, x + 1} : Finset ℤ).filter (fun c => c % 2 = 1) = {x + 1} := by
          ext c; simp only [mem_filter, mem_insert, mem_singleton]; omega
        rw [hfilt, card_singleton]
      · have hfilt : ({x, x + 1} : Finset ℤ).filter (fun c => c % 2 = 0) = {x + 1} := by
          ext c; simp only [mem_filter, mem_insert, mem_singleton]; omega
        rw [hfilt, card_singleton]
      · have hfilt : ({x, x + 1} : Finset ℤ).filter (fun c => c % 2 = 1) = {x} := by
          ext c; simp only [mem_filter, mem_insert, mem_singleton]; omega
        rw [hfilt, card_singleton]
    rw [hpair]

/-- Exact triangular sum `∑_{d = 1}^{2 L - 1} min(d, 2 L - d) = L ^ 2`. -/
theorem sum_min_sub_two_mul (L : ℕ) :
    ∑ d ∈ Icc 1 (2 * L - 1), min d (2 * L - d) = L ^ 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    -- Split `Icc 1 (2 * L + 1)` into `{1}`, `Icc 2 (2 * L)` (shifted from `Icc 1 (2 * L - 1)` by `+ 1`),
    -- and `{2 * L + 1}` (when `L ≥ 1`; handle `L = 0` directly).
    cases L with
    | zero => decide
    | succ L' =>
      set M := L' + 1
      have hset : Icc 1 (2 * (M + 1) - 1) =
          insert 1 (insert (2 * M + 1) (Icc 2 (2 * M))) := by
        ext d; simp only [mem_Icc, mem_insert]; omega
      rw [hset, Finset.sum_insert (by rw [mem_insert, mem_Icc]; omega),
        Finset.sum_insert (by rw [mem_Icc]; omega)]
      have hshift : ∑ d ∈ Icc 2 (2 * M), min d (2 * (M + 1) - d) =
          ∑ k ∈ Icc 1 (2 * M - 1), (min k (2 * M - k) + 1) := by
        refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
        · intro d hd; rw [mem_Icc] at hd ⊢; omega
        · intro d₁ h1 d₂ h2 heq; rw [mem_Icc] at h1 h2; omega
        · intro k hk; rw [mem_Icc] at hk
          exact ⟨k + 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro d hd; rw [mem_Icc] at hd; omega
      rw [hshift, Finset.sum_add_distrib, ih, Finset.sum_const, Nat.card_Icc]
      have hmin1 : min 1 (2 * (M + 1) - 1) = 1 := by omega
      have hmin2 : min (2 * M + 1) (2 * (M + 1) - (2 * M + 1)) = 1 := by omega
      have hlen : 2 * M - 1 + 1 - 1 = 2 * M - 1 := by omega
      rw [hmin1, hmin2, hlen, smul_eq_mul, mul_one]
      have hsq : (M + 1) ^ 2 = M ^ 2 + 2 * M + 1 := by ring
      omega

/-- **Exact Parity-Conditioned Straddle Sum (`Theorem V*(d)`)**:
For any even stroke length `Π_κ = 2 * L` with `2 * L ≤ R_k` and either parity `p ∈ {0, 1}`,
summing `(straddleSet c0 α_V (2 * L) R_k).card` over all centers `c0 ∈ [α_V, α_V + 4 * L)` with
`c0 % 2 = p` yields **exact** count `L ^ 2` (`= Π_κ ^ 2 / 4`). -/
theorem sum_straddleSet_card_parity (α_V : ℤ) (L R_k : ℕ) (hpi : 2 * L ≤ R_k)
    {p : ℤ} (hp : p = 0 ∨ p = 1) :
    ∑ c0 ∈ (Ico α_V (α_V + 2 * ((2 * L : ℕ) : ℤ))).filter (fun c => c % 2 = p),
      (straddleSet c0 α_V (2 * L) R_k).card = L ^ 2 := by
  classical
  cases L with
  | zero => simp [straddleSet]
  | succ L' =>
    set L := L' + 1
    set Cset := (Ico α_V (α_V + 2 * ((2 * L : ℕ) : ℤ))).filter (fun c => c % 2 = p)
    set Dset := Icc 1 (2 * L - 1)
    -- Every `d ∈ straddleSet c0 α_V (2 * L) R_k` lies in `Dset = Icc 1 (2 * L - 1)`
    have hcard_eq : ∀ c0 ∈ Cset,
        (straddleSet c0 α_V (2 * L) R_k).card =
          (Dset.filter (fun d => d ∈ straddleSet c0 α_V (2 * L) R_k)).card := by
      intro c0 _
      congr 1
      ext d
      simp only [mem_filter, Dset, mem_Icc]
      refine ⟨fun hd => ⟨?_, hd⟩, fun h => h.2⟩
      have hlt := lt_pi_of_mem_straddleSet hd
      rw [straddleSet, mem_filter, mem_Icc] at hd
      omega
    rw [Finset.sum_congr rfl hcard_eq]
    -- Swap summation order between `c0 ∈ Cset` and `d ∈ Dset`
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    -- For each `d ∈ Dset`, `{c0 ∈ Cset | d ∈ straddleSet}` is `Ico a (a + 2 * m)` filtered by `c % 2 = p`
    -- where `m = min d (2 * L - d)`!
    have hfiber : ∀ d ∈ Dset,
        (∑ x ∈ Cset, if d ∈ straddleSet x α_V (2 * L) R_k then 1 else 0) =
          min d (2 * L - d) := by
      intro d hd
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      rw [mem_Icc] at hd
      set m := min d (2 * L - d)
      set a := α_V + (max d (2 * L - d) : ℕ)
      have hset_eq : Cset.filter (fun x => d ∈ straddleSet x α_V (2 * L) R_k) =
          (Ico a (a + 2 * (m : ℤ))).filter (fun c => c % 2 = p) := by
        ext c
        simp only [Cset, mem_filter, mem_Ico, straddleSet, mem_Icc, a, m]
        have hd_rk : d ≤ R_k - 1 := by omega
        have hmax_min : max d (2 * L - d) + 2 * min d (2 * L - d) = 2 * L + min d (2 * L - d) := by
          omega
        push_cast at *
        constructor
        · rintro ⟨⟨_, hcpar⟩, ⟨_, h1, h2, h3, h4⟩⟩
          refine ⟨⟨?_, ?_⟩, hcpar⟩ <;> omega
        · rintro ⟨⟨hlo, hhi⟩, hcpar⟩
          refine ⟨⟨⟨by omega, by omega⟩, hcpar⟩, ⟨⟨hd.1, hd_rk⟩, ?_, ?_, ?_, ?_⟩⟩ <;> omega
      rw [hset_eq]
      exact card_Ico_even_len_mod_two a m hp
    rw [Finset.sum_congr rfl hfiber]
    exact sum_min_sub_two_mul L

end DirectedReciprocity
