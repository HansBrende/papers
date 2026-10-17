import Transpose.Tape.MStarDiscrete
import Transpose.Tape.MStarExcess

/-!
# Theorem M* for block walks: the machine-free core

The limit argument of Theorem M\*, for abstract walks. At each size `n_i` there are `k` walks
`h_i t : ℕ → ℤ` with unit steps before `T_i`, a length `T_i ≤ c L_i`, blocks of
`r_i = blockSize G n_i` cells of `G` bits, and **the cut inequality of Discrete Isoperimetry**
(`CutIneq`, `DefsM.lean`): for every slot labelling with at most `m` slots per label and `M_b` label
changes,

  `(n − M_b)(n − 2m) b ≤ (M_b + 1) D + M_b s + r G (3k M_b + Σ_t χ_t)`,

with `χ_t` the chords of tape `t` between different labels, a co-entropy `D` and `s` extra bits per
label change. If `(D_i + s_i) / L_i → 0`, then the rescaled block walks (`blockTraj`), frozen at
`T_i`, have uniformly convergent subsequences on `[0, c₀]`, `c₀ = c G + 1` (when the walks start at
`0`), and every subsequential limit is 1-Lipschitz, satisfies (★) and has the labelling-free
properties of `excess_of_star` (`theoremMStar_walk`, the most general form of Theorem M\*; every
other form is an instance). Code-carrying diagrams (`MStarDiagram.lean`) and machines
(`MStarClass.lean`) are instances. The walk lemmas used here ((V1′), (V2′), `N ≤ c₀ n`, 1-Lipschitz
limits, Arzelà–Ascoli) are in `MStarTM.lean`.

* `mstar_arith` (the final arithmetic);
* `mstar_discrete_walk` (the per-size inequality), `mstar_single_walk` (one large size),
  `slack_small_walk` (the slack is `o(n)`), `walk_levelChords_limsup_le` (the limsup bound for
  frozen walks), `mstar_core_walk` (real `θ > 0`, by contradiction) and `mstar_level_walk` (any `θ`,
  for walks with unit steps and `G ≥ 1`);
* `div_inputLength_tendsto`: `D = O(n b)` is `o(L)`;
* `theoremMStar_walk`: the walks need unit steps only before `T_i` (the cut inequality reads them
  only there, `pairRes_eq_of_agree`), and no `G ≥ 1` (at `G = 0` there are no slots, so the cut
  inequality forces `n² b ≤ D`, against `D / L → 0`); `theoremMStar_level_walk` is its case
  `φ = id`.
-/

namespace Transpose.Tape.Impl

open Transpose MeasureTheory Filter Topology TSDiagram

open scoped ENNReal

/-! ### The per-size inequality -/

/-- **The final arithmetic.** If `(n - M)(n - 2m) b ≤ R` with `m ≤ θ n + B + 1`, `n ≥ M`,
`R ≤ (n b + G)(n X + C)`, `X ≤ 1 - 2θ - g/2` and `g ≥ 0`, then `n g / 2 ≤ C₂`, with `C₂` explicit
and independent of `n`. -/
theorem mstar_arith {n b G M B C X θ g A₂ R : ℝ} (hn : 1 ≤ n) (hb : 1 ≤ b) (hG : 0 ≤ G)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hnM : M ≤ n) (hA₂ : n - 2 * (θ * n + B + 1) ≤ A₂)
    (hmain : (n - M) * A₂ * b ≤ R) (hR : R ≤ (n * b + G) * (n * X + C))
    (hX : X ≤ 1 - 2 * θ - g / 2) (hg : 0 ≤ g) :
    n * g / 2 ≤ 2 * B + 2 + M + C + G + G * C := by
  have hbn : 1 ≤ b * n := by nlinarith
  have h1 : (n - M) * (n * (1 - 2 * θ) - 2 * B - 2) * b ≤ (n - M) * A₂ * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      (by linarith)
  have h2 : b * n * (n * X) ≤ b * n * (n * (1 - 2 * θ - g / 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (by linarith)) (by linarith)
  have h3 : G * (n * X) ≤ G * n :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by linarith) (by linarith)) hG
  have e1 : 0 ≤ θ * M * n * b := by positivity
  have e2 : 0 ≤ B * M * b := by positivity
  have e3 : 0 ≤ M * b := by positivity
  have e4 : 0 ≤ G * n * (b - 1) := mul_nonneg (by positivity) (by linarith)
  have e5 : 0 ≤ G * C * (b * n - 1) := mul_nonneg (by positivity) (by linarith)
  have h4 : b * n * (n * g / 2) ≤ b * n * (2 * B + 2 + M + C + G + G * C) := by nlinarith
  exact le_of_mul_le_mul_left h4 (by linarith)

open Classical in
/-- **The discrete inequality for walks**: the cut inequality for the M\* labelling, with the
crossing chords split into short, `S`-touching and long label-crossing ones (`crossChords_split`). -/
theorem mstar_discrete_walk {k n G r T D s : ℕ} {h : Fin k → ℕ → ℤ} {c₀ θ η : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrG : r * G ≤ n * entryBits n + G)
    (hh : ∀ t, UnitSteps (h t)) (hN : (numSlots r T : ℝ) ≤ c₀ * n) (hθ : 0 < θ)
    (hcut : CutIneq n G r T D s h)
    {S : Set ℝ} {I : Finset (ℝ × ℝ)} (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2) {β : ℝ → ℕ}
    {Z : Finset ℝ}
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ →
      (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) → β u = β v)
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ ENNReal.ofReal θ) :
    (n - 2 * (mstarBreaks Z I c₀ θ).card) *
        (n - 2 * (⌊θ * n⌋₊ + 2 * (Z ∪ endpts I).card + 1)) * entryBits n ≤
      (2 * (mstarBreaks Z I c₀ θ).card + 1) * D + 2 * (mstarBreaks Z I c₀ θ).card * s +
        (n * entryBits n + G) * (3 * k * (2 * (mstarBreaks Z I c₀ θ).card) +
          ∑ t : Fin k, (2 * (mstarBreaks Z I c₀ θ).card * (⌈η * n⌉₊ + 1) +
            2 * ((Finset.range (numSlots r T)).filter (fun y : ℕ => (y : ℝ) / n ∈ S)).card +
            (longCross (pairRes r (h t) T) S β n η (numSlots r T)).card)) := by
  classical
  set N := numSlots r T with hNdef
  set lab := mstarLabel S β θ n with hlab
  set Mc := 2 * (mstarBreaks Z I c₀ θ).card with hMc
  set m := ⌊θ * n⌋₊ + 2 * (Z ∪ endpts I).card + 1 with hm
  set YS := (Finset.range N).filter (fun y : ℕ => (y : ℝ) / n ∈ S) with hYS
  have hn0 : 0 < n := by omega
  have hclassN : ∀ ℓ, ((Finset.range N).filter (fun y => lab y = ℓ)).card ≤ m :=
    fun ℓ => mstar_class_le hθ hn0 hN hSI hβZ hclass ℓ
  have hbits := hcut lab m hclassN
  have hMb : labelChanges lab N ≤ Mc := mstar_labelChanges_le hθ hn0 hN hSI hβZ
  -- the chord split, tape by tape
  have hsplit : ∀ t : Fin k,
      (crossChords (pairRes r (h t) T) lab N).card ≤
        Mc * (⌈η * n⌉₊ + 1) + 2 * YS.card + (longCross (pairRes r (h t) T) S β n η N).card := by
    intro t
    have hc := crossChords_split (R := pairRes r (h t) T)
      (fun he he' => pairRes_chord_source_unique (hh t) hr T he he')
      (fun he he' => pairRes_chord_target_unique (hh t) hr T he he')
      lab N n η S β (mstarLabel_hlab S β θ n)
    rw [← hYS] at hc
    have : labelChanges lab N * (⌈η * n⌉₊ + 1) ≤ Mc * (⌈η * n⌉₊ + 1) :=
      Nat.mul_le_mul_right _ hMb
    omega
  have hsum : ∑ t : Fin k, (crossChords (pairRes r (h t) T) lab N).card ≤
      ∑ t : Fin k, (Mc * (⌈η * n⌉₊ + 1) + 2 * YS.card +
        (longCross (pairRes r (h t) T) S β n η N).card) :=
    Finset.sum_le_sum (fun t _ => hsplit t)
  calc (n - Mc) * (n - 2 * m) * entryBits n
      ≤ (n - labelChanges lab N) * (n - 2 * m) * entryBits n := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
    _ ≤ (labelChanges lab N + 1) * D + labelChanges lab N * s +
          r * G * (3 * k * labelChanges lab N +
            ∑ t, (crossChords (pairRes r (h t) T) lab N).card) := hbits
    _ ≤ (Mc + 1) * D + Mc * s + (n * entryBits n + G) * (3 * k * Mc +
          ∑ t : Fin k, (Mc * (⌈η * n⌉₊ + 1) + 2 * YS.card +
            (longCross (pairRes r (h t) T) S β n η N).card)) := by
        apply Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
          (Nat.mul_le_mul_right _ hMb))
        exact Nat.mul_le_mul hrG (Nat.add_le_add (Nat.mul_le_mul_left _ hMb) hsum)

/-- The constant of the single-size bound for walks. -/
noncomputable def walkConst (k G Mc B₃ E : ℕ) : ℝ :=
  2 * (B₃ : ℝ) + 2 + Mc + (k : ℝ) * (5 * Mc + 4 * E) + G + G * ((k : ℝ) * (5 * Mc + 4 * E))

/-- **One large size.** If every walk's long crossing chords number at most `n (K_t + δ)`, then
`n · gap / 2` is at most a constant independent of `n` plus the slack
`(1 + G)((M_c + 1) D + M_c s) / (n b + G)`. -/
theorem mstar_single_walk {k n G r T D s : ℕ} {h : Fin k → ℕ → ℤ} {c₀ θ η δ gap : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrG : r * G ≤ n * entryBits n + G)
    (hh : ∀ t, UnitSteps (h t)) (hN : (numSlots r T : ℝ) ≤ c₀ * n) (hθ : 0 < θ)
    (hcut : CutIneq n G r T D s h)
    {S : Set ℝ} {I : Finset (ℝ × ℝ)} (hSI : S = ⋃ x ∈ I, Set.Icc x.1 x.2) {β : ℝ → ℕ}
    {Z : Finset ℝ}
    (hβZ : ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ →
      (∀ x ∈ Set.Icc u v, x ∉ S ∧ x ∉ (Z : Set ℝ)) → β u = β v)
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 c₀ ∧ u ∉ S ∧ β u = ℓ} ≤ ENNReal.ofReal θ)
    {Mc B₃ E : ℕ} (hMc : 2 * (mstarBreaks Z I c₀ θ).card = Mc)
    (hB₃ : 2 * (Z ∪ endpts I).card = B₃) (hE : (endpts I).card = E)
    {K : Fin k → ℝ} (hK0 : ∀ t, 0 ≤ K t)
    (hX : ∀ t, ((longCross (pairRes r (h t) T) S β n η (numSlots r T)).card : ℝ) ≤
      n * (K t + δ))
    (hη : 0 < η) (hgap : 0 ≤ gap)
    (hηsmall : (k : ℝ) * Mc * η ≤ gap / 4) (hδsmall : (k : ℝ) * δ ≤ gap / 4)
    {sv : ℝ} (hs : sv = (volume (S ∩ Set.Icc 0 c₀)).toReal)
    (hsum : (∑ t, K t) + 2 * θ + 2 * k * sv = 1 - gap) :
    (n : ℝ) * gap / 2 ≤ walkConst k G Mc B₃ E +
      (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * D + Mc * s) / ((n : ℝ) * entryBits n + G) := by
  classical
  have hn0 : 0 < n := by omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb1 : 1 ≤ entryBits n := by unfold entryBits; omega
  have hbr : (1 : ℝ) ≤ entryBits n := by exact_mod_cast hb1
  have hs0 : 0 ≤ sv := by rw [hs]; exact ENNReal.toReal_nonneg
  have hsumK : 0 ≤ ∑ t, K t := Finset.sum_nonneg (fun t _ => hK0 t)
  have hg1 : gap ≤ 1 := by nlinarith
  obtain ⟨Sl, hSl⟩ : ∃ Sl : ℝ, Sl = ((Mc : ℝ) + 1) * D + Mc * s := ⟨_, rfl⟩
  rw [← hSl]
  have hSl0 : 0 ≤ Sl := by rw [hSl]; positivity
  have hden : (0 : ℝ) < (n : ℝ) * entryBits n + G := by positivity
  have hslack0 : (0 : ℝ) ≤ (1 + (G : ℝ)) * Sl / ((n : ℝ) * entryBits n + G) := by positivity
  unfold walkConst
  -- `n ≥ M_cut`, or the claim is immediate
  rcases lt_or_ge n Mc with hsmall | hnMc
  · have h1 : (n : ℝ) ≤ Mc := by exact_mod_cast hsmall.le
    have h2 : (n : ℝ) * gap / 2 ≤ Mc := by nlinarith
    have h4 : (0 : ℝ) ≤ (G : ℝ) * ((k : ℝ) * (5 * Mc + 4 * E)) := by positivity
    have h5 : (0 : ℝ) ≤ (B₃ : ℝ) := by positivity
    have h6 : (0 : ℝ) ≤ (G : ℝ) := by positivity
    have h7 : (0 : ℝ) ≤ (k : ℝ) * (5 * Mc + 4 * E) := by positivity
    linarith
  -- the slots in `S`
  have hYS := slots_in_S_le (I := I) hn0 hN hSI
  rw [← hs, hE] at hYS
  generalize hYSdef : ((Finset.range (numSlots r T)).filter
    (fun y : ℕ => (y : ℝ) / n ∈ S)).card = YS at hYS
  -- the inner bound
  set Xp : ℝ := (k : ℝ) * Mc * η + 2 * k * sv + (∑ t, K t) + k * δ with hXp
  have hXbound : Xp ≤ 1 - 2 * θ - gap / 2 := by rw [hXp]; linarith
  have hin : 3 * (k : ℝ) * Mc + ∑ t : Fin k, ((Mc : ℝ) * (⌈η * n⌉₊ + 1) + 2 * YS +
      ((longCross (pairRes r (h t) T) S β n η (numSlots r T)).card : ℝ)) ≤
      n * Xp + (k : ℝ) * (5 * Mc + 4 * E) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hceil : (⌈η * n⌉₊ : ℝ) ≤ η * n + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h1 : (Mc : ℝ) * (⌈η * n⌉₊ + 1) + 2 * YS ≤
        (Mc : ℝ) * (η * n + 2) + 2 * (n * sv + 2 * E) := by
      have : (Mc : ℝ) * (⌈η * n⌉₊ + 1) ≤ (Mc : ℝ) * (η * n + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h2 := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin k))) => hX t)
    have h3 : ∑ t : Fin k, (n : ℝ) * (K t + δ) = n * ((∑ t, K t) + k * δ) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have h4 : (k : ℝ) * ((Mc : ℝ) * (⌈η * n⌉₊ + 1) + 2 * YS) ≤
        k * ((Mc : ℝ) * (η * n + 2) + 2 * (n * sv + 2 * E)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : 3 * (k : ℝ) * Mc + (k * ((Mc : ℝ) * (η * n + 2) + 2 * (n * sv + 2 * E)) +
        n * ((∑ t, K t) + k * δ)) = n * Xp + (k : ℝ) * (5 * Mc + 4 * E) := by
      rw [hXp]; ring
    linarith
  have hA₂ : (n : ℝ) - 2 * (θ * n + B₃ + 1) ≤ ((n - 2 * (⌊θ * n⌋₊ + B₃ + 1) : ℕ) : ℝ) := by
    have hfl : (⌊θ * n⌋₊ : ℝ) ≤ θ * n := Nat.floor_le (by positivity)
    rcases le_total (2 * (⌊θ * n⌋₊ + B₃ + 1)) n with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have : (n : ℝ) ≤ 2 * (⌊θ * n⌋₊ + B₃ + 1) := by exact_mod_cast h
      linarith
  -- the per-`n` inequality, in `ℝ`
  have hDd := mstar_discrete_walk (η := η) hn hr hrG hh hN hθ hcut hSI hβZ hclass
  rw [hMc, hB₃, hYSdef] at hDd
  have hDr := (Nat.cast_le (α := ℝ)).2 hDd
  clear hDd
  push_cast at hDr
  rw [Nat.cast_sub hnMc] at hDr
  have hR := mul_le_mul_of_nonneg_left hin
    (show (0 : ℝ) ≤ (n : ℝ) * entryBits n + G by positivity)
  have hcancel : ((n : ℝ) * entryBits n + G) *
      (Sl / ((n : ℝ) * entryBits n + G)) = Sl := mul_div_cancel₀ _ (ne_of_gt hden)
  have hfin := mstar_arith (n := n) (b := entryBits n) (G := G) (M := Mc) (B := B₃)
    (C := (k : ℝ) * (5 * Mc + 4 * E) + Sl / ((n : ℝ) * entryBits n + G))
    (X := Xp) (θ := θ) (g := gap)
    hnr hbr (by positivity) (by positivity) (by positivity) (by positivity) hθ.le
    (by exact_mod_cast hnMc) hA₂ hDr (by rw [hSl] at hcancel ⊢; linarith) hXbound hgap
  have e : (1 + (G : ℝ)) * Sl / ((n : ℝ) * entryBits n + G) =
      Sl / ((n : ℝ) * entryBits n + G) + G * (Sl / ((n : ℝ) * entryBits n + G)) := by ring
  rw [e]
  linarith

/-- **The slack is eventually at most `n · g / 4`** when `(D + s) / L → 0`. -/
theorem slack_small_walk (G : ℕ) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) {Ds ss : ℕ → ℕ}
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    (Mc : ℕ) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ i in atTop, (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * Ds i + Mc * ss i) /
      ((ns i : ℝ) * entryBits (ns i) + G) ≤ ns i * g / 4 := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (1 + (G : ℝ)) * ((Mc : ℝ) + 1) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hKne : K ≠ 0 := hK0.ne'
  have hev : ∀ᶠ i in atTop, ((Ds i : ℝ) + ss i) / inputLength (ns i) < g / (4 * K) :=
    hDL.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev, hns.eventually_ge_atTop 1] with i h1 hn1
  have hb1 : 1 ≤ entryBits (ns i) := by unfold entryBits; omega
  have hnr : (1 : ℝ) ≤ ns i := by exact_mod_cast hn1
  have hbr : (1 : ℝ) ≤ entryBits (ns i) := by exact_mod_cast hb1
  have hL : (inputLength (ns i) : ℝ) = ns i * ns i * entryBits (ns i) := by
    rw [inputLength]; push_cast; ring
  have hLpos : (0 : ℝ) < inputLength (ns i) := by rw [hL]; positivity
  have hD : (Ds i : ℝ) + ss i ≤ g / (4 * K) * (ns i * ns i * entryBits (ns i)) := by
    rw [div_lt_iff₀ hLpos, hL] at h1; linarith
  have hnum : (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * Ds i + Mc * ss i) ≤ K * ((Ds i : ℝ) + ss i) := by
    have hss : (0 : ℝ) ≤ ss i := by positivity
    have : ((Mc : ℝ) + 1) * Ds i + Mc * ss i ≤ ((Mc : ℝ) + 1) * ((Ds i : ℝ) + ss i) := by
      nlinarith
    have hG0 : (0 : ℝ) ≤ 1 + (G : ℝ) := by positivity
    calc _ ≤ (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * ((Ds i : ℝ) + ss i)) :=
          mul_le_mul_of_nonneg_left this hG0
      _ = K * ((Ds i : ℝ) + ss i) := by rw [hK]; ring
  have hnb : (0 : ℝ) < ns i * entryBits (ns i) := by positivity
  have hnum0 : (0 : ℝ) ≤ (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * Ds i + Mc * ss i) := by positivity
  have hG0 : (0 : ℝ) ≤ G := by positivity
  calc (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * Ds i + Mc * ss i) / ((ns i : ℝ) * entryBits (ns i) + G)
      ≤ (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * Ds i + Mc * ss i) / ((ns i : ℝ) * entryBits (ns i)) :=
        div_le_div_of_nonneg_left hnum0 hnb (by linarith)
    _ ≤ ns i * g / 4 := by
        rw [div_le_iff₀ hnb]
        calc (1 + (G : ℝ)) * (((Mc : ℝ) + 1) * Ds i + Mc * ss i) ≤ K * ((Ds i : ℝ) + ss i) := hnum
          _ ≤ K * (g / (4 * K) * (ns i * ns i * entryBits (ns i))) :=
              mul_le_mul_of_nonneg_left hD hK0.le
          _ = ns i * g / 4 * (ns i * entryBits (ns i)) := by field_simp

/-! ### The limsup bound for frozen walks -/

/-- **The limsup bound for frozen walks**: the long label-crossing chords of a walk, per `n`, have
`limsup ≤ ∫⁻ κ`, when the rescaled frozen block walks converge uniformly. -/
theorem walk_levelChords_limsup_le {G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts : ℕ → ℕ} {hs : ℕ → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, UnitSteps (hs i))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i)) {P : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i)
      (fun τ => hs i (min τ (Ts i)))) P atTop (Set.Icc 0 (c * G + 1)))
    {η : ℝ} (hη : 0 < η) {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1)) :
    limsup (fun i => ((longCross (pairRes (blockSize G (ns i)) (hs i) (Ts i)) S β (ns i) η
        (numSlots (blockSize G (ns i)) (Ts i))).card : ℝ≥0∞) / ns i) atTop ≤
      ∫⁻ p, levelCross P S β (c * G + 1) p := by
  have hn1 : ∀ᶠ i in atTop, 1 ≤ ns i := hns.eventually_ge_atTop 1
  have hlip : LipschitzOnWith 1 P (Set.Icc 0 (c * G + 1)) :=
    blockTraj_limit_lipschitz hns (by
      filter_upwards [hunit, hn1] with i hi hni
      exact ⟨unitSteps_frozen hi _, one_le_blockSize hG hni⟩) hconv
  apply levelChords_limsup_le (D := 1) hη hlip hns
    (W := fun i y => curBlock (blockSize G (ns i)) (fun τ => hs i (min τ (Ts i)))
      (y * blockSize G (ns i)))
  · filter_upwards [hn1, htime] with i hi hti
    exact numSlots_le_of hi (blockSize_mul_ge hG) hti
  · filter_upwards [hn1, hunit] with i hi hui
    intro y σ hσ
    have := frozen_V1 hui (one_le_blockSize hG hi) (Ts i) y hσ
    exact_mod_cast this
  · filter_upwards [hn1, hunit] with i hi hui
    intro y₁ y₂ σ hy hσ
    exact frozen_V2 hui (one_le_blockSize hG hi) hy hσ
  · exact hconv
  · exact hS
  · exact hβ

/-! ### Theorem M* for walks -/

/-- **Theorem M\* for walks, real `θ > 0`** (the core, by contradiction at one large size). -/
theorem mstar_core_walk {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts Ds ss : ℕ → ℕ} {hs : ℕ → Fin k → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, ∀ t, UnitSteps (hs i t))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hcut : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hs i))
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    {P : Fin k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i)
      (fun τ => hs i t (min τ (Ts i)))) (P t) atTop (Set.Icc 0 (c * G + 1)))
    {θ : ℝ} (hθ : 0 < θ) {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤
      ENNReal.ofReal θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * ENNReal.ofReal θ +
      2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) := by
  classical
  set c₀ : ℝ := c * G + 1 with hc₀
  by_contra hlt
  push Not at hlt
  have hVfin : volume (S ∩ Set.Icc 0 c₀) ≠ ⊤ := ne_top_of_le_ne_top
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono Set.inter_subset_right)
  have hκfin : ∀ t, ∫⁻ p, levelCross (P t) S β c₀ p ≠ ⊤ := by
    intro t
    apply ne_top_of_lt (b := 1)
    calc ∫⁻ p, levelCross (P t) S β c₀ p
        ≤ ∑ t, ∫⁻ p, levelCross (P t) S β c₀ p :=
          Finset.single_le_sum (f := fun t => ∫⁻ p, levelCross (P t) S β c₀ p)
            (fun _ _ => zero_le) (Finset.mem_univ t)
      _ ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) + 2 * ENNReal.ofReal θ +
            2 * k * volume (S ∩ Set.Icc 0 c₀) := le_self_add.trans le_self_add
      _ < 1 := hlt
  obtain ⟨K, hK⟩ : ∃ K : Fin k → ℝ,
      K = fun t => (∫⁻ p, levelCross (P t) S β c₀ p).toReal := ⟨_, rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : ℝ, sv = (volume (S ∩ Set.Icc 0 c₀)).toReal := ⟨_, rfl⟩
  have hK0 : ∀ t, 0 ≤ K t := by intro t; rw [hK]; exact ENNReal.toReal_nonneg
  have hs0 : 0 ≤ sv := by rw [hsv]; exact ENNReal.toReal_nonneg
  have hKeq : ∀ t, ∫⁻ p, levelCross (P t) S β c₀ p = ENNReal.ofReal (K t) := by
    intro t; rw [hK, ENNReal.ofReal_toReal (hκfin t)]
  have hsumK : 0 ≤ ∑ t, K t := Finset.sum_nonneg (fun t _ => hK0 t)
  have hreal : (∑ t, K t) + 2 * θ + 2 * k * sv < 1 := by
    have e1 : (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p) = ENNReal.ofReal (∑ t, K t) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => hK0 t)]
      exact Finset.sum_congr rfl (fun t _ => hKeq t)
    have e3 : (2 : ℝ≥0∞) * ENNReal.ofReal θ = ENNReal.ofReal (2 * θ) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have e4 : (2 : ℝ≥0∞) * k * volume (S ∩ Set.Icc 0 c₀) = ENNReal.ofReal (2 * k * sv) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), hsv,
        ENNReal.ofReal_toReal hVfin, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
    rw [e1, e3, e4, ← ENNReal.ofReal_add hsumK (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).1 hlt
  obtain ⟨gap, hgapdef⟩ : ∃ gap : ℝ, gap = 1 - ((∑ t, K t) + 2 * θ + 2 * k * sv) := ⟨_, rfl⟩
  have hgap0 : 0 < gap := by rw [hgapdef]; linarith
  have hsum : (∑ t, K t) + 2 * θ + 2 * k * sv = 1 - gap := by rw [hgapdef]; ring
  obtain ⟨I, hSI⟩ := hS
  obtain ⟨Z, hβZ⟩ := hβ
  obtain ⟨Mc, hMc⟩ : ∃ Mc, 2 * (mstarBreaks Z I c₀ θ).card = Mc := ⟨_, rfl⟩
  obtain ⟨B₃, hB₃⟩ : ∃ B₃, 2 * (Z ∪ endpts I).card = B₃ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, (endpts I).card = E := ⟨_, rfl⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = gap / (4 * ((k : ℝ) * Mc + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηsmall : (k : ℝ) * Mc * η ≤ gap / 4 := by
    rw [hηdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = gap / (4 * ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : (k : ℝ) * δ ≤ gap / 4 := by
    rw [hδdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the limsup bound on every walk
  have hX : ∀ᶠ i in atTop, ∀ t : Fin k,
      ((longCross (pairRes (blockSize G (ns i)) (hs i t) (Ts i)) S β (ns i) η
        (numSlots (blockSize G (ns i)) (Ts i))).card : ℝ) ≤ ns i * (K t + δ) := by
    rw [Filter.eventually_all]
    intro t
    have hL := walk_levelChords_limsup_le hG hns (hunit.mono fun i h => h t) htime (hconv t) hη
      ⟨I, hSI⟩ ⟨Z, hβZ⟩
    have hlt' : ∫⁻ p, levelCross (P t) S β c₀ p < ENNReal.ofReal (K t + δ) := by
      rw [hKeq t]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [hK0 t])).2 (by linarith)
    have hev := eventually_lt_of_limsup_lt (lt_of_le_of_lt hL hlt')
    filter_upwards [hev, hns.eventually_ge_atTop 1] with i hi hn1
    have hnpos : (0 : ℝ) < ns i := by exact_mod_cast (show 0 < ns i by omega)
    generalize (longCross (pairRes (blockSize G (ns i)) (hs i t) (Ts i)) S β (ns i) η
      (numSlots (blockSize G (ns i)) (Ts i))).card = X at hi ⊢
    have e : (X : ℝ≥0∞) / (ns i : ℝ≥0∞) = ENNReal.ofReal ((X : ℝ) / ns i) := by
      rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [e] at hi
    have := (ENNReal.ofReal_lt_ofReal_iff (by linarith [hK0 t])).1 hi
    rw [div_lt_iff₀ hnpos] at this
    linarith
  -- a large size, at which the slack is at most `n · gap / 4`
  have hslack := slack_small_walk G hns hDL Mc hgap0
  obtain ⟨i, hXi, hcuti, hui, htimi, hsli, hni⟩ := (hX.and (hcut.and (hunit.and (htime.and
    (hslack.and (hns.eventually_ge_atTop (⌈4 * walkConst k G Mc B₃ E / gap⌉₊ + 1))))))).exists
  have hn1 : 1 ≤ ns i := by omega
  have hr1 := one_le_blockSize hG hn1
  have hfin := mstar_single_walk hn1 hr1 (blockSize_mul_le G (ns i)) hui
    (numSlots_le_of hn1 (blockSize_mul_ge hG) htimi) hθ hcuti hSI hβZ hclass hMc hB₃ hE hK0
    hXi hη hgap0.le hηsmall hδsmall hsv hsum
  have hbig : 4 * walkConst k G Mc B₃ E / gap < ns i := by
    have h1 := Nat.le_ceil (4 * walkConst k G Mc B₃ E / gap)
    have h2 : ((⌈4 * walkConst k G Mc B₃ E / gap⌉₊ + 1 : ℕ) : ℝ) ≤ ns i := by exact_mod_cast hni
    push_cast at h2
    linarith
  rw [div_lt_iff₀ hgap0] at hbig
  linarith

/-- **Theorem M\* for walks with unit steps and `G ≥ 1`** (level form, any `θ`): if the walks of
every large size satisfy the cut inequality with `(D + s) / L → 0`, have unit steps and length
`T ≤ c L`, and their rescaled frozen block walks converge uniformly to `P` on `[0, c₀]`
(`c₀ = c G + 1`), then `1 ≤ Σ_t ∫⁻ κ_t + 2θ + 2k |S ∩ [0, c₀]|`. -/
theorem mstar_level_walk {k G : ℕ} (hG : 1 ≤ G) {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts Ds ss : ℕ → ℕ} {hs : ℕ → Fin k → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, ∀ t, UnitSteps (hs i t))
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hcut : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hs i))
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    {P : Fin k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i)
      (fun τ => hs i t (min τ (Ts i)))) (P t) atTop (Set.Icc 0 (c * G + 1)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
      2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) := by
  rcases eq_or_ne θ ⊤ with rfl | hθtop
  · rw [ENNReal.mul_top (by norm_num)]; simp
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε' : (0 : ℝ) < ε := hε
    have hθ' : 0 < θ.toReal + ε / 2 := by positivity
    have hcls : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤
        ENNReal.ofReal (θ.toReal + ε / 2) := by
      intro ℓ
      calc volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ := hclass ℓ
        _ = ENNReal.ofReal θ.toReal := (ENNReal.ofReal_toReal hθtop).symm
        _ ≤ ENNReal.ofReal (θ.toReal + ε / 2) := ENNReal.ofReal_le_ofReal (by linarith)
    have hcore := mstar_core_walk hG hns hunit htime hcut hDL hconv hθ' hS hβ hcls
    have e : (2 : ℝ≥0∞) * ENNReal.ofReal (θ.toReal + ε / 2) = 2 * θ + ε := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hθtop,
        mul_add]
      congr 1
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        show (2 : ℝ) * (ε / 2) = ε by ring, ENNReal.ofReal_coe_nnreal]
    rw [e] at hcore
    calc (1 : ℝ≥0∞) ≤ _ := hcore
      _ = _ := by ring

/-! ### `o(L)` -/

/-- **`D / L → 0` for any `D = O(n b)`.** -/
theorem div_inputLength_tendsto {C : ℕ} {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {Ds : ℕ → ℕ} (hDs : ∀ᶠ i in atTop, Ds i ≤ C * ns i * entryBits (ns i)) :
    Tendsto (fun i => (Ds i : ℝ) / inputLength (ns i)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)).comp hns)
  · exact Eventually.of_forall (fun i => by positivity)
  · filter_upwards [hDs, hns.eventually_ge_atTop 1] with i hi hn
    have hb1 : 1 ≤ entryBits (ns i) := by unfold entryBits; omega
    have hnr : (0 : ℝ) < ns i := by exact_mod_cast (show 0 < ns i by omega)
    have hbr : (0 : ℝ) < entryBits (ns i) := by
      exact_mod_cast (show 0 < entryBits (ns i) by omega)
    have hi' : (Ds i : ℝ) ≤ C * ns i * entryBits (ns i) := by exact_mod_cast hi
    simp only [Function.comp_apply, inputLength]; push_cast
    rw [div_le_div_iff₀ (by positivity) hnr]
    nlinarith

/-! ### Theorem M* for walks: the most general form -/

/-- **Theorem M\* for walks** (the most general form). At sizes `n_i → ∞`, let `k` walks `h_i t`
have unit steps before `T_i`, length `T_i ≤ c L_i`, and satisfy the cut inequality (blocks of
`r_i = blockSize G n_i` cells of `G` bits) with co-entropy `D_i` and `s_i` bits per label change,
where `(D_i + s_i) / L_i → 0`. Then, if the walks start at `0`, their rescaled block walks frozen
at `T_i` have a uniformly convergent subsequence on `[0, c₀]`, `c₀ = c G + 1`; and every
subsequential limit `P` is 1-Lipschitz, satisfies (★), has total excess multiplicity `≥ 1` and
total range `≤ k c₀ − 1`, and is not monotone on every tape. -/
theorem theoremMStar_walk {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts Ds ss : ℕ → ℕ} {hs : ℕ → Fin k → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, ∀ t, ∀ τ < Ts i, |hs i t (τ + 1) - hs i t τ| ≤ 1)
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hcut : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hs i))
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0)) :
    ((∀ᶠ i in atTop, ∀ t, hs i t 0 = 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : Fin k → ℝ → ℝ, ∀ t,
      TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns (φ i))) (ns (φ i))
        (fun τ => hs (φ i) t (min τ (Ts (φ i))))) (P t) atTop (Set.Icc 0 (c * G + 1))) ∧
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ P : Fin k → ℝ → ℝ,
      (∀ t, TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns (φ i))) (ns (φ i))
        (fun τ => hs (φ i) t (min τ (Ts (φ i))))) (P t) atTop (Set.Icc 0 (c * G + 1))) →
      (∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1))) ∧
      (∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S → PiecewiseConstOn β S (c * G + 1) →
        (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
        1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
          2 * k * volume (S ∩ Set.Icc 0 (c * G + 1))) ∧
      1 ≤ ∑ t, ∫⁻ p, levelExcess (P t) (c * G + 1) p ∧
      1 + ∑ t, volume (P t '' Set.Icc 0 (c * G + 1)) ≤ k * ENNReal.ofReal (c * G + 1) ∧
      ¬ ∀ t, MonotoneOn (P t) (Set.Icc 0 (c * G + 1)) ∨
        AntitoneOn (P t) (Set.Icc 0 (c * G + 1)) := by
  -- `G = 0`: no slots, so the cut inequality says `n² b ≤ D`, against `D / L → 0`
  rcases Nat.eq_zero_or_pos G with rfl | hG
  · exfalso
    obtain ⟨i, hci, hi, hn⟩ := (hcut.and ((hDL.eventually (gt_mem_nhds one_pos)).and
      (hns.eventually_ge_atTop 1))).exists
    have h := hci (fun _ => 0) 0 (fun _ => by simp [blockSize, numSlots])
    simp only [blockSize, numSlots, Nat.div_zero, labelChanges, Finset.range_zero,
      Finset.filter_empty, Finset.card_empty] at h
    have hb : 1 ≤ entryBits (ns i) := by unfold entryBits; omega
    have hL : (0 : ℝ) < inputLength (ns i) := by unfold inputLength; positivity
    rw [div_lt_one hL] at hi
    have : ((ns i * ns i * entryBits (ns i) : ℕ) : ℝ) ≤ Ds i := by exact_mod_cast (by simpa using h)
    have hs0 : (0 : ℝ) ≤ ss i := Nat.cast_nonneg _
    unfold inputLength at hi
    push_cast at hi this
    linarith
  -- the frozen walks: unit steps everywhere, the same residencies, the same frozen walks
  set hf : ℕ → Fin k → ℕ → ℤ := fun i t τ => hs i t (min τ (Ts i)) with hfdef
  have hfu : ∀ᶠ i in atTop, ∀ t, UnitSteps (hf i t) := by
    filter_upwards [hunit] with i hi t τ
    show |hs i t (min (τ + 1) (Ts i)) - hs i t (min τ (Ts i))| ≤ 1
    rcases lt_or_ge τ (Ts i) with h | h
    · rw [min_eq_left (show τ + 1 ≤ Ts i by omega), min_eq_left h.le]; exact hi t τ h
    · rw [min_eq_right (show Ts i ≤ τ + 1 by omega), min_eq_right h]; simp
  have hfc : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hf i) := by
    filter_upwards [hcut] with i hi
    have hpr : ∀ t, pairRes (blockSize G (ns i)) (hf i t) (Ts i) =
        pairRes (blockSize G (ns i)) (hs i t) (Ts i) := fun t => by
      funext y; exact pairRes_eq_of_agree (fun σ hσ => by simp [hfdef, min_eq_left hσ.le]) y
    unfold CutIneq at hi ⊢
    simpa only [hpr] using hi
  have hff : ∀ i t, (fun τ => hf i t (min τ (Ts i))) = hf i t := fun i t => by
    funext τ; simp [hfdef]
  have hgood : ∀ᶠ i in atTop, 1 ≤ blockSize G (ns i) ∧ ∀ t, UnitSteps (hf i t) :=
    (hfu.and (hns.eventually_ge_atTop 1)).mono fun i h => ⟨one_le_blockSize hG h.2, h.1⟩
  refine ⟨fun h0 => exists_subseq_blockTraj _ hns (rs := fun i => blockSize G (ns i)) (hs := hf)
    ((hgood.and h0).mono fun i h => ⟨h.1.1, fun t => ⟨h.1.2 t, by simp [hfdef, h.2 t]⟩⟩),
    fun φ hφ P hP => ?_⟩
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hlip : ∀ t, LipschitzOnWith 1 (P t) (Set.Icc 0 (c * G + 1)) := fun t =>
    blockTraj_limit_lipschitz (hns.comp hφt) (rs := fun i => blockSize G (ns (φ i)))
      (hs := fun i => hf (φ i) t)
      ((hφt.eventually hgood).mono fun i hi => ⟨hi.2 t, hi.1⟩) (hP t)
  have hstar : ∀ (θ : ℝ≥0∞) (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S (c * G + 1) →
      (∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
        2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) := fun θ S β hS hβ hcl =>
    mstar_level_walk hG (hns.comp hφt) (Ts := fun i => Ts (φ i)) (Ds := fun i => Ds (φ i))
      (ss := fun i => ss (φ i)) (hs := fun i => hf (φ i)) (hφt.eventually hfu)
      (hφt.eventually htime) (hφt.eventually hfc) (hDL.comp hφt)
      (fun t => (hP t).congr (Eventually.of_forall fun i _u _ => by rw [hff]; rfl)) hS hβ hcl
  exact ⟨hlip, hstar, excess_of_star hlip hstar⟩

/-- **Theorem M\* for walks, level form** (any `θ`): the case `φ = id` of `theoremMStar_walk`. -/
theorem theoremMStar_level_walk {k G : ℕ} {c : ℝ} {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {Ts Ds ss : ℕ → ℕ} {hs : ℕ → Fin k → ℕ → ℤ}
    (hunit : ∀ᶠ i in atTop, ∀ t, ∀ τ < Ts i, |hs i t (τ + 1) - hs i t τ| ≤ 1)
    (htime : ∀ᶠ i in atTop, (Ts i : ℝ) ≤ c * inputLength (ns i))
    (hcut : ∀ᶠ i in atTop, CutIneq (ns i) G (blockSize G (ns i)) (Ts i) (Ds i) (ss i) (hs i))
    (hDL : Tendsto (fun i => ((Ds i : ℝ) + ss i) / inputLength (ns i)) atTop (𝓝 0))
    {P : Fin k → ℝ → ℝ}
    (hconv : ∀ t, TendstoUniformlyOn (fun i => blockTraj (blockSize G (ns i)) (ns i)
      (fun τ => hs i t (min τ (Ts i)))) (P t) atTop (Set.Icc 0 (c * G + 1)))
    {θ : ℝ≥0∞} {S : Set ℝ} (hS : FinUnionIcc S) {β : ℝ → ℕ}
    (hβ : PiecewiseConstOn β S (c * G + 1))
    (hclass : ∀ ℓ, volume {u | u ∈ Set.Icc 0 (c * G + 1) ∧ u ∉ S ∧ β u = ℓ} ≤ θ) :
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β (c * G + 1) p) + 2 * θ +
      2 * k * volume (S ∩ Set.Icc 0 (c * G + 1)) :=
  ((theoremMStar_walk hns hunit htime hcut hDL).2 id strictMono_id P hconv).2.1 θ S β hS hβ hclass

end Transpose.Tape.Impl

