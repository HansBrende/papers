import MergeDepth.EMSimulation
import MergeDepth.Traces

/-!
# Theorem EM and Corollary EM

**Theorem EM** (`theoremEM`). Let `M` be a machine with `k` work tapes, let `c ≥ 0` and let `M`
transpose at dimension `d ≥ 1` within `c (L + 1)` steps (`TransposesAt`). Then there is an
external-memory algorithm over the alphabet `Σ_M` (`Sym M`) with block size `B = d b(d)`,
`2k + 3` slots and a register of at most `γ log₂(2L)` bits, `γ = emGamma k |Q| c`, that is correct
on every input with at most `c₁ d` I/Os, `c₁ = 4(k+1)c + 2` (`emC1`), and oblivious on a set of at
least `2^(L - c₂ d)` input words, `c₂ = (2(k+1)c + 1) log₂(2k + 4)` (`emC2`).

* `em_core`: the simulation as a run, for any machine and any input and output words of length
  `dB`; its I/O sequence is determined by an event word with at most `⌊T₀/B⌋` shifts per tape and
  exactly `d` flushes.
* `em_oblivious`: for any finite set `W` of such inputs, the algorithm is oblivious on a subset
  `C ⊆ W` with `|W| ≤ |C| (2k + 4)^((k + 1)⌊T₀/B⌋ + d)` (the largest fibre of the event word).
* `theoremEM_nat`: the exact form for a natural time bound `T₀`: at most `1 + (2k+1)⌊T₀/B⌋ + d`
  I/Os, and `2^L ≤ |C| (2k+4)^((k+1)⌊T₀/B⌋ + d)`.
* `theoremEM_real`: the same with any real bound `s ≥ ⌊T₀/B⌋`; `theoremEM` takes `s = 2cd`, and
  `theoremEM_sharp` takes `s = cd + c`, which gives `((2k+1)c + 1)d + (2k+1)c + 1` I/Os and the
  exponent `(((k+1)c + 1)d + (k+1)c) log₂(2k + 4)`.

**Corollary EM** (`corollaryEM`). If every correct external-memory transposition that is oblivious
on a set of `2^(L - Ad)` inputs needs more than `Ad` I/Os for all large `d`, for every alphabet,
slot number, register constant `γ` and constant `A` (`EMLowerBound`), then (T) fails:
`¬ Transpose.LinearTimeTransposable`. `corollaryEM_some` needs the bound at one dimension only
(`EMLowerBoundSome`).

## The register

The abstract register `Reg M` is stored through an injective encoding of the finite type
`RegFin M R` (integers clamped to `[-R, R]`) into `regBits M R = ⌈log₂ |RegFin M R|⌉` bits, which
sends the initial register to the zero register (`enc`, `dec`, `dec_enc`, `enc_reg₀`). The
registers of the simulation have all integers in `[-(T₀ + 2), T₀ + 2]` (`Inv.good`), and
`regBits_le` bounds the width by `γ log₂(2L)`.
-/

namespace MergeDepth.EM

open Transpose Transpose.Tape Transpose.Tape.Impl

section Register

variable (M : TM)

instance (k : ℕ) : Nonempty (Phase k) := ⟨.start⟩

/-- Register values with integers in `[-R, R]`, stored as elements of `Fin (2R + 1)`. -/
abbrev RegFin (R : ℕ) :=
  Fin (M.q + 1) × (Fin (M.k + 1) → Fin (2 * R + 1)) × (Fin (M.k + 1) → Fin (2 * R + 1)) ×
    Fin (2 * R + 1) × Fin (2 * R + 1) × Phase M.k

/-- An integer clamped to `[-R, R]` and shifted to `[0, 2R]`. -/
def clampI (R : ℕ) (x : ℤ) : Fin (2 * R + 1) := ⟨min (x + R).toNat (2 * R), by omega⟩

/-- A natural number clamped to `[0, 2R]`. -/
def clampN (R n : ℕ) : Fin (2 * R + 1) := ⟨min n (2 * R), by omega⟩

theorem clampI_val {R : ℕ} {x : ℤ} (h : |x| ≤ R) : ((clampI R x).val : ℤ) - R = x := by
  rw [abs_le] at h
  simp only [clampI]
  omega

theorem clampN_val {R n : ℕ} (h : n ≤ R) : (clampN R n).val = n := by
  simp only [clampN]; omega

/-- The bounded image of a register. -/
def toFin (R : ℕ) (ρ : Reg M) : RegFin M R :=
  (ρ.st, fun τ => clampI R (ρ.x τ), fun τ => clampI R (ρ.j τ), clampN R ρ.nfl, clampN R ρ.nbuf,
    ρ.ph)

/-- The register of a bounded value. -/
def ofFin (R : ℕ) (v : RegFin M R) : Reg M where
  st := v.1
  x := fun τ => ((v.2.1 τ).val : ℤ) - R
  j := fun τ => ((v.2.2.1 τ).val : ℤ) - R
  nfl := v.2.2.2.1.val
  nbuf := v.2.2.2.2.1.val
  ph := v.2.2.2.2.2

theorem ofFin_toFin {R : ℕ} {ρ : Reg M} (h : Good M R ρ) : ofFin M R (toFin M R ρ) = ρ := by
  obtain ⟨hx, hj, hn, hb⟩ := h
  exact Reg.ext rfl (funext fun τ => clampI_val (hx τ)) (funext fun τ => clampI_val (hj τ))
    (clampN_val hn) (clampN_val hb) rfl

theorem card_regFin (R : ℕ) :
    (Fintype.card (RegFin M R) : ℝ) = (M.q + 1) * (2 * R + 1 : ℝ) ^ (2 * M.k + 4) * (2 * M.k + 2) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Phase.card]
  push_cast
  ring

/-- The register width `⌈log₂ |RegFin M R|⌉`. -/
def regBits (R : ℕ) : ℕ := Nat.clog 2 (Fintype.card (RegFin M R))

theorem exists_regEnc (R : ℕ) : ∃ e : RegFin M R → Fin (regBits M R) → Bool,
    Function.Injective e ∧ e (toFin M R (reg₀ M)) = fun _ => false :=
  exists_enc _ (Nat.le_pow_clog one_lt_two _)

/-- An injective encoding of bounded register values into `regBits M R` bits. -/
noncomputable def regEnc (R : ℕ) : RegFin M R → Fin (regBits M R) → Bool :=
  (exists_regEnc M R).choose

/-- Storing a register. -/
noncomputable def enc (R : ℕ) (ρ : Reg M) : Fin (regBits M R) → Bool := regEnc M R (toFin M R ρ)

/-- Reading a register. -/
noncomputable def dec (R : ℕ) (v : Fin (regBits M R) → Bool) : Reg M :=
  ofFin M R (Function.invFun (regEnc M R) v)

theorem dec_enc {R : ℕ} {ρ : Reg M} (h : Good M R ρ) : dec M R (enc M R ρ) = ρ := by
  have hinj : Function.Injective (regEnc M R) := (exists_regEnc M R).choose_spec.1
  rw [dec, enc, Function.leftInverse_invFun hinj, ofFin_toFin M h]

theorem enc_reg₀ (R : ℕ) : enc M R (reg₀ M) = fun _ => false := (exists_regEnc M R).choose_spec.2

/-- **The external-memory algorithm of Theorem EM**: the simulator `inner`, with internal steps
collapsed and the register stored in `regBits M (T₀ + 2)` bits. -/
noncomputable def emAlg (d B T₀ : ℕ) : Alg (Sym M) B (2 * M.k + 3) (regBits M (T₀ + 2)) :=
  collapse (inner M d B) (enc M (T₀ + 2)) (dec M (T₀ + 2))

/-- **The simulation as an external-memory run.** If `M` computes `v` from `w` within `T₀`
steps and `|w| = |v| = dB`, then `emAlg M d B T₀`, run on the input disk of `w`, halts with row `n`
of `v` at address `d + n`. Its I/O sequence is the first read followed by the I/Os of an event
word with at most `T₀ / B` shifts of every tape and exactly `d` flushes. -/
theorem em_core {d B T₀ : ℕ} (hB : 0 < B) (hd : 0 < d) {w v : List Bool}
    (hw : w.length = d * B) (hv : v.length = d * B) (hM : ComputesWithin M w v T₀) :
    ∃ ev : List (Letter M.k),
      HaltsWith (emAlg M d B T₀) (symAlph M) d w
        ((.read, hiS M 0, 0) :: ioWords M d (fun _ => -1) 0 ev) v ∧
      (∀ τ, B * cnt τ ev ≤ T₀) ∧ nflush ev = d := by
  obtain ⟨Th, hTh0, hTh, hout⟩ := (computesWithin_iff v T₀).1 hM
  have hout' : (run M w Th).outRev.length = d * B := by
    rw [← List.length_reverse, hout, hv]
  obtain ⟨ev, ios, D', hr, hios, hcnt, hfl, hrows⟩ :=
    simulate hB hd hw hTh hout' (T₀ + 2) (by omega)
  refine ⟨ev, ⟨D', ?_, fun n hn => by rw [hrows n hn, hout]⟩,
    fun τ => (hcnt τ).trans hTh0, hfl⟩
  have hinit : (initMem (symAlph M) : Mem (Sym M) B (2 * M.k + 3) (regBits M (T₀ + 2))) =
      ((fun _ _ => .inr 0 : Slots M B), enc M (T₀ + 2) (reg₀ M)) := by
    rw [enc_reg₀]; rfl
  rw [hinit, ← hios]
  exact MRuns.runs (fun ρ hρ => dec_enc M hρ) hr

end Register

/-! ## Counting -/

section Counting

variable {M : TM}

theorem ioWords_length_le' {d N : ℕ} (jv : Fin (M.k + 1) → ℤ) (n : ℕ) {ev : List (Letter M.k)}
    (hc : ∀ τ, cnt τ ev ≤ N) : (ioWords M d jv n ev).length ≤ (2 * M.k + 1) * N + nflush ev := by
  have h1 := ioWords_length_le (d := d) jv n ev
  have h2 : (∑ h : Fin M.k, cnt h.succ ev) ≤ M.k * N := by
    calc (∑ h : Fin M.k, cnt h.succ ev) ≤ ∑ _h : Fin M.k, N := Finset.sum_le_sum fun h _ => hc _
      _ = M.k * N := by simp
  have h3 := hc 0
  nlinarith

theorem length_le_of_cnt {k N : ℕ} {ev : List (Letter k)} (hc : ∀ τ, cnt τ ev ≤ N) :
    ev.length ≤ (k + 1) * N + nflush ev := by
  rw [length_eq_sum_cnt]
  have : (∑ τ, cnt τ ev) ≤ (k + 1) * N := by
    calc (∑ τ, cnt τ ev) ≤ ∑ _τ : Fin (k + 1), N := Finset.sum_le_sum fun τ _ => hc τ
      _ = (k + 1) * N := by simp
  omega

/-- Padding a list of length at most `N` to `N` entries is injective. -/
theorem pad_inj {α : Type*} {N : ℕ} {l l' : List α} (hl : l.length ≤ N) (hl' : l'.length ≤ N)
    (h : (fun i : Fin N => l[i.val]?) = fun i : Fin N => l'[i.val]?) : l = l' := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < N
  · exact congrFun h ⟨n, hn⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The words of length `L`. -/
def wordsOfLength (L : ℕ) : Finset (List Bool) := (Finset.univ : Finset (Fin L → Bool)).image List.ofFn

theorem mem_wordsOfLength {L : ℕ} {w : List Bool} : w ∈ wordsOfLength L ↔ w.length = L := by
  constructor
  · intro hw
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hw
    exact List.length_ofFn
  · intro hw
    subst hw
    exact Finset.mem_image.2 ⟨fun i => w[i.val], Finset.mem_univ _, List.ofFn_getElem⟩

theorem card_wordsOfLength (L : ℕ) : (wordsOfLength L).card = 2 ^ L := by
  rw [wordsOfLength, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

end Counting

/-! ## Theorem EM -/


/-- The I/O constant `c₁ = 4(k + 1)c + 2`. -/
noncomputable def emC1 (k : ℕ) (c : ℝ) : ℝ := 4 * (k + 1) * c + 2

/-- The entropy constant `c₂ = (2(k + 1)c + 1) log₂(2k + 4)`. -/
noncomputable def emC2 (k : ℕ) (c : ℝ) : ℝ := (2 * (k + 1) * c + 1) * Real.logb 2 (2 * k + 4)

/-- The register constant `γ = (2k + 4)(log₂(4c + 5) + 1) + log₂|Q| + log₂(2k + 2) + 1`, where
`|Q| = q + 1`. -/
noncomputable def emGamma (k q : ℕ) (c : ℝ) : ℝ :=
  (2 * k + 4) * (Real.logb 2 (4 * c + 5) + 1) + Real.logb 2 (q + 1) + Real.logb 2 (2 * k + 2) + 1

theorem emGamma_nonneg (k q : ℕ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ emGamma k q c := by
  unfold emGamma
  have h1 : 0 ≤ Real.logb 2 (4 * c + 5) := Real.logb_nonneg one_lt_two (by linarith)
  have h2 : 0 ≤ Real.logb 2 ((q : ℝ) + 1) := Real.logb_nonneg one_lt_two (by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith)
  have h3 : 0 ≤ Real.logb 2 (2 * (k : ℝ) + 2) := Real.logb_nonneg one_lt_two (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  positivity

/-- **The register bound**: `regBits M (T₀ + 2) ≤ γ log₂(2L)` when `T₀ ≤ c (L + 1)`. -/
theorem regBits_le (M : TM) {c : ℝ} (hc : 0 ≤ c) {L T₀ : ℕ} (hL : 1 ≤ L)
    (hT : (T₀ : ℝ) ≤ c * (L + 1)) :
    (regBits M (T₀ + 2) : ℝ) ≤ emGamma M.k M.q c * Real.logb 2 (2 * L) := by
  set n := Fintype.card (RegFin M (T₀ + 2)) with hn
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hk : (0 : ℝ) ≤ M.k := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ M.q := Nat.cast_nonneg _
  -- `log₂ (2L) = 1 + log₂ L ≥ 1`
  have hlogL : Real.logb 2 (2 * L) = 1 + Real.logb 2 L := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two]
  have hlogL0 : 0 ≤ Real.logb 2 (L : ℝ) := Real.logb_nonneg one_lt_two hL'
  -- `regBits ≤ log₂ n + 1`
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hr : (regBits M (T₀ + 2) : ℝ) ≤ Real.logb 2 n + 1 := by
    rcases Nat.lt_or_ge 1 n with h2 | h2
    · have h3 := Nat.pow_pred_clog_lt_self one_lt_two h2
      have h4 : ((Nat.clog 2 n).pred : ℝ) < Real.logb 2 n := by
        have := Real.logb_lt_logb one_lt_two (by positivity)
          (show ((2 ^ (Nat.clog 2 n).pred : ℕ) : ℝ) < n by exact_mod_cast h3)
        rwa [Nat.cast_pow, Real.logb_pow, Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two,
          mul_one] at this
      have h5 : (Nat.clog 2 n : ℝ) ≤ (Nat.clog 2 n).pred + 1 := by
        have : Nat.clog 2 n ≤ (Nat.clog 2 n).pred + 1 := by
          rw [Nat.pred_eq_sub_one]; omega
        exact_mod_cast this
      show (Nat.clog 2 n : ℝ) ≤ _
      linarith
    · have : n = 1 := le_antisymm h2 hn1
      rw [show regBits M (T₀ + 2) = 0 by
        show Nat.clog 2 n = 0
        rw [this]; exact Nat.clog_one_right 2]
      rw [this, Nat.cast_one, Real.logb_one]
      norm_num
  -- `log₂ n ≤ log₂(q+1) + (2k+4)(log₂(4c+5) + log₂ L) + log₂(2k+2)`
  have hX : (2 * ((T₀ + 2 : ℕ) : ℝ) + 1) ≤ (4 * c + 5) * L := by
    push_cast
    nlinarith
  have hX0 : (0 : ℝ) < 2 * ((T₀ + 2 : ℕ) : ℝ) + 1 := by positivity
  have hlogn : Real.logb 2 n ≤ Real.logb 2 (M.q + 1) +
      (2 * M.k + 4) * (Real.logb 2 (4 * c + 5) + Real.logb 2 L) + Real.logb 2 (2 * M.k + 2) := by
    have hcard : (n : ℝ) ≤ (M.q + 1) * ((4 * c + 5) * L) ^ (2 * M.k + 4) * (2 * M.k + 2) := by
      rw [hn, card_regFin]
      gcongr
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
    refine (Real.logb_le_logb_of_le one_lt_two hpos hcard).trans (le_of_eq ?_)
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), Real.logb_pow, Real.logb_mul (by positivity) (by positivity)]
    push_cast
    ring
  have ha : 0 ≤ Real.logb 2 (4 * c + 5) := Real.logb_nonneg one_lt_two (by linarith)
  have hb : 0 ≤ Real.logb 2 ((M.q : ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have he : 0 ≤ Real.logb 2 (2 * (M.k : ℝ) + 2) := Real.logb_nonneg one_lt_two (by linarith)
  unfold emGamma
  rw [hlogL]
  nlinarith [mul_nonneg ha hlogL0, mul_nonneg hb hlogL0, mul_nonneg he hlogL0,
    mul_nonneg hk hlogL0, mul_nonneg (mul_nonneg hk ha) hlogL0]

/-- **Obliviousness on a large subset, for any machine and any finite set of inputs.** Let every
word of a finite set `W` have length `dB`, and let `M` compute from it some output of length `dB`
within `T₀` steps. Then `emAlg M d B T₀` is oblivious on a subset `C ⊆ W` with
`|W| ≤ |C| (2k + 4)^((k + 1)⌊T₀/B⌋ + d)`: the I/O sequence of each run is determined by an event
word of length at most `(k + 1)⌊T₀/B⌋ + d` (`em_core`), and `C` is the largest fibre. -/
theorem em_oblivious (M : TM) {d B T₀ : ℕ} (hB : 0 < B) (hd : 0 < d) (W : Finset (List Bool))
    (hW : ∀ w ∈ W, w.length = d * B ∧
      ∃ v : List Bool, v.length = d * B ∧ ComputesWithin M w v T₀) :
    ∃ C ⊆ W, W.card ≤ C.card * (2 * M.k + 4) ^ ((M.k + 1) * (T₀ / B) + d) ∧
      ObliviousOn (emAlg M d B T₀) (symAlph M) d C := by
  have hcnt' : ∀ {ev : List (Letter M.k)}, (∀ τ, B * cnt τ ev ≤ T₀) → ∀ τ, cnt τ ev ≤ T₀ / B :=
    fun h τ => (Nat.le_div_iff_mul_le hB).2 (by rw [Nat.mul_comm]; exact h τ)
  set N := (M.k + 1) * (T₀ / B) + d
  have key : ∀ w ∈ W, ∃ ev : List (Letter M.k), ev.length ≤ N ∧
      ∃ D', Runs (emAlg M d B T₀) (initMem (symAlph M)) (inputDisk (symAlph M) d B w)
        ((.read, hiS M 0, 0) :: ioWords M d (fun _ => -1) 0 ev) D' := by
    intro w hw
    obtain ⟨hwl, v, hvl, hc⟩ := hW w hw
    obtain ⟨ev, ⟨D', hr, -⟩, hcnt, hfl⟩ := em_core M hB hd hwl hvl hc
    refine ⟨ev, ?_, D', hr⟩
    have := length_le_of_cnt (hcnt' hcnt)
    omega
  choose! evOf hevOf using key
  let φ : List Bool → Fin N → Option (Letter M.k) := fun w i => (evOf w)[i.val]?
  have hcod : (Finset.univ : Finset (Fin N → Option (Letter M.k))).card = (2 * M.k + 4) ^ N := by
    simp [Finset.card_univ, Fintype.card_option, Letter.card]
  -- the largest fibre of `φ`
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin N → Option (Letter M.k)))
    (fun z => (W.filter (fun w => φ w = z)).card) Finset.univ_nonempty
  refine ⟨W.filter (fun w => φ w = y), Finset.filter_subset _ _, ?_, ?_⟩
  · have hsum := Finset.card_eq_sum_card_fiberwise (s := W) (t := Finset.univ) (f := φ)
      (fun _ _ => Finset.mem_univ _)
    calc W.card = ∑ z ∈ Finset.univ, (W.filter (fun w => φ w = z)).card := hsum
      _ ≤ ∑ _z ∈ (Finset.univ : Finset (Fin N → Option (Letter M.k))),
            (W.filter (fun w => φ w = y)).card :=
          Finset.sum_le_sum fun z _ => hy z (Finset.mem_univ _)
      _ = _ := by rw [Finset.sum_const, hcod, smul_eq_mul, Nat.mul_comm]
  · by_cases hne : (W.filter (fun w => φ w = y)).Nonempty
    · obtain ⟨w₀, hw₀⟩ := hne
      refine ⟨(.read, hiS M 0, 0) :: ioWords M d (fun _ => -1) 0 (evOf w₀), fun w hw => ?_⟩
      have h1 := Finset.mem_filter.1 hw
      have h0 := Finset.mem_filter.1 hw₀
      have heq : evOf w = evOf w₀ :=
        pad_inj (hevOf w h1.1).1 (hevOf w₀ h0.1).1 (h1.2.trans h0.2.symm)
      rw [← heq]
      exact (hevOf w h1.1).2
    · exact ⟨[], fun w hw => absurd ⟨w, hw⟩ hne⟩

/-- **Theorem EM, exact form.** Let `M` transpose at dimension `d ≥ 1` within `T₀` steps, and put
`B = d b(d)`, `L = d² b(d)`. The algorithm `emAlg M d B T₀` (`2k + 3` slots, `regBits M (T₀ + 2)`
register bits) is correct on every input with at most `1 + (2k + 1)⌊T₀/B⌋ + d` I/Os, and it is
oblivious on a set `C` of input words with `2^L ≤ |C| (2k + 4)^((k + 1)⌊T₀/B⌋ + d)`. -/
theorem theoremEM_nat (M : TM) {d T₀ : ℕ} (hd : 1 ≤ d)
    (hM : ∀ X : Transpose.Matrix, ComputesWithin M (encode d (entryBits d) X)
      (encode d (entryBits d) (transpose X)) T₀) :
    (∀ X : Transpose.Matrix, ∃ ios,
      HaltsWith (emAlg M d (d * entryBits d) T₀) (symAlph M) d (encode d (entryBits d) X) ios
        (encode d (entryBits d) (transpose X)) ∧
      ios.length ≤ 1 + (2 * M.k + 1) * (T₀ / (d * entryBits d)) + d) ∧
    ∃ C : Finset (List Bool), (∀ w ∈ C, w.length = inputLength d) ∧
      2 ^ inputLength d ≤ C.card * (2 * M.k + 4) ^ ((M.k + 1) * (T₀ / (d * entryBits d)) + d) ∧
      ObliviousOn (emAlg M d (d * entryBits d) T₀) (symAlph M) d C := by
  set b := entryBits d with hb_def
  set B := d * b with hB_def
  have hb : 1 ≤ b := Nat.succ_le_succ (Nat.zero_le _)
  have hB : 0 < B := Nat.mul_pos hd hb
  have hLB : inputLength d = d * B := by simp only [inputLength, hB_def, hb_def, Nat.mul_assoc]
  have hlen : ∀ X : Transpose.Matrix, (encode d b X).length = d * B := fun X => by
    rw [length_encode, ← hLB]; rfl
  refine ⟨fun X => ?_, ?_⟩
  · obtain ⟨ev, hhalt, hcnt, hfl⟩ := em_core M hB hd (hlen X) (hlen _) (hM X)
    refine ⟨_, hhalt, ?_⟩
    have := ioWords_length_le' (d := d) (fun _ => -1) 0
      (fun τ => (Nat.le_div_iff_mul_le hB).2 (by rw [Nat.mul_comm]; exact hcnt τ))
    rw [List.length_cons]
    omega
  · obtain ⟨C, hCW, hcard, hobl⟩ := em_oblivious M hB hd (wordsOfLength (inputLength d))
      (fun w hw => by
        have hw' : w ∈ matrixInputs d b := by
          rw [matrixInputs_eq]
          exact mem_wordsOfLength.1 hw
        obtain ⟨X, rfl⟩ := hw'
        exact ⟨hlen X, _, hlen _, hM X⟩)
    rw [card_wordsOfLength] at hcard
    exact ⟨C, fun w hw => mem_wordsOfLength.1 (hCW hw), hcard, hobl⟩

/-- `⌊T₀ / B⌋ ≤ cd + c` when `T₀ ≤ c (dB + 1)`. -/
theorem div_le_mul_add {c : ℝ} (hc : 0 ≤ c) {d B T₀ : ℕ} (hB : 1 ≤ B)
    (hT : (T₀ : ℝ) ≤ c * (d * B + 1)) : ((T₀ / B : ℕ) : ℝ) ≤ c * d + c := by
  have h1 : ((T₀ / B : ℕ) : ℝ) * B ≤ T₀ := by exact_mod_cast Nat.div_mul_le_self T₀ B
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have h3 : c ≤ c * B := le_mul_of_one_le_right hc hB'
  have h2 : ((T₀ / B : ℕ) : ℝ) * B ≤ (c * d + c) * B := by nlinarith
  exact le_of_mul_le_mul_right h2 (by linarith)

/-- `⌊T₀ / B⌋ ≤ 2cd` when `T₀ ≤ c (dB + 1)`. -/
theorem div_le_two_mul {c : ℝ} (hc : 0 ≤ c) {d B T₀ : ℕ} (hd : 1 ≤ d) (hB : 1 ≤ B)
    (hT : (T₀ : ℝ) ≤ c * (d * B + 1)) : ((T₀ / B : ℕ) : ℝ) ≤ 2 * c * d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have := div_le_mul_add hc hB hT
  nlinarith

/-- The time bound `T₀ = ⌊c (L + 1)⌋` in the form of `div_le_mul_add`: `T₀ ≤ c (d B + 1)` for the
block size `B = d b(d)`. -/
theorem floor_le_mul_block {c : ℝ} (hc : 0 ≤ c) (d : ℕ) :
    (⌊c * ((inputLength d : ℝ) + 1)⌋₊ : ℝ) ≤ c * (d * (d * entryBits d : ℕ) + 1) := by
  have := Nat.floor_le (show 0 ≤ c * ((inputLength d : ℝ) + 1) by positivity)
  have e : (inputLength d : ℝ) = d * ((d * entryBits d : ℕ) : ℝ) := by
    simp only [inputLength, Nat.mul_assoc]; push_cast; ring
  exact this.trans (le_of_eq (by rw [e]))

/-- **Theorem EM, real form**, for any real `s` bounding the number `⌊T₀/B⌋` of shifts per tape,
`T₀ = ⌊c (L + 1)⌋`: at most `1 + (2k + 1)s + d` I/Os, and obliviousness on at least
`2^(L - ((k + 1)s + d) log₂(2k + 4))` input words. -/
theorem theoremEM_real (M : TM) {c : ℝ} (hc : 0 ≤ c) {d : ℕ} (hd : 1 ≤ d)
    (hM : TransposesAt M d c) {s : ℝ}
    (hs : ((⌊c * ((inputLength d : ℝ) + 1)⌋₊ / (d * entryBits d) : ℕ) : ℝ) ≤ s) :
    ∃ (r : ℕ) (A : Alg (Sym M) (d * entryBits d) (2 * M.k + 3) r),
      (r : ℝ) ≤ emGamma M.k M.q c * Real.logb 2 (2 * inputLength d) ∧
      (∀ X : Transpose.Matrix, ∃ ios,
        HaltsWith A (symAlph M) d (encode d (entryBits d) X) ios
          (encode d (entryBits d) (transpose X)) ∧ (ios.length : ℝ) ≤ 1 + (2 * M.k + 1) * s + d) ∧
      ∃ C : Finset (List Bool), (∀ w ∈ C, w.length = inputLength d) ∧
        (2 : ℝ) ^ ((inputLength d : ℝ) - ((M.k + 1) * s + d) * Real.logb 2 (2 * M.k + 4)) ≤
          C.card ∧
        ObliviousOn A (symAlph M) d C := by
  obtain ⟨hcorr, C, hClen, hCcard, hobl⟩ :=
    theoremEM_nat M (T₀ := ⌊c * ((inputLength d : ℝ) + 1)⌋₊) hd hM
  set T₀ := ⌊c * ((inputLength d : ℝ) + 1)⌋₊ with hT₀_def
  set B := d * entryBits d with hB_def
  have hb := one_le_entryBits d
  have hB : 1 ≤ B := by simpa using Nat.mul_le_mul hd hb
  have hLB : inputLength d = d * B := by simp only [inputLength, hB_def, Nat.mul_assoc]
  have hL : 1 ≤ inputLength d := by rw [hLB]; simpa using Nat.mul_le_mul hd hB
  have hT : (T₀ : ℝ) ≤ c * (inputLength d + 1) := Nat.floor_le (by positivity)
  have hk : (0 : ℝ) ≤ M.k := Nat.cast_nonneg _
  refine ⟨_, emAlg M d B T₀, regBits_le M hc hL hT, fun X => ?_, C, hClen, ?_, hobl⟩
  · obtain ⟨ios, hh, hlen⟩ := hcorr X
    refine ⟨ios, hh, ?_⟩
    have h1 : (ios.length : ℝ) ≤ 1 + (2 * M.k + 1) * ((T₀ / B : ℕ) : ℝ) + d := by
      exact_mod_cast hlen
    have h2 : (2 * (M.k : ℝ) + 1) * ((T₀ / B : ℕ) : ℝ) ≤ (2 * M.k + 1) * s :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    linarith
  · set N := (M.k + 1) * (T₀ / B) + d
    have hN : (N : ℝ) ≤ (M.k + 1) * s + d := by
      have : ((M.k : ℝ) + 1) * ((T₀ / B : ℕ) : ℝ) ≤ (M.k + 1) * s :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      simp only [N]
      push_cast
      linarith
    have hbase : (1 : ℝ) ≤ 2 * M.k + 4 := by linarith
    have hpos : (0 : ℝ) < 2 * M.k + 4 := by linarith
    have hcard : (2 : ℝ) ^ inputLength d ≤ C.card * (2 * M.k + 4 : ℝ) ^ N := by
      exact_mod_cast hCcard
    have h1 : (2 : ℝ) ^ ((inputLength d : ℝ) - ((M.k + 1) * s + d) * Real.logb 2 (2 * M.k + 4)) =
        2 ^ inputLength d / (2 * M.k + 4 : ℝ) ^ ((M.k + 1) * s + d) := by
      rw [Real.rpow_sub two_pos, Real.rpow_natCast]
      congr 1
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb two_pos (by norm_num) hpos]
    have h2 : (2 * M.k + 4 : ℝ) ^ N ≤ (2 * M.k + 4 : ℝ) ^ ((M.k + 1) * s + d) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hbase hN
    rw [h1, div_le_iff₀ (by positivity)]
    calc (2 : ℝ) ^ inputLength d ≤ C.card * (2 * M.k + 4 : ℝ) ^ N := hcard
      _ ≤ C.card * (2 * M.k + 4 : ℝ) ^ ((M.k + 1) * s + d) := by gcongr

/-- **Theorem EM** (Theorem 6.4). Let `M` transpose at dimension `d ≥ 1` within `c (L + 1)` steps,
`c ≥ 0`. Then there is an external-memory algorithm over `Σ_M` with block size `d b(d)`, `2k + 3`
slots and a register of at most `γ log₂(2L)` bits that (i) is correct on every input, with at most
`c₁ d` I/Os, and (ii) is oblivious on a set of at least `2^(L - c₂ d)` input words. -/
theorem theoremEM (M : TM) {c : ℝ} (hc : 0 ≤ c) {d : ℕ} (hd : 1 ≤ d) (hM : TransposesAt M d c) :
    ∃ (r : ℕ) (A : Alg (Sym M) (d * entryBits d) (2 * M.k + 3) r),
      (r : ℝ) ≤ emGamma M.k M.q c * Real.logb 2 (2 * inputLength d) ∧
      (∀ X : Transpose.Matrix, ∃ ios,
        HaltsWith A (symAlph M) d (encode d (entryBits d) X) ios
          (encode d (entryBits d) (transpose X)) ∧ (ios.length : ℝ) ≤ emC1 M.k c * d) ∧
      ∃ C : Finset (List Bool), (∀ w ∈ C, w.length = inputLength d) ∧
        (2 : ℝ) ^ ((inputLength d : ℝ) - emC2 M.k c * d) ≤ C.card ∧
        ObliviousOn A (symAlph M) d C := by
  have hB : 1 ≤ d * entryBits d := by simpa using Nat.mul_le_mul hd (one_le_entryBits d)
  have hT := floor_le_mul_block hc d
  obtain ⟨r, A, hr, hcorr, C, hClen, hCcard, hobl⟩ :=
    theoremEM_real M hc hd hM (div_le_two_mul hc hd hB hT)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (0 : ℝ) ≤ M.k := Nat.cast_nonneg _
  refine ⟨r, A, hr, fun X => ?_, C, hClen, ?_, hobl⟩
  · obtain ⟨ios, hh, hlen⟩ := hcorr X
    refine ⟨ios, hh, ?_⟩
    have h3 : 0 ≤ c * d := by positivity
    unfold emC1
    nlinarith
  · convert hCcard using 3
    unfold emC2
    ring

/-- **Theorem EM with sharper constants**: at most `((2k + 1)c + 1)d + (2k + 1)c + 1` I/Os, and
obliviousness on at least `2^(L - (((k + 1)c + 1)d + (k + 1)c) log₂(2k + 4))` input words; for
large `d` this is `c₁ ≈ (2k + 1)c + 1` and `c₂ ≈ ((k + 1)c + 1) log₂(2k + 4)`. -/
theorem theoremEM_sharp (M : TM) {c : ℝ} (hc : 0 ≤ c) {d : ℕ} (hd : 1 ≤ d)
    (hM : TransposesAt M d c) :
    ∃ (r : ℕ) (A : Alg (Sym M) (d * entryBits d) (2 * M.k + 3) r),
      (r : ℝ) ≤ emGamma M.k M.q c * Real.logb 2 (2 * inputLength d) ∧
      (∀ X : Transpose.Matrix, ∃ ios,
        HaltsWith A (symAlph M) d (encode d (entryBits d) X) ios
          (encode d (entryBits d) (transpose X)) ∧
        (ios.length : ℝ) ≤ ((2 * M.k + 1) * c + 1) * d + (2 * M.k + 1) * c + 1) ∧
      ∃ C : Finset (List Bool), (∀ w ∈ C, w.length = inputLength d) ∧
        (2 : ℝ) ^ ((inputLength d : ℝ) -
          (((M.k + 1) * c + 1) * d + (M.k + 1) * c) * Real.logb 2 (2 * M.k + 4)) ≤ C.card ∧
        ObliviousOn A (symAlph M) d C := by
  have hB : 1 ≤ d * entryBits d := by simpa using Nat.mul_le_mul hd (one_le_entryBits d)
  have hT := floor_le_mul_block hc d
  obtain ⟨r, A, hr, hcorr, C, hClen, hCcard, hobl⟩ :=
    theoremEM_real M hc hd hM (div_le_mul_add hc hB hT)
  refine ⟨r, A, hr, fun X => ?_, C, hClen, ?_, hobl⟩
  · obtain ⟨ios, hh, hlen⟩ := hcorr X
    exact ⟨ios, hh, by linarith⟩
  · convert hCcard using 3
    ring

/-! ## Corollary EM -/

/-- **The hypothesis of Corollary EM**: for every finite alphabet with `0`, `1` and a blank, and
all constants `m ≥ 1`, `γ ≥ 0`, `A ≥ 0`, from some dimension `d₀` on, every external-memory
algorithm with block size `d b(d)`, `m` slots and at most `γ log₂(2L)` register bits that is
correct on every word of a set `C` of at least `2^(L - Ad)` input words and oblivious on `C`
performs more than `Ad` I/Os on the words of `C`. -/
def EMLowerBound : Prop :=
  ∀ (Λ : Type) [Fintype Λ] (al : Alphabet Λ) (m : ℕ) (γ A : ℝ), 1 ≤ m → 0 ≤ γ → 0 ≤ A →
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (r : ℕ) (alg : Alg Λ (d * entryBits d) m r),
      (r : ℝ) ≤ γ * Real.logb 2 (2 * inputLength d) →
      ∀ C : Finset (List Bool), (∀ w ∈ C, w.length = inputLength d) →
        (2 : ℝ) ^ ((inputLength d : ℝ) - A * d) ≤ C.card →
        (∀ w ∈ C, CorrectAt alg al w) →
        ∀ ios : List (IO m),
          (∀ w ∈ C, ∃ D', Runs alg (initMem al) (inputDisk al d (d * entryBits d) w) ios D') →
          A * d < ios.length

/-- A weaker hypothesis: the lower bound of `EMLowerBound` at **one** dimension `d ≥ 1` for each
alphabet and constants, instead of at all large dimensions. -/
def EMLowerBoundSome : Prop :=
  ∀ (Λ : Type) [Fintype Λ] (al : Alphabet Λ) (m : ℕ) (γ A : ℝ), 1 ≤ m → 0 ≤ γ → 0 ≤ A →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ (r : ℕ) (alg : Alg Λ (d * entryBits d) m r),
      (r : ℝ) ≤ γ * Real.logb 2 (2 * inputLength d) →
      ∀ C : Finset (List Bool), (∀ w ∈ C, w.length = inputLength d) →
        (2 : ℝ) ^ ((inputLength d : ℝ) - A * d) ≤ C.card →
        (∀ w ∈ C, CorrectAt alg al w) →
        ∀ ios : List (IO m),
          (∀ w ∈ C, ∃ D', Runs alg (initMem al) (inputDisk al d (d * entryBits d) w) ios D') →
          A * d < ios.length

theorem EMLowerBound.some (h : EMLowerBound) : EMLowerBoundSome := by
  intro Λ _ al m γ A hm hγ hA
  obtain ⟨d₀, hd₀⟩ := h Λ al m γ A hm hγ hA
  exact ⟨max d₀ 1, le_max_right _ _, hd₀ _ (le_max_left _ _)⟩

/-- **Corollary EM, strengthened**: the I/O lower bound at one dimension for each alphabet and
constants already refutes (T). -/
theorem corollaryEM_some (h : EMLowerBoundSome) : ¬ LinearTimeTransposable := by
  rintro ⟨M, c, hM⟩
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hc1 : 0 ≤ emC1 M.k c := by unfold emC1; positivity
  obtain ⟨d, hd, hd₀⟩ := h (Sym M) (symAlph M) (2 * M.k + 3) (emGamma M.k M.q c)
    (max (emC1 M.k c) (emC2 M.k c)) (by omega) (emGamma_nonneg _ _ hc)
    (le_max_of_le_left hc1)
  obtain ⟨r, alg, hr, hcorr, C, hClen, hCcard, ios, hios⟩ :=
    theoremEM M hc hd (transposesAt_of_transposesWithin hM hd)
  have hcard : (2 : ℝ) ^ ((inputLength d : ℝ) - max (emC1 M.k c) (emC2 M.k c) * d) ≤ C.card := by
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hCcard
    have : emC2 M.k c * d ≤ max (emC1 M.k c) (emC2 M.k c) * d :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg d)
    linarith
  have hcorrect : ∀ w ∈ C, CorrectAt alg (symAlph M) w := by
    intro w _ X hX
    subst hX
    obtain ⟨ios', hh, -⟩ := hcorr X
    exact ⟨ios', hh⟩
  have hlt := hd₀ r alg hr C hClen hcard hcorrect ios hios
  -- a word of `C` and its run
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < C.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  obtain ⟨w, hw⟩ := hCne
  have hw' : w ∈ matrixInputs d (entryBits d) := by
    rw [matrixInputs_eq]; exact hClen w hw
  obtain ⟨X, rfl⟩ := hw'
  obtain ⟨ios', ⟨D', hrun, -⟩, hlen⟩ := hcorr X
  obtain ⟨D'', hrun'⟩ := hios _ hw
  obtain ⟨rfl, -⟩ := Runs.det hrun' hrun
  have : emC1 M.k c * d ≤ max (emC1 M.k c) (emC2 M.k c) * d :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg d)
  linarith

/-- **Corollary EM** (Corollary 6.5). An indivisibility-free I/O lower bound of order `ω(d)` for
oblivious external-memory transposition on large sets refutes (T). -/
theorem corollaryEM (h : EMLowerBound) : ¬ LinearTimeTransposable :=
  corollaryEM_some h.some

end MergeDepth.EM
