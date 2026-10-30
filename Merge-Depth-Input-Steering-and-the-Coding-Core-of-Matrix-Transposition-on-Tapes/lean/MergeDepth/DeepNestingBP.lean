import MergeDepth.DeepNestingLabels

/-!
# Lemmas 7.7–7.9 and Theorem BP for the walk pair (paper 11, Section 7)

The model of `BlockPairsModel`, `BlockPairsWitness` and `BlockPairsBlindness` works with explicit
families, turn times and potentials in one period. The files `DeepNestingWalk`, `DeepNestingHops`
and `DeepNestingLabels` identify them with the walk pair `x₁ = U(s₀, m, 1)`, `x₂ = x₁(· + ξ)`:
`periodTurns` are the turns of `U` (`isTurnZ_dnpWalk_iff`), the families are hops of the classes
(`family_inHopClass`), every class has `4Λ` hops per period and `4rΛ = n_h/(2N)` on the `r`-fold cover
(`levelCount_eq`, `card_coverClass`), the model's potentials are the potentials of the block labels
(`IsBlockLabel.potentialOf_eq`) and its errors are the errors of the block-pair label
(`hopError_blockPairLabel`), and `θ`-service on any cover implies the model's service on the witness
hops (`ThetaServes.servedOnWitness`). This file states the results for the walk pair.

* `InFamily` (family `f` of the class `(h, k)`, in every period, in real time), `IsBlind` (no turn of
  the other head in `(p, u]`; `isBlind_iff_blindHop`), `familyPerPeriod` (its hops with later endpoint
  in `[0, P)`; `card_familyPerPeriod`), `HalfBlindPair` (`halfBlindPair_iff`: the model's
  `HalfBlind`), `nonHalfBlindPair` (`nonHalfBlindPair_eq`).
* **Lemma 7.7**: `familyPerPeriod_subset_class` and `class_card_le_family` (a),
  `hopError_of_inFamily_blind` (b), `familyBlindErr_le_of_thetaServes` (c).
* **Lemma 7.8**: `sum_nonHalfBlindPair_le`, `prob_many_nonHalfBlindPair_le`.
* **Lemma 7.9**: `witnesses_unserved_pair`, with `unservedLevelsPair` (the levels not doubly
  `θ₀`-served on the `r`-fold cover).
* **Theorem BP**: `theoremBP_pair`, with `doublyServedLevelsPair`; Conjecture S is its only hypothesis.

The proofs never use `q ∣ r`: it is needed only for the block-pair label to be a label on the cover
(`blockPairLabel_add_mul`); with the lifted label the statements hold on every cover.
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-! ### Families, blindness and half-blindness for the walk pair -/

/-- The hop `(p, u)` (in real time) belongs to **family `f` of the class `(h, k)`** of the walk pair:
in the time of head `h`, and in some period, it is a hop of `family s0 m k f` (Definition 7.6). -/
def InFamily (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k f : ℕ) (p u : ℤ) : Prop :=
  ∃ n : ℤ, (p + headShift ξ h - n * dnpPeriod s0 m, u + headShift ξ h - n * dnpPeriod s0 m) ∈
    family s0 m k f

/-- A hop `(p, u)` of head `h` is **blind**: its half-open interval `(p, u]` contains no turn of the
other head. -/
def IsBlind (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u : ℤ) : Prop :=
  ∀ t, p < t → t ≤ u → ¬ IsTurnZ (headWalk s0 m ξ (!h)) t

open Classical in
/-- The hops of family `f` of the class `(h, k)` with later endpoint in `[0, P)`. -/
noncomputable def familyPerPeriod (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k f : ℕ) : Finset (ℤ × ℤ) :=
  (coverHops s0 m ξ 1 h).filter fun η => InFamily s0 m ξ h k f η.1 η.2

open Classical in
/-- Family `f` of the class `(h, k)` is **half-blind** at `ξ`: at least half of its hops with later
endpoint in `[0, P)` are blind (Definition 7.6). -/
def HalfBlindPair (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k f : ℕ) : Prop :=
  (familyPerPeriod s0 m ξ h k f).card ≤
    2 * ((familyPerPeriod s0 m ξ h k f).filter fun η => IsBlind s0 m ξ h η.1 η.2).card

open Classical in
/-- The triples `(h, k, f)` with `k ∈ ℱ_ε` whose family is not half-blind at `ξ`. -/
noncomputable def nonHalfBlindPair (s0 m : ℕ) (ε : ℝ) (ξ : ℕ) : Finset (Bool × ℕ × ℕ) :=
  ((Finset.univ : Finset Bool) ×ˢ (fineZone m ε ×ˢ range 4)).filter
    fun x => ¬ HalfBlindPair s0 m ξ x.1 x.2.1 x.2.2

theorem isTurnZ_headWalk_iff_dnp (s0 m : ℕ) (ξ : ℤ) (h : Bool) (t : ℤ) :
    IsTurnZ (headWalk s0 m ξ h) t ↔ IsTurnZ (dnpWalk s0 m) (t + headShift ξ h) := by
  unfold IsTurnZ headWalk
  rw [show t + 1 + headShift ξ h = t + headShift ξ h + 1 by ring,
    show t - 1 + headShift ξ h = t + headShift ξ h - 1 by ring]

/-- **Blindness is the model's `BlindHop`** in the head's own time. -/
theorem isBlind_iff_blindHop {s0 m : ℕ} (hms : m ≤ s0) (ξ : ℤ) (h : Bool) (p u : ℤ) :
    IsBlind s0 m ξ h p u ↔ BlindHop s0 m ξ h (p + headShift ξ h) (u + headShift ξ h) := by
  unfold IsBlind BlindHop TurnFree
  cases h
  · simp only [Bool.not_false, headShift, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hb t ht hmem
      rw [mem_Ioc] at ht
      apply hb (t - ξ) (by omega) (by omega)
      rw [isTurnZ_headWalk_iff_dnp, isTurnZ_dnpWalk_iff hms]
      simpa [headShift, sub_eq_add_neg] using hmem
    · intro hb t h1 h2 hturn
      rw [isTurnZ_headWalk_iff_dnp, isTurnZ_dnpWalk_iff hms] at hturn
      apply hb (t + ξ) (mem_Ioc.mpr ⟨by omega, by omega⟩)
      simpa [headShift] using hturn
  · simp only [Bool.not_true, headShift, ↓reduceIte, add_zero]
    constructor
    · intro hb t ht hmem
      rw [mem_Ioc] at ht
      apply hb t ht.1 ht.2
      rw [isTurnZ_headWalk_iff_dnp, isTurnZ_dnpWalk_iff hms]
      simpa [headShift] using hmem
    · intro hb t h1 h2 hturn
      rw [isTurnZ_headWalk_iff_dnp, isTurnZ_dnpWalk_iff hms] at hturn
      exact hb t (mem_Ioc.mpr ⟨h1, h2⟩) (by simpa [headShift] using hturn)

theorem isTurnZ_headWalk_add_mul_period (s0 m : ℕ) (ξ : ℤ) (h : Bool) (t n : ℤ) :
    IsTurnZ (headWalk s0 m ξ h) (t + n * dnpPeriod s0 m) ↔ IsTurnZ (headWalk s0 m ξ h) t := by
  unfold IsTurnZ headWalk
  rw [show t + n * dnpPeriod s0 m + 1 + headShift ξ h = (t + 1 + headShift ξ h) + n * dnpPeriod s0 m by
    ring, show t + n * dnpPeriod s0 m + headShift ξ h = (t + headShift ξ h) + n * dnpPeriod s0 m by ring,
    show t + n * dnpPeriod s0 m - 1 + headShift ξ h = (t - 1 + headShift ξ h) + n * dnpPeriod s0 m by
    ring, dnpWalk_add_mul_period, dnpWalk_add_mul_period, dnpWalk_add_mul_period]

theorem isBlind_add_mul_period (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u n : ℤ) :
    IsBlind s0 m ξ h (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) ↔ IsBlind s0 m ξ h p u := by
  unfold IsBlind
  constructor
  · intro hb t h1 h2
    have := hb (t + n * dnpPeriod s0 m) (by linarith) (by linarith)
    rwa [isTurnZ_headWalk_add_mul_period] at this
  · intro hb t h1 h2
    have := hb (t - n * dnpPeriod s0 m) (by linarith) (by linarith)
    rwa [← isTurnZ_headWalk_add_mul_period s0 m ξ (!h) (t - n * dnpPeriod s0 m) n, sub_add_cancel] at this

theorem inFamily_add_mul_period (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k f : ℕ) (p u n : ℤ) :
    InFamily s0 m ξ h k f (p + n * dnpPeriod s0 m) (u + n * dnpPeriod s0 m) ↔
      InFamily s0 m ξ h k f p u := by
  unfold InFamily
  constructor
  · rintro ⟨n', hn'⟩
    exact ⟨n' - n, by convert hn' using 2 <;> ring⟩
  · rintro ⟨n', hn'⟩
    exact ⟨n' + n, by convert hn' using 2 <;> ring⟩

/-- Counting the hops of a family per period: for a `P`-periodic property `R`, the hops of family `f`
of the class `(h, k)` with later endpoint in `[0, P)` that satisfy `R` correspond to the hops of the
explicit `family s0 m k f` that satisfy `R` in real time. -/
theorem card_familyPerPeriod_filter {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m)
    (hf : f < 4) (ξ : ℤ) (h : Bool) (R : ℤ → ℤ → Prop) [DecidableRel R]
    (hR : ∀ p u, R (p + dnpPeriod s0 m) (u + dnpPeriod s0 m) ↔ R p u) :
    ((familyPerPeriod s0 m ξ h k f).filter fun η => R η.1 η.2).card =
      ((family s0 m k f).filter fun η => R (η.1 - headShift ξ h) (η.2 - headShift ξ h)).card := by
  classical
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  set c := headShift ξ h with hcdef
  set hp := headPrev s0 m ξ h
  set g : ℤ → ℕ := fun u => if InFamily s0 m ξ h k f (hp u) u ∧ R (hp u) u then 1 else 0 with hg
  have hgper : ∀ u, g (u + dnpPeriod s0 m) = g u := by
    intro u
    have h1 : hp (u + dnpPeriod s0 m) = hp u + dnpPeriod s0 m := by
      have := headPrev_add_mul_period s0 m ξ h u 1; rwa [one_mul] at this
    have h2 := inFamily_add_mul_period s0 m ξ h k f (hp u) u 1
    rw [one_mul] at h2
    have h3 := hR (hp u) u
    simp only [hg]
    rw [h1]
    by_cases hc : InFamily s0 m ξ h k f (hp u) u ∧ R (hp u) u
    · rw [ite_eq_left ⟨h2.2 hc.1, h3.2 hc.2⟩, ite_eq_left hc]
    · rw [ite_eq_right (fun h' => hc ⟨h2.1 h'.1, h3.1 h'.2⟩), ite_eq_right hc]
  -- the left side counts the later endpoints in `[0, P)`
  have hL : ((familyPerPeriod s0 m ξ h k f).filter fun η => R η.1 η.2).card =
      ∑ u ∈ Ico 0 (dnpPeriod s0 m : ℤ), g u := by
    unfold familyPerPeriod
    rw [Finset.filter_filter, coverHops_eq_image, Finset.filter_image,
      Finset.card_image_of_injective _ (fun a b hab => by
        simp only [Prod.mk.injEq] at hab; exact hab.2), Finset.card_filter]
    simp only [Nat.cast_one, one_mul, hg]
    rfl
  rw [hL, ← sum_Ico_periodic hP hgper (-c)]
  -- the window `[-c, -c + P)`
  simp only [hg]
  rw [← Finset.card_filter]
  symm
  refine Finset.card_nbij (fun η => η.2 - c) ?_ ?_ ?_
  · intro η hη
    simp only [coe_filter, Set.mem_ofPred_eq] at hη ⊢
    obtain ⟨hη, hR'⟩ := hη
    have hcl := family_inHopClass hms hk1 hkm hf hη ξ h 0
    simp only [zero_mul, add_zero] at hcl
    have hprev : hp (η.2 - c) = η.1 - c := hcl.1.eq_headPrev.symm
    have hsnd := family_snd_mem hms hk1 hkm hη
    refine ⟨mem_Ico.mpr ⟨by linarith, by linarith⟩, ⟨0, ?_⟩, ?_⟩
    · rw [hprev, hcdef]; simpa using hη
    · rw [hprev]; exact hR'
  · intro η₁ h₁ η₂ h₂ he
    simp only [coe_filter, Set.mem_ofPred_eq] at h₁ h₂ he
    have e1 := (family_spec hms hk1 hkm hf h₁.1 0).1
    have e2 := (family_spec hms hk1 hkm hf h₂.1 0).1
    simp only [zero_mul, add_zero] at e1 e2
    have h2 : η₁.2 = η₂.2 := by linarith
    rw [h2] at e1
    exact Prod.ext (e1.eq_of_snd e2) h2
  · intro u hu
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hu
    obtain ⟨⟨hu1, hu2⟩, ⟨n, hn⟩, hRu⟩ := hu
    have hsnd := family_snd_mem hms hk1 hkm hn
    simp only at hsnd
    have hn0 : n = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : n * (dnpPeriod s0 m : ℤ) ≤ -(dnpPeriod s0 m : ℤ) := by nlinarith
        linarith
      · have : (dnpPeriod s0 m : ℤ) ≤ n * (dnpPeriod s0 m : ℤ) := by nlinarith
        linarith
    subst hn0
    simp only [zero_mul, sub_zero] at hn
    refine ⟨(hp u + c, u + c), ?_, by simp⟩
    simp only [coe_filter, Set.mem_ofPred_eq, add_sub_cancel_right]
    exact ⟨hn, hRu⟩

theorem card_familyPerPeriod {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m)
    (hf : f < 4) (ξ : ℤ) (h : Bool) :
    (familyPerPeriod s0 m ξ h k f).card = (family s0 m k f).card := by
  have := card_familyPerPeriod_filter hms hk1 hkm hf ξ h (fun _ _ => True) (fun _ _ => Iff.rfl)
  simpa using this

/-- **Half-blindness of the walk pair is the model's `HalfBlind`.** -/
theorem halfBlindPair_iff {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4)
    (ξ : ℤ) (h : Bool) : HalfBlindPair s0 m ξ h k f ↔ HalfBlind s0 m ξ h k f := by
  classical
  unfold HalfBlindPair HalfBlind
  rw [card_familyPerPeriod hms hk1 hkm hf ξ h,
    card_familyPerPeriod_filter hms hk1 hkm hf ξ h (fun p u => IsBlind s0 m ξ h p u)
      (fun p u => by simpa using isBlind_add_mul_period s0 m ξ h p u 1)]
  have : ((family s0 m k f).filter fun η => IsBlind s0 m ξ h (η.1 - headShift ξ h) (η.2 - headShift ξ h)) =
      (family s0 m k f).filter fun η => BlindHop s0 m ξ h η.1 η.2 := by
    refine Finset.filter_congr fun η _ => ?_
    rw [isBlind_iff_blindHop hms, sub_add_cancel, sub_add_cancel]
  rw [this]

/-- The non-half-blind triples of the walk pair are those of the model. -/
theorem nonHalfBlindPair_eq {s0 m : ℕ} {ε : ℝ} (hms : m ≤ s0) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8)
    (hεm : 4 ≤ ε * m) (ξ : ℕ) : nonHalfBlindPair s0 m ε ξ = nonHalfBlind s0 m ε ξ := by
  classical
  obtain ⟨-, -, -, -, -, hk⟩ := fineZone_props hε0 hε1 hεm
  unfold nonHalfBlindPair nonHalfBlind
  refine Finset.filter_congr fun x hx => ?_
  simp only [mem_product, mem_univ, true_and, mem_range] at hx
  obtain ⟨hk1, hkm, -, -⟩ := hk x.2.1 hx.1
  rw [halfBlindPair_iff hms hk1 hkm hx.2]

/-! ### Lemma 7.7 for the walk pair -/

/-- The families of the class `(h, k)` consist of hops of the class. -/
theorem familyPerPeriod_subset_class {s0 m k f : ℕ} (hms : m ≤ s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m)
    (hf : f < 4) (ξ : ℤ) (h : Bool) : familyPerPeriod s0 m ξ h k f ⊆ coverClass s0 m ξ 1 h k := by
  classical
  intro η hη
  unfold familyPerPeriod at hη
  rw [mem_filter] at hη
  obtain ⟨hcov, n, hn⟩ := hη
  rw [mem_coverClass]
  rw [mem_coverHops] at hcov
  refine ⟨hcov.1, ?_⟩
  have := family_inHopClass hms hk1 hkm hf hn ξ h n
  simp only at this
  rwa [show η.1 + headShift ξ h - n * (dnpPeriod s0 m : ℤ) - headShift ξ h + n * dnpPeriod s0 m = η.1
      by ring, show η.2 + headShift ξ h - n * (dnpPeriod s0 m : ℤ) - headShift ξ h + n * dnpPeriod s0 m =
      η.2 by ring] at this

/-- **Lemma 7.7(a)** for the walk pair: every family of the class `(h, k)` contains at least a
fraction `1/32` of the hops of the class with later endpoint in `[0, P)` (the class has exactly `4Λ`
of them, `card_coverClass`). -/
theorem class_card_le_family {s0 m k f : ℕ} (hms : m < s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m)
    (hf : f < 4) (ξ : ℤ) (h : Bool) :
    (coverClass s0 m ξ 1 h k).card ≤ 32 * (familyPerPeriod s0 m ξ h k f).card := by
  rw [card_coverClass hms.le ξ 1 h (by omega), card_familyPerPeriod hms.le hk1 hkm hf ξ h, one_mul]
  exact family_card_ge hk1 hkm hms hf

/-- **Lemma 7.7(b)** for the walk pair: every blind hop of family `f` of the class `(h, k)` (in any
period) has, under the block-pair label of `(B(a₁, K₁), B(a₂, K₂))` modulo `q`, the error
`a^{(h)}(k)` (apex family) or `b^{(h)}_j(k)` (band-`j` family). -/
theorem hopError_of_inFamily_blind {s0 m k f : ℕ} (hms : m < s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m)
    (hf : f < 4) (a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (h : Bool) {p u : ℤ}
    (hfam : InFamily s0 m ξ h k f p u) (hbl : IsBlind s0 m ξ h p u) :
    hopError (blockPairLabel s0 m a1 a2 K1 K2 q ξ) q p u =
      familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f := by
  obtain ⟨n, hn⟩ := hfam
  set P : ℤ := (dnpPeriod s0 m : ℤ)
  set c := headShift ξ h
  have e1 := hopError_add_mul_period hms.le a1 a2 K1 K2 q ξ (p - n * P) (u - n * P) n
  rw [sub_add_cancel, sub_add_cancel] at e1
  rw [e1, hopError_blockPairLabel hms.le a1 a2 K1 K2 q ξ h]
  have hbl' : BlindHop s0 m ξ h (p - n * P + c) (u - n * P + c) := by
    rw [← isBlind_iff_blindHop hms.le]
    exact (isBlind_add_mul_period s0 m ξ h (p - n * P) (u - n * P) n).1
      (by rwa [sub_add_cancel, sub_add_cancel])
  rw [show p - n * P + c = p + c - n * P by ring, show u - n * P + c = u + c - n * P by ring] at hbl' ⊢
  exact pairHopErr_of_blind K1 K2 q ξ hms hk1 hkm hf h (η := (p + c - n * P, u + c - n * P)) hn hbl'

/-- **Lemma 7.7(c)** for the walk pair: if the block-pair label `θ`-serves level `k` for head `h` on
an `r`-fold cover and a family of the class `(h, k)` is half-blind at `ξ`, the common error of its
blind hops is at most `64 θ q`. -/
theorem familyBlindErr_le_of_thetaServes {s0 m k f a1 a2 : ℕ} {K1 K2 q ξ : ℤ} {r : ℕ} {θ : ℝ}
    {h : Bool} (hms : m < s0) (hq : 0 < q) (hr : 0 < r) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4)
    (hserv : ThetaServes s0 m a1 a2 K1 K2 q ξ r θ h k) (hhb : HalfBlindPair s0 m ξ h k f) :
    (familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f : ℝ) ≤ 64 * θ * q :=
  familyBlindErr_le_of_served hms hq hk1 hkm hf (hserv.servedOnWitness hms hq hr)
    ((halfBlindPair_iff hms.le hk1 hkm hf ξ h).1 hhb)

/-! ### Lemma 7.8 for the walk pair -/

/-- **Lemma 7.8** (expectation) for the walk pair: over a uniformly random odd shift, the expected
number of triples `(h, k, f)`, `k ∈ ℱ_ε`, whose family is not half-blind is at most `64 ε² m`. -/
theorem sum_nonHalfBlindPair_le {s0 m : ℕ} {ε : ℝ} (hms : m < s0) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8)
    (hεm : 4 ≤ ε * m) :
    ∑ ξ ∈ oddRange (dnpPeriod s0 m), ((nonHalfBlindPair s0 m ε ξ).card : ℝ) ≤
      64 * ε ^ 2 * m * (oddRange (dnpPeriod s0 m)).card := by
  simp_rw [nonHalfBlindPair_eq hms.le hε0 hε1 hεm]
  exact sum_nonHalfBlind_le' hms hε0 hε1 hεm

/-- **Lemma 7.8** (probability) for the walk pair: more than `δ |ℱ_ε|` such triples,
`δ = 1/(48 (a₀ + 1))`, occur with probability at most `6144 (a₀ + 1) ε`. -/
theorem prob_many_nonHalfBlindPair_le {s0 m : ℕ} {ε : ℝ} (hms : m < s0) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 8) (hεm : 4 ≤ ε * m) (a0 : ℕ) :
    (((oddRange (dnpPeriod s0 m)).filter fun ξ : ℕ =>
        1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card < (nonHalfBlindPair s0 m ε ξ).card).card : ℝ) /
      (oddRange (dnpPeriod s0 m)).card ≤ 6144 * ((a0 : ℝ) + 1) * ε := by
  simp_rw [nonHalfBlindPair_eq hms.le hε0 hε1 hεm]
  exact prob_many_nonHalfBlind_le' hms hε0 hε1 hεm a0

/-! ### Lemma 7.9 and Theorem BP for the walk pair -/

open Classical in
/-- The levels `k ∈ {0, …, m}` that the block-pair label does not doubly `θ`-serve on the `r`-fold
cover. -/
noncomputable def unservedLevelsPair (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ) (θ : ℝ) : Finset ℕ :=
  (range (m + 1)).filter fun k => ¬ DoublyThetaServes s0 m a1 a2 K1 K2 q ξ r θ k

open Classical in
/-- The levels `k ∈ {0, …, m}` that the block-pair label doubly `θ`-serves on the `r`-fold cover. -/
noncomputable def doublyServedLevelsPair (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (r : ℕ) (θ : ℝ) :
    Finset ℕ :=
  (range (m + 1)).filter fun k => DoublyThetaServes s0 m a1 a2 K1 K2 q ξ r θ k

theorem doublyThetaServes_servedOnWitness {s0 m a1 a2 : ℕ} {K1 K2 q ξ : ℤ} {r : ℕ} {θ : ℝ} {k : ℕ}
    (hms : m < s0) (hq : 0 < q) (hr : 0 < r) (hd : DoublyThetaServes s0 m a1 a2 K1 K2 q ξ r θ k) :
    ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ true k ∧ ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ false k :=
  ⟨hd.1.servedOnWitness hms hq hr, hd.2.servedOnWitness hms hq hr⟩

theorem unservedLevels_subset_pair {s0 m a1 a2 : ℕ} {K1 K2 q : ℤ} {ξ : ℕ} {r : ℕ} {θ : ℝ}
    (hms : m < s0) (hq : 0 < q) (hr : 0 < r) :
    unservedLevels s0 m a1 a2 K1 K2 q ξ θ ⊆ unservedLevelsPair s0 m a1 a2 K1 K2 q ξ r θ := by
  classical
  intro k hk
  unfold unservedLevels at hk
  unfold unservedLevelsPair
  rw [mem_filter] at hk ⊢
  exact ⟨hk.1, fun hd => hk.2 (doublyThetaServes_servedOnWitness hms hq hr hd)⟩

theorem doublyServedLevelsPair_subset {s0 m a1 a2 : ℕ} {K1 K2 q : ℤ} {ξ : ℕ} {r : ℕ} {θ : ℝ}
    (hms : m < s0) (hq : 0 < q) (hr : 0 < r) :
    doublyServedLevelsPair s0 m a1 a2 K1 K2 q ξ r θ ⊆ doublyServedLevels s0 m a1 a2 K1 K2 q ξ θ := by
  classical
  intro k hk
  unfold doublyServedLevelsPair at hk
  unfold doublyServedLevels
  rw [mem_filter] at hk ⊢
  exact ⟨hk.1, doublyThetaServes_servedOnWitness hms hq hr hk.2⟩

/-- **Lemma 7.9** for the walk pair: at an odd shift `ξ` with (i) `Γ_{a,±}(ξ) ≥ γ|𝒦|` for all
`1 ≤ a ≤ a₀` and both signs and (ii) at most `δ|ℱ_ε|` triples `(h, k, f)`, `k ∈ ℱ_ε`, whose family is
not half-blind, for all `1 ≤ a₁, a₂ ≤ a₀`, all `K₁, K₂`, every `q ≥ 3` and every multiple `r` of `q`,
at least `c(m + 1) - 2` levels are not doubly `θ₀`-served by the block-pair label of
`(B(a₁, K₁), B(a₂, K₂))` modulo `q` on the `r`-fold cover, `c = min(γ/8, ε/(26(a₀ + 1)))`. -/
theorem witnesses_unserved_pair {s0 m a0 : ℕ} {γ ε : ℝ} (ha0 : 1 ≤ a0) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) (hms : m < s0) (hεm : 4 ≤ ε * m)
    (hsize : 4 * (jZero m + a0) ≤ m + 1) {ξ : ℕ} (hξ : ξ ∈ oddRange (dnpPeriod s0 m))
    (hi : ∀ a ∈ Icc (1 : ℕ) a0, ∀ dir : Bool,
      γ * ((coarseZone m).card : ℝ) ≤ goodCount s0 m a dir ξ)
    (hii : ((nonHalfBlindPair s0 m ε ξ).card : ℝ) ≤
      1 / (48 * ((a0 : ℝ) + 1)) * (fineZone m ε).card)
    {a1 a2 : ℕ} (ha1 : 1 ≤ a1) (ha1' : a1 ≤ a0) (ha2 : 1 ≤ a2) (ha2' : a2 ≤ a0) (K1 K2 q : ℤ)
    (hq : 3 ≤ q) : ∀ r : ℕ, 0 < r → q ∣ r →
      min (γ / 8) (ε / (26 * ((a0 : ℝ) + 1))) * ((m : ℝ) + 1) - 2 ≤
        ((unservedLevelsPair s0 m a1 a2 K1 K2 q ξ r (theta0 a0)).card : ℝ) := by
  intro r hr _
  rw [nonHalfBlindPair_eq hms.le hε0 hε1 hεm] at hii
  have hw := witnesses_unserved ha0 hγ0 hγ1 hε0 hε1 hms hεm hsize hξ hi hii ha1 ha1' ha2 ha2' K1 K2 q hq
  have hsub := Finset.card_le_card (unservedLevels_subset_pair (a1 := a1) (a2 := a2) (K1 := K1)
    (K2 := K2) (ξ := ξ) (θ := theta0 a0) hms (by omega : (0 : ℤ) < q) hr)
  have : ((unservedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card : ℝ) ≤
      (unservedLevelsPair s0 m a1 a2 K1 K2 q ξ r (theta0 a0)).card := by exact_mod_cast hsub
  linarith

/-- **Theorem BP** for the walk pair `x₁ = U(s₀, m, 1)`, `x₂ = x₁(· + ξ)`: assume Conjecture S for
`a = 1, …, a₀`, and put `θ₀ = 2^{-(a₀+11)}`, `c = 2^{-16}/(26 (a₀ + 1)²)`. There is a constant `C'` such
that for all `m` and `s₀ > m` some odd shift `ξ` has the property: for all `1 ≤ a₁, a₂ ≤ a₀`, all
`K₁, K₂`, every `q ≥ 3` and every multiple `r` of `q`, the block-pair label of `(B(a₁, K₁), B(a₂, K₂))`
modulo `q` on the `r`-fold cover doubly `θ₀`-serves at most `(1 - c)(m + 1) + C'` levels. -/
theorem theoremBP_pair {a0 : ℕ} (ha0 : 1 ≤ a0) (hS : ∀ a ∈ Icc 1 a0, ConjectureS a) :
    ∃ C' : ℝ, ∀ m s0 : ℕ, m < s0 → ∃ ξ ∈ oddRange (dnpPeriod s0 m),
      ∀ a1 a2 : ℕ, 1 ≤ a1 → a1 ≤ a0 → 1 ≤ a2 → a2 ≤ a0 → ∀ K1 K2 q : ℤ, 3 ≤ q →
        ∀ r : ℕ, 0 < r → q ∣ r →
          ((doublyServedLevelsPair s0 m a1 a2 K1 K2 q ξ r (theta0 a0)).card : ℝ) ≤
            (1 - constBP a0) * ((m : ℝ) + 1) + C' := by
  obtain ⟨C', hC'⟩ := theoremBP' ha0 hS
  refine ⟨C', fun m s0 hms => ?_⟩
  obtain ⟨ξ, hξ, hall⟩ := hC' m s0 hms
  refine ⟨ξ, hξ, fun a1 a2 ha1 ha1' ha2 ha2' K1 K2 q hq r hr _ => ?_⟩
  have hsub := Finset.card_le_card (doublyServedLevelsPair_subset (a1 := a1) (a2 := a2) (K1 := K1)
    (K2 := K2) (ξ := ξ) (θ := theta0 a0) hms (by omega : (0 : ℤ) < q) hr)
  have : ((doublyServedLevelsPair s0 m a1 a2 K1 K2 q ξ r (theta0 a0)).card : ℝ) ≤
      (doublyServedLevels s0 m a1 a2 K1 K2 q ξ (theta0 a0)).card := by exact_mod_cast hsub
  linarith [hall a1 a2 ha1 ha1' ha2 ha2' K1 K2 q hq]

end MergeDepth
