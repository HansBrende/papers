import MergeDepth.BlockPairsShift

/-!
# Block pairs: the label on the deep-nesting pair, families and blind errors (Definition 7.6,
Lemma 7.7)

A concrete model, in the time of one period of `U = U(s₀, m, 1)`, built from the tenth paper's
library.

* `turnPotential`: the turn potential on `ℤ` of `U` for level-uniform jumps (the tenth paper's
  `evalPhiRec` on `[0, P)`, extended by its increment per period); `blockPotential s0 m a K` carries
  the block label `B(a, K)`. `evalPhiRec_parent`: on the parent stroke of every level-`k` V of a
  period, `evalPhiRec` is a constant plus the stroke potential `strokePhiRec … (k - 1)` (the path
  sums of the eighth paper's Lemma 5.9 for these potentials). Hence `turnPotential_apex`,
  `turnPotential_band` (the single-head apex and valley-band increments, the eighth paper's
  Lemma 5.10 with `F = 0`) and `turnPotential_vDecomp` (the hypothesis of Theorem V* at every
  level-`κ` V).
* `periodTurns`: the turn times of one period; `periodTurnJump_support`: the turn jumps sit there;
  `turnPotential_sub_one`: the increment of the potential at `t` is the jump at `t mod P`; so
  `turnPotential_eq_of_turnFree`: the potential is constant across turn-free windows (`TurnFree`).
* `pairHopErr`: the error `(G(u) - G(p) - 1) mod q` of a hop of head `h` under the block-pair label
  `G = Φ₁ + Φ₂` of `(B(a₁, K₁), B(a₂, K₂))` at the shift `ξ` (`x₂ = x₁(· + ξ)`); `BlindHop`: no turn of
  the other head in `(p, u]`.
* **Definition 7.6**: `apexFamily`, `bandFamily`, `family s0 m k f` (`f = 0` apex, `f = j + 1`
  band `j`), `HalfBlind`, `fineZone`; the witness hops `witnessHops` (the union of the four
  families) with total error `witnessErr`, and `ServedOnWitness`: `θ`-service measured on them.
* **Lemma 7.7**: `family_card_ge` (a): each family has at least `4Λ/32` hops; `pairHopErr_of_blind`
  (b): its blind hops have the error `familyBlindErr` (`a(k)` or `b_j(k)`); and
  `familyBlindErr_le_of_served` (c): if level `k` is `θ`-served for head `h` and the family is
  half-blind, that error is at most `64 θ q`.

The eighth paper's Lemma 5.1(b),(c) (with a written proof there) identifies these explicit families
with hops of the class `(h, k)` and gives every class `4Λ` hops per period; a level that is
`θ`-served for a head is therefore `ServedOnWitness` for it. This identification is not formalized.
-/

namespace MergeDepth

open Finset DirectedReciprocity

/-- Inside a level-`i` stroke, the potential along the parent stroke (of level `i + d`) of the V with
apex `β ∈ vApicesAux s0 m i d` is a constant plus the stroke potential of that parent stroke. -/
theorem strokePhiRec_parent {s0 m : ℕ} (hms : m ≤ s0) (cb cf : ℕ → ℤ) :
    ∀ (d i : ℕ), i + 1 + d ≤ m → ∀ β ∈ vApicesAux s0 m i d,
      ∃ C : ℤ, ∀ o < strokeLen s0 m (i + d),
        strokePhiRec s0 m cb cf i (β - scaleR s0 (i + d) + o) =
          C + strokePhiRec s0 m cb cf (i + d) o := by
  intro d
  induction d with
  | zero =>
    intro i _ β hβ
    rw [vApicesAux, mem_singleton] at hβ
    subst hβ
    exact ⟨0, fun o _ => by simp⟩
  | succ d ih =>
    intro i hi β hβ
    have hspan := vApicesAux_span hms d (i + 1) (by omega)
    have hR : scaleR s0 (i + 1 + d) ≤ scaleR s0 (i + 1) := by
      unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsucc := strokeLen_succ (s0 := s0) (m := m) (i := i + 1 + d) (by omega) hms
    rw [vApicesAux, mem_union, mem_image, mem_image] at hβ
    rcases hβ with ⟨β', hβ', rfl⟩ | ⟨β', hβ', rfl⟩
    · obtain ⟨C', hC'⟩ := ih (i + 1) (by omega) β' hβ'
      obtain ⟨hβ1, hβ2⟩ := hspan β' hβ'
      refine ⟨cb (i + 1) + C', fun o ho => ?_⟩
      rw [show i + (d + 1) = i + 1 + d by omega] at ho ⊢
      have hlt : β' - scaleR s0 (i + 1 + d) + o < strokeLen s0 m (i + 1) := by
        rw [show i + 1 + 1 + d = i + 1 + d + 1 by omega] at hβ2; omega
      have hback := strokePhiRec_back cb cf (κ := i + 1) (by omega) (by omega) hlt
      simp only [Nat.add_sub_cancel] at hback
      rw [show scaleR s0 i + β' - scaleR s0 (i + 1 + d) + o =
        scaleR s0 i + (β' - scaleR s0 (i + 1 + d) + o) by omega, hback, hC' o ho]
      ring
    · obtain ⟨C', hC'⟩ := ih (i + 1) (by omega) β' hβ'
      obtain ⟨hβ1, hβ2⟩ := hspan β' hβ'
      refine ⟨cf (i + 1) + C', fun o ho => ?_⟩
      rw [show i + (d + 1) = i + 1 + d by omega] at ho ⊢
      have hlt : β' - scaleR s0 (i + 1 + d) + o < strokeLen s0 m (i + 1) := by
        rw [show i + 1 + 1 + d = i + 1 + d + 1 by omega] at hβ2; omega
      have hfwd := strokePhiRec_fwd cb cf (κ := i + 1) (by omega) (by omega) hlt
      simp only [Nat.add_sub_cancel] at hfwd
      rw [show scaleR s0 i + strokeLen s0 m (i + 1) + β' - scaleR s0 (i + 1 + d) + o =
        scaleR s0 i + strokeLen s0 m (i + 1) + (β' - scaleR s0 (i + 1 + d) + o) by omega, hfwd,
        hC' o ho]
      ring

/-- On the parent stroke of every level-`k` V in a period, `evalPhiRec` is a constant plus the
stroke potential of level `k - 1`. -/
theorem evalPhiRec_parent {s0 m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hms : m ≤ s0)
    (cb cf : ℕ → ℤ) (jTip : ℤ) {α : ℕ} (hα : α ∈ periodVApices s0 m k) :
    scaleR s0 (k - 1) ≤ α ∧ ∃ C : ℤ, ∀ o < strokeLen s0 m (k - 1),
      evalPhiRec s0 m cb cf jTip (α - scaleR s0 (k - 1) + o) =
        C + strokePhiRec s0 m cb cf (k - 1) o := by
  rw [periodVApices, mem_biUnion] at hα
  obtain ⟨q, hq, hα⟩ := hα
  rw [mem_image] at hα
  obtain ⟨β, hβ, rfl⟩ := hα
  rw [mem_range] at hq
  obtain ⟨hβ1, hβ2⟩ := vApicesAux_span hms (k - 1) 0 (by omega) β hβ
  rw [show 0 + 1 + (k - 1) = k by omega] at hβ2
  have hR : scaleR s0 (k - 1) ≤ scaleR s0 0 := by
    unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨C, hC⟩ := strokePhiRec_parent hms cb cf (k - 1) 0 (by omega) β hβ
  rw [show 0 + (k - 1) = k - 1 by omega] at hC
  have hsucc := strokeLen_succ (s0 := s0) (m := m) (i := k - 1) (by omega) hms
  rw [show k - 1 + 1 = k by omega] at hsucc
  refine ⟨by nlinarith [Nat.zero_le q], ?_⟩
  set pi0 := strokeLen s0 m 0
  have hpi0 := strokeLen_pos s0 m 0
  refine ⟨(q : ℤ) * strokeMass m cf 0 + (if pi0 ≤ q * pi0 then jTip else 0) +
    (if 3 * pi0 ≤ q * pi0 then jTip else 0) + C, fun o ho => ?_⟩
  have hy : β - scaleR s0 (k - 1) + o < pi0 := by omega
  have hdiv : (q * pi0 + β - scaleR s0 (k - 1) + o) / pi0 = q := by
    rw [show q * pi0 + β - scaleR s0 (k - 1) + o = (β - scaleR s0 (k - 1) + o) + pi0 * q by
      rw [Nat.mul_comm]; omega]
    rw [Nat.add_mul_div_left _ _ hpi0, Nat.div_eq_of_lt hy, zero_add]
  have hmod : (q * pi0 + β - scaleR s0 (k - 1) + o) % pi0 = β - scaleR s0 (k - 1) + o := by
    rw [show q * pi0 + β - scaleR s0 (k - 1) + o = (β - scaleR s0 (k - 1) + o) + pi0 * q by
      rw [Nat.mul_comm]; omega]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  have hle1 : (pi0 ≤ q * pi0 + β - scaleR s0 (k - 1) + o) ↔ pi0 ≤ q * pi0 := by
    constructor
    · intro h; by_contra hc; push Not at hc
      have : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · exact h0
        · nlinarith
      subst this; omega
    · intro h; omega
  have hle3 : (3 * pi0 ≤ q * pi0 + β - scaleR s0 (k - 1) + o) ↔ 3 * pi0 ≤ q * pi0 := by
    constructor
    · intro h; by_contra hc; push Not at hc
      have : q ≤ 2 := by
        by_contra hq3; push Not at hq3; nlinarith
      have : q * pi0 + β - scaleR s0 (k - 1) + o < 3 * pi0 := by
        have : q * pi0 ≤ 2 * pi0 := Nat.mul_le_mul_right _ this
        omega
      omega
    · intro h; omega
  unfold evalPhiRec
  dsimp only
  rw [show q * pi0 + β - scaleR s0 (k - 1) + o = q * pi0 + β - scaleR s0 (k - 1) + o from rfl]
  rw [show (q * strokeLen s0 m 0 + β - scaleR s0 (k - 1) + o) = q * pi0 + β - scaleR s0 (k - 1) + o
    from rfl, hdiv, hmod, hC o ho]
  have e1 : (strokeLen s0 m 0 ≤ q * pi0 + β - scaleR s0 (k - 1) + o) ↔ pi0 ≤ q * pi0 := hle1
  have e3 : (3 * strokeLen s0 m 0 ≤ q * pi0 + β - scaleR s0 (k - 1) + o) ↔ 3 * pi0 ≤ q * pi0 := hle3
  simp only [e1, e3]
  ring


/-- The turn jumps inside a level-`i` stroke sit at the apices and valleys of its inner V's. -/
theorem strokeTurnJumpAux_support {s0 m : ℕ} (cb cf : ℕ → ℤ) :
    ∀ (d i τ : ℕ), i + d ≤ m → strokeTurnJumpAux s0 m cb cf i d τ ≠ 0 →
      ∃ d' < d, τ ∈ vApicesAux s0 m i d' ∨
        ∃ β ∈ vApicesAux s0 m i d', τ = β + strokeLen s0 m (i + 1 + d') := by
  intro d
  induction d with
  | zero => intro i τ _ h; exact absurd rfl h
  | succ d ih =>
    intro i τ hid h
    simp only [strokeTurnJumpAux] at h
    split_ifs at h with h1 h2 h3 h4 h5
    · exact absurd rfl h
    · exact ⟨0, by omega, Or.inl (by rw [vApicesAux, mem_singleton]; exact h2)⟩
    · obtain ⟨d'', hd'', hmem⟩ := ih (i + 1) (τ - scaleR s0 i) (by omega) h
      refine ⟨d'' + 1, by omega, ?_⟩
      rcases hmem with hm | ⟨β, hβ, hτ⟩
      · left; rw [vApicesAux, mem_union, mem_image]
        exact Or.inl ⟨τ - scaleR s0 i, hm, by omega⟩
      · right; refine ⟨scaleR s0 i + β, ?_, ?_⟩
        · rw [vApicesAux, mem_union, mem_image]; exact Or.inl ⟨β, hβ, rfl⟩
        · rw [show i + 1 + (d'' + 1) = i + 1 + 1 + d'' by omega]; omega
    · exact ⟨0, by omega, Or.inr ⟨scaleR s0 i, by rw [vApicesAux, mem_singleton],
        by rw [h4]⟩⟩
    · obtain ⟨d'', hd'', hmem⟩ := ih (i + 1) (τ - scaleR s0 i - strokeLen s0 m (i + 1)) (by omega) h
      refine ⟨d'' + 1, by omega, ?_⟩
      rcases hmem with hm | ⟨β, hβ, hτ⟩
      · left; rw [vApicesAux, mem_union, mem_image, mem_image]
        exact Or.inr ⟨_, hm, by omega⟩
      · right; refine ⟨scaleR s0 i + strokeLen s0 m (i + 1) + β, ?_, ?_⟩
        · rw [vApicesAux, mem_union, mem_image, mem_image]; exact Or.inr ⟨β, hβ, rfl⟩
        · rw [show i + 1 + (d'' + 1) = i + 1 + 1 + d'' by omega]; omega
    · exact absurd rfl h

/-- The turn times of `U(s₀, m, 1)` in one period `[0, P)`: the apex and valley times of the V's of
all levels `1, …, m` and the two tips `Π₀`, `3Π₀`. -/
def periodTurns (s0 m : ℕ) : Finset ℕ :=
  (Icc 1 m).biUnion (fun i => periodVApices s0 m i ∪
    (periodVApices s0 m i).image (· + strokeLen s0 m i)) ∪
    {strokeLen s0 m 0, 3 * strokeLen s0 m 0}

/-- The turn jumps of one period sit at turn times. -/
theorem periodTurnJump_support {s0 m : ℕ} (cb cf : ℕ → ℤ) (jTip : ℤ) {r : ℕ}
    (h : periodTurnJump s0 m cb cf jTip r ≠ 0) : r ∈ periodTurns s0 m := by
  unfold periodTurnJump at h
  dsimp only at h
  split_ifs at h with h1 h2
  · unfold periodTurns; rw [mem_union, mem_insert, mem_singleton]; right; exact h1
  · obtain ⟨hlt, hne⟩ := h2
    obtain ⟨d', hd', hmem⟩ := strokeTurnJumpAux_support cb cf (m - 0) 0 _ (by omega) h
    have hpi0 := strokeLen_pos s0 m 0
    obtain ⟨q, hqdef⟩ : ∃ q, q = r / strokeLen s0 m 0 := ⟨_, rfl⟩
    have hq : q < 4 := by rw [hqdef]; exact Nat.div_lt_of_lt_mul (by linarith)
    have hr : r = q * strokeLen s0 m 0 + r % strokeLen s0 m 0 := by
      rw [hqdef, Nat.mul_comm]; exact (Nat.div_add_mod r _).symm
    unfold periodTurns
    rw [mem_union, mem_biUnion]
    left
    refine ⟨d' + 1, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [mem_union]
    rcases hmem with hm | ⟨β, hβ, hτ⟩
    · left
      rw [periodVApices, mem_biUnion]
      exact ⟨q, mem_range.mpr hq, mem_image.mpr ⟨_, by simpa using hm, hr.symm⟩⟩
    · right
      rw [mem_image]
      refine ⟨q * strokeLen s0 m 0 + β, ?_, ?_⟩
      · rw [periodVApices, mem_biUnion]
        exact ⟨q, mem_range.mpr hq, mem_image.mpr ⟨β, by simpa using hβ, rfl⟩⟩
      · rw [show 0 + 1 + d' = d' + 1 by omega] at hτ; omega
  · exact absurd rfl h

/-- The turn potential on `ℤ` of `U(s₀, m, 1)` for level-uniform jumps `cb, cf` and tip jump `jTip`:
`evalPhiRec` on `[0, P)`, extended by its increment `4 M_f(0) + 2 j_tip` per period. -/
def turnPotential (s0 m : ℕ) (cb cf : ℕ → ℤ) (jTip : ℤ) (t : ℤ) : ℤ :=
  t / (dnpPeriod s0 m : ℤ) * (4 * strokeMass m cf 0 + 2 * jTip) +
    evalPhiRec s0 m cb cf jTip (t % (dnpPeriod s0 m : ℤ)).toNat

theorem dnpPeriod_pos (s0 m : ℕ) : 0 < dnpPeriod s0 m := by
  unfold dnpPeriod; exact Nat.mul_pos (by norm_num) (strokeLen_pos _ _ _)

theorem turnPotential_of_lt {s0 m : ℕ} (cb cf : ℕ → ℤ) (jTip : ℤ) {t : ℕ}
    (ht : t < dnpPeriod s0 m) : turnPotential s0 m cb cf jTip t = evalPhiRec s0 m cb cf jTip t := by
  unfold turnPotential
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  rw [Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast ht),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ht)]
  simp

theorem turnPotential_add_mul_period {s0 m : ℕ} (cb cf : ℕ → ℤ) (jTip : ℤ) (t n : ℤ) :
    turnPotential s0 m cb cf jTip (t + n * dnpPeriod s0 m) =
      turnPotential s0 m cb cf jTip t + n * (4 * strokeMass m cf 0 + 2 * jTip) := by
  unfold turnPotential
  have hP : (dnpPeriod s0 m : ℤ) ≠ 0 := by exact_mod_cast (dnpPeriod_pos s0 m).ne'
  rw [Int.add_mul_ediv_right _ _ hP, Int.add_mul_emod_self_right]
  ring

theorem turnPotential_add_period {s0 m : ℕ} (cb cf : ℕ → ℤ) (jTip : ℤ) (t : ℤ) :
    turnPotential s0 m cb cf jTip (t + dnpPeriod s0 m) =
      turnPotential s0 m cb cf jTip t + (4 * strokeMass m cf 0 + 2 * jTip) := by
  have := turnPotential_add_mul_period (s0 := s0) (m := m) cb cf jTip t 1
  rw [one_mul, one_mul] at this
  exact this


theorem evalPhiRec_zero (s0 m : ℕ) (cb cf : ℕ → ℤ) (jTip : ℤ) : evalPhiRec s0 m cb cf jTip 0 = 0 := by
  have hpi0 := strokeLen_pos s0 m 0
  unfold evalPhiRec
  simp only [Nat.zero_div, Nat.cast_zero, zero_mul, Nat.zero_mod, zero_add]
  rw [strokePhiRec_lt_scaleR cb cf (Nat.zero_le m) (scaleR_pos s0 0)]
  simp [show ¬ strokeLen s0 m 0 ≤ 0 by omega, hpi0.ne']

theorem evalPhiRec_last {s0 m : ℕ} (hms : m ≤ s0) (cb cf : ℕ → ℤ) (jTip : ℤ) :
    evalPhiRec s0 m cb cf jTip (dnpPeriod s0 m - 1) = 4 * strokeMass m cf 0 + 2 * jTip := by
  have hpi0 := strokeLen_pos s0 m 0
  set pi0 := strokeLen s0 m 0
  have hP : dnpPeriod s0 m - 1 = 3 * pi0 + (pi0 - 1) := by unfold dnpPeriod; omega
  unfold evalPhiRec
  dsimp only
  rw [hP]
  have hdiv : (3 * pi0 + (pi0 - 1)) / pi0 = 3 := by
    rw [show 3 * pi0 + (pi0 - 1) = (pi0 - 1) + pi0 * 3 by ring, Nat.add_mul_div_left _ _ hpi0,
      Nat.div_eq_of_lt (by omega)]
  have hmod : (3 * pi0 + (pi0 - 1)) % pi0 = pi0 - 1 := by
    rw [show 3 * pi0 + (pi0 - 1) = (pi0 - 1) + pi0 * 3 by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have htail := strokePhiRec_tail_fwd_chain cb cf (k := 0) (l := m) (y := 1) (Nat.zero_le m)
    le_rfl hms (by norm_num) (Nat.one_le_iff_ne_zero.mpr (strokeLen_pos s0 m m).ne')
  have hm0 : strokePhiRec s0 m cb cf m (strokeLen s0 m m - 1) = 0 := by
    unfold strokePhiRec; rw [Nat.sub_self]; rfl
  rw [hm0, add_zero] at htail
  have hmass : strokeMass m cf 0 = ∑ i ∈ Icc (0 + 1) m, cf i := rfl
  rw [hdiv, hmod, htail, ← hmass,
    ite_eq_left (show strokeLen s0 m 0 ≤ 3 * pi0 + (pi0 - 1) by omega),
    ite_eq_left (show 3 * strokeLen s0 m 0 ≤ 3 * pi0 + (pi0 - 1) by omega)]
  push_cast; ring

theorem periodTurnJump_zero (s0 m : ℕ) (cb cf : ℕ → ℤ) (jTip : ℤ) :
    periodTurnJump s0 m cb cf jTip 0 = 0 := by
  have hpi0 := strokeLen_pos s0 m 0
  unfold periodTurnJump
  simp [show (0 : ℕ) ≠ strokeLen s0 m 0 by omega, show (0 : ℕ) ≠ 3 * strokeLen s0 m 0 by omega]

/-- The increment of the turn potential at a time `t` is the turn jump at `t mod P`. -/
theorem turnPotential_sub_one {s0 m : ℕ} (hms : m ≤ s0) (cb cf : ℕ → ℤ) (jTip : ℤ) (t : ℤ) :
    turnPotential s0 m cb cf jTip t - turnPotential s0 m cb cf jTip (t - 1) =
      periodTurnJump s0 m cb cf jTip (t % (dnpPeriod s0 m : ℤ)).toNat := by
  have hP : (0 : ℤ) < dnpPeriod s0 m := by exact_mod_cast dnpPeriod_pos s0 m
  obtain ⟨n, r, hr0, hrP, rfl⟩ : ∃ n r : ℤ, 0 ≤ r ∧ r < dnpPeriod s0 m ∧
      t = r + n * dnpPeriod s0 m :=
    ⟨t / dnpPeriod s0 m, t % dnpPeriod s0 m, Int.emod_nonneg _ hP.ne', Int.emod_lt_of_pos _ hP,
      by linarith [Int.emod_add_mul_ediv t (dnpPeriod s0 m)]⟩
  rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt hr0 hrP,
    turnPotential_add_mul_period cb cf jTip r n,
    show r + n * (dnpPeriod s0 m : ℤ) - 1 = (r - 1) + n * dnpPeriod s0 m by ring,
    turnPotential_add_mul_period cb cf jTip (r - 1) n]
  obtain ⟨R, rfl⟩ : ∃ R : ℕ, r = R := ⟨r.toNat, (Int.toNat_of_nonneg hr0).symm⟩
  have hRP : R < dnpPeriod s0 m := by exact_mod_cast hrP
  rw [Int.toNat_natCast, turnPotential_of_lt cb cf jTip hRP]
  rcases Nat.eq_zero_or_pos R with hR0 | hR0
  · subst hR0
    have hlast := turnPotential_add_mul_period (s0 := s0) (m := m) cb cf jTip
      ((dnpPeriod s0 m - 1 : ℕ) : ℤ) (-1)
    rw [show ((dnpPeriod s0 m - 1 : ℕ) : ℤ) + -1 * (dnpPeriod s0 m : ℤ) = ((0 : ℕ) : ℤ) - 1 by
      have := dnpPeriod_pos s0 m; push_cast [Nat.cast_sub (by omega : 1 ≤ dnpPeriod s0 m)]; ring]
      at hlast
    rw [hlast, turnPotential_of_lt cb cf jTip (by have := dnpPeriod_pos s0 m; omega),
      evalPhiRec_last hms, evalPhiRec_zero, periodTurnJump_zero]
    ring
  · have hR1 : ((R : ℤ) - 1) = ((R - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hR0]; ring
    rw [hR1, turnPotential_of_lt cb cf jTip (by omega),
      evalPhiRec_eq_sum_turnJumps cb cf jTip hms hRP,
      evalPhiRec_eq_sum_turnJumps cb cf jTip hms (by omega : R - 1 < dnpPeriod s0 m)]
    conv_lhs => rw [show R = (R - 1) + 1 by omega]
    rw [Finset.sum_Ioc_succ_top (by omega), show R - 1 + 1 = R by omega]
    ring


/-- No turn of `U` lies at the times `t + c` for `p < t ≤ u` (times modulo `P`). -/
def TurnFree (s0 m : ℕ) (c p u : ℤ) : Prop :=
  ∀ t ∈ Finset.Ioc p u, ((t + c) % (dnpPeriod s0 m : ℤ)).toNat ∉ periodTurns s0 m

/-- Across a turn-free window the turn potential does not change. -/
theorem turnPotential_eq_of_turnFree {s0 m : ℕ} (hms : m ≤ s0) (cb cf : ℕ → ℤ) (jTip : ℤ)
    {c p u : ℤ} (hpu : p ≤ u) (h : TurnFree s0 m c p u) :
    turnPotential s0 m cb cf jTip (u + c) = turnPotential s0 m cb cf jTip (p + c) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = p + n := ⟨(u - p).toNat, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := turnPotential_sub_one hms cb cf jTip (p + ((n + 1 : ℕ) : ℤ) + c)
    have hnot := h (p + ((n + 1 : ℕ) : ℤ)) (Finset.mem_Ioc.mpr ⟨by omega, le_refl _⟩)
    have hzero : periodTurnJump s0 m cb cf jTip
        ((p + ((n + 1 : ℕ) : ℤ) + c) % (dnpPeriod s0 m : ℤ)).toNat = 0 := by
      by_contra hne; exact hnot (periodTurnJump_support cb cf jTip hne)
    rw [hzero, sub_eq_zero] at hstep
    rw [hstep, show p + ((n + 1 : ℕ) : ℤ) + c - 1 = p + (n : ℕ) + c by push_cast; ring]
    exact ih (by omega) fun t ht => h t (Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp ht).1, by have := (Finset.mem_Ioc.mp ht).2; push_cast at this ⊢; omega⟩)

/-- **Single-head apex formula** on `ℤ`: for every level-`k` V of a period and `1 ≤ d < R_k`, the
apex hop `(α - d, α + d)` has single-head increment `1 + A_k`. -/
theorem turnPotential_apex {s0 m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hms : m ≤ s0)
    (A E : ℕ → ℤ) (jTip : ℤ) {α : ℕ} (hα : α ∈ periodVApices s0 m k) {d : ℕ} (hd1 : 1 ≤ d)
    (hd2 : d < scaleR s0 k) :
    turnPotential s0 m (pathSumBack A) (pathSumFwd A E) jTip ((α : ℤ) + d) -
      turnPotential s0 m (pathSumBack A) (pathSumFwd A E) jTip ((α : ℤ) - d) - 1 = A k := by
  obtain ⟨hRα, C, hC⟩ := evalPhiRec_parent hk1 hkm hms (pathSumBack A) (pathSumFwd A E) jTip hα
  have hspan := periodVApices_span_subset hk1 hkm hms hα
  have hR : scaleR s0 (k - 1) = 2 * scaleR s0 k := by
    simpa [Nat.sub_add_cancel hk1] using scaleR_succ (s0 := s0) (i := k - 1) (by omega)
  have hsucc := strokeLen_succ (s0 := s0) (m := m) (i := k - 1) (by omega) hms
  rw [show k - 1 + 1 = k by omega] at hsucc
  have hpk : scaleR s0 k ≤ strokeLen s0 m k := by
    unfold strokeLen; nlinarith [scaleR_pos s0 k]
  have h1 : (α : ℤ) + d = ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) + d) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hRα]; ring
  have h2 : (α : ℤ) - d = ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) - d) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hRα, Nat.cast_sub (show d ≤ scaleR s0 (k - 1) by omega)]; ring
  rw [h1, h2, turnPotential_of_lt _ _ _ (by omega), turnPotential_of_lt _ _ _ (by omega),
    hC _ (by omega), hC _ (by omega)]
  have := strokePhiRec_apex_hop (s0 := s0) (m := m) A E hk1 hkm hms hd1 hd2
  simp only at this
  linarith

/-- **Single-head valley-band formula** on `ℤ`: for every level-`k` V of a period with valley
`ν = α + Π_k`, every `k ≤ l ≤ m` and `1 ≤ x < R_l`, the hop `(ν - (m - l) R_l - x, ν + x)` has
single-head increment `1 + E_k - ∑_{i=k+1}^{l} (A_i + E_i + 2)`. -/
theorem turnPotential_band {s0 m k l : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (hlm : l ≤ m) (hms : m ≤ s0)
    (A E : ℕ → ℤ) (jTip : ℤ) {α : ℕ} (hα : α ∈ periodVApices s0 m k) {x : ℕ} (hx1 : 1 ≤ x)
    (hx2 : x < scaleR s0 l) :
    turnPotential s0 m (pathSumBack A) (pathSumFwd A E) jTip (((α + strokeLen s0 m k + x : ℕ) : ℤ)) -
      turnPotential s0 m (pathSumBack A) (pathSumFwd A E) jTip
        (((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x) - 1 =
      E k - ∑ i ∈ Icc (k + 1) l, (A i + E i + 2) := by
  obtain ⟨hRα, C, hC⟩ := evalPhiRec_parent hk1 (by omega) hms (pathSumBack A) (pathSumFwd A E) jTip hα
  have hspan := periodVApices_span_subset hk1 (by omega) hms hα
  have hsucc := strokeLen_succ (s0 := s0) (m := m) (i := k - 1) (by omega) hms
  rw [show k - 1 + 1 = k by omega] at hsucc
  have hRl : scaleR s0 l ≤ scaleR s0 k := by
    unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpl : (m - l + 1) * scaleR s0 l = strokeLen s0 m l := rfl
  have hPl : strokeLen s0 m l ≤ strokeLen s0 m k := strokeLen_anti hkl hlm hms
  have hy : (m - l) * scaleR s0 l + x < strokeLen s0 m l := by
    rw [← hpl]; nlinarith
  have h1 : ((α + strokeLen s0 m k + x : ℕ) : ℤ) =
      ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) + strokeLen s0 m k + x) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hRα]; ring
  have h2 : ((α + strokeLen s0 m k : ℕ) : ℤ) - ((m - l) * scaleR s0 l : ℕ) - x =
      ((α - scaleR s0 (k - 1) + (scaleR s0 (k - 1) + strokeLen s0 m k -
        ((m - l) * scaleR s0 l + x)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hRα, Nat.cast_sub (show (m - l) * scaleR s0 l + x ≤
      scaleR s0 (k - 1) + strokeLen s0 m k by omega)]
    ring
  rw [h1, h2, turnPotential_of_lt _ _ _ (by omega), turnPotential_of_lt _ _ _ (by omega),
    hC _ (by omega), hC _ (by omega)]
  have := strokePhiRec_valley_band_hop (s0 := s0) (m := m) A E hk1 hkl hlm hms hx1 hx2
  simp only at this
  linarith

/-- The turn potential has the level-uniform V decomposition (the hypothesis of Theorem V*) at
every level-`κ` V of a period. -/
theorem turnPotential_vDecomp {s0 m κ : ℕ} (hκ1 : 1 ≤ κ) (hκm : κ ≤ m) (hms : m ≤ s0)
    (cb cf : ℕ → ℤ) (jTip : ℤ) {α : ℕ} (hα : α ∈ periodVApices s0 m κ) :
    ∃ C : ℤ, HasLevelUniformVDecomp (turnPotential s0 m cb cf jTip) (α : ℤ) (strokeLen s0 m κ)
      C (cb κ) (cf κ) (strokePhiRec s0 m cb cf κ) := by
  obtain ⟨hRα, C, hC⟩ := evalPhiRec_parent hκ1 hκm hms cb cf jTip hα
  have hspan := periodVApices_span_subset hκ1 hκm hms hα
  have hsucc := strokeLen_succ (s0 := s0) (m := m) (i := κ - 1) (by omega) hms
  rw [show κ - 1 + 1 = κ by omega] at hsucc
  refine ⟨C, fun o ho => ⟨?_, ?_⟩⟩
  · have h1 : (α : ℤ) + o = ((α - scaleR s0 (κ - 1) + (scaleR s0 (κ - 1) + o) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hRα]; ring
    rw [h1, turnPotential_of_lt _ _ _ (by omega), hC _ (by omega),
      strokePhiRec_back cb cf hκ1 hκm ho]
    ring
  · have h1 : (α : ℤ) + strokeLen s0 m κ + o =
        ((α - scaleR s0 (κ - 1) + (scaleR s0 (κ - 1) + strokeLen s0 m κ + o) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hRα]; ring
    rw [h1, turnPotential_of_lt _ _ _ (by omega), hC _ (by omega),
      strokePhiRec_fwd cb cf hκ1 hκm ho]
    ring


/-! ### The block-pair label -/

/-- The potential of `U` carrying the block label `B(a, K)` (tip jumps `1`). -/
def blockPotential (s0 m a : ℕ) (K : ℤ) : ℤ → ℤ :=
  turnPotential s0 m (pathSumBack (blockA m a K)) (pathSumFwd (blockA m a K) (blockE m a K)) 1

/-- The error `(G(u) - G(p) - 1) mod q` of a hop `(p, u)` of head `h` (`true` for head `1`, `false`
for head `2`), given in the head's own time, under the block-pair label `G = Φ₁ + Φ₂` of
`(B(a₁, K₁), B(a₂, K₂))` modulo `q` for the pair `x₁ = U`, `x₂ = U(· + ξ)`. -/
def pairHopErr (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (h : Bool) (p u : ℤ) : ℤ :=
  if h then
    (blockPotential s0 m a1 K1 u - blockPotential s0 m a1 K1 p +
      (blockPotential s0 m a2 K2 (u + ξ) - blockPotential s0 m a2 K2 (p + ξ)) - 1) % q
  else
    (blockPotential s0 m a2 K2 u - blockPotential s0 m a2 K2 p +
      (blockPotential s0 m a1 K1 (u + -ξ) - blockPotential s0 m a1 K1 (p + -ξ)) - 1) % q

/-- A hop `(p, u)` of head `h` (in its own time) is **blind** at the shift `ξ`: no turn of the other
head lies in `(p, u]`. In the time of head `1` the turns of head `2` are the times `t` with `t + ξ` a
turn of `U`; in the time of head `2` the turns of head `1` are the times `t` with `t - ξ` one. -/
def BlindHop (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u : ℤ) : Prop :=
  TurnFree s0 m (if h then ξ else -ξ) p u

instance (s0 m : ℕ) (ξ : ℤ) (h : Bool) (p u : ℤ) : Decidable (BlindHop s0 m ξ h p u) := by
  unfold BlindHop TurnFree; infer_instance

/-! ### Definition 7.6: families and the fine zone -/

/-- `R_{l+1}`, with `R_{m+1} = 0`. -/
def scaleBelow (s0 m l : ℕ) : ℕ := if l < m then scaleR s0 (l + 1) else 0

/-- The apex family of a level-`k` class in one period: the hops `(α - d, α + d)`, `1 ≤ d < R_k`, of
the level-`k` V's (in the head's own time). -/
def apexFamily (s0 m k : ℕ) : Finset (ℤ × ℤ) :=
  ((periodVApices s0 m k) ×ˢ (Icc 1 (scaleR s0 k - 1))).image
    fun x => ((x.1 : ℤ) - x.2, (x.1 : ℤ) + x.2)

/-- The band-`j` family of a level-`k` class in one period: with `l = k + j` and `ν = α + Π_k`, the
valley hops `(ν - (m - l) R_l - x, ν + x)`, `R_{l+1} < x < R_l`. -/
def bandFamily (s0 m k j : ℕ) : Finset (ℤ × ℤ) :=
  ((periodVApices s0 m k) ×ˢ (Ioo (scaleBelow s0 m (k + j)) (scaleR s0 (k + j)))).image
    fun x => (((x.1 + strokeLen s0 m k : ℕ) : ℤ) - ((m - (k + j)) * scaleR s0 (k + j) : ℕ) - x.2,
      ((x.1 + strokeLen s0 m k + x.2 : ℕ) : ℤ))

/-- The four families of the class of level `k`: `f = 0` is the apex family and `f = j + 1` the
band-`j` family (`j = 0, 1, 2`). -/
def family (s0 m k f : ℕ) : Finset (ℤ × ℤ) :=
  if f = 0 then apexFamily s0 m k else bandFamily s0 m k (f - 1)

/-- The blind error of family `f` of a level-`k` class of a head carrying `B(a, K)`: `a(k)` for the
apex family and `b_j(k)` for the band-`j` family. -/
def familyBlindErr (m a : ℕ) (K q : ℤ) (k f : ℕ) : ℤ :=
  if f = 0 then blindApexErr (blockA m a K) q k
  else blindBandErr (blockA m a K) (blockE m a K) q k (k + (f - 1))

/-- A family is **half-blind** at `ξ` for head `h` if at least half of its hops are blind. -/
def HalfBlind (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k f : ℕ) : Prop :=
  (family s0 m k f).card ≤ 2 * ((family s0 m k f).filter fun η => BlindHop s0 m ξ h η.1 η.2).card

instance (s0 m : ℕ) (ξ : ℤ) (h : Bool) (k f : ℕ) : Decidable (HalfBlind s0 m ξ h k f) := by
  unfold HalfBlind; infer_instance

/-- The fine zone `ℱ_ε = {k : m - ⌊ε m⌋ ≤ k ≤ m - 2}`. -/
noncomputable def fineZone (m : ℕ) (ε : ℝ) : Finset ℕ := Icc (m - ⌊ε * m⌋₊) (m - 2)

/-- The witness hops of a level: the union of its four families (empty unless `1 ≤ k ≤ m - 2`). -/
def witnessHops (s0 m k : ℕ) : Finset (ℤ × ℤ) :=
  if 1 ≤ k ∧ k + 2 ≤ m then (range 4).biUnion (family s0 m k) else ∅

/-- The total error of the witness hops of level `k` of head `h` in one period. -/
def witnessErr (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (h : Bool) (k : ℕ) : ℤ :=
  ∑ η ∈ witnessHops s0 m k, pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2

/-- `θ`-service measured on the witness hops: their total error is at most `θ q` times the
`4Λ` hops of a class in one period. A level that is `θ`-served for head `h` is `θ`-served on its
witness hops, since these are hops of its class and errors are nonnegative. -/
def ServedOnWitness (s0 m a1 a2 : ℕ) (K1 K2 q ξ : ℤ) (θ : ℝ) (h : Bool) (k : ℕ) : Prop :=
  (witnessErr s0 m a1 a2 K1 K2 q ξ h k : ℝ) ≤ θ * q * (4 * 2 ^ s0)

/-! ### Lemma 7.7 -/

theorem card_apexFamily {s0 m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hms : m ≤ s0) :
    (apexFamily s0 m k).card = 2 ^ (k + 1) * (scaleR s0 k - 1) := by
  unfold apexFamily
  rw [Finset.card_image_of_injective _ (fun x y hxy => by
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by omega) (by omega)), card_product, card_periodVApices hk1 hkm hms,
    Nat.card_Icc]
  congr 1

theorem card_bandFamily {s0 m k j : ℕ} (hk1 : 1 ≤ k) (hkm : k + j ≤ m) (hms : m ≤ s0) :
    (bandFamily s0 m k j).card =
      2 ^ (k + 1) * (scaleR s0 (k + j) - scaleBelow s0 m (k + j) - 1) := by
  unfold bandFamily
  rw [Finset.card_image_of_injOn, card_product, card_periodVApices hk1 (by omega) hms,
    Nat.card_Ioo]
  · intro x hx y hy hxy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ioo] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have hRl : scaleR s0 (k + j) ≤ scaleR s0 k := by
      unfold scaleR; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpk : scaleR s0 k ≤ strokeLen s0 m k := by unfold strokeLen; nlinarith [scaleR_pos s0 k]
    by_cases hα : x.1 = y.1
    · exact Prod.ext hα (by omega)
    · have := periodVApices_spans_disjoint hk1 (by omega) hms hx.1 hy.1 hα
      omega

/-- **Lemma 7.7(a)**: each family has at least `1/32` of the `4Λ` hops of a class in one period. -/
theorem family_card_ge {s0 m k f : ℕ} (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hms : m < s0) (hf : f < 4) :
    4 * 2 ^ s0 ≤ 32 * (family s0 m k f).card := by
  have hΛ : 2 ^ s0 = 2 ^ k * scaleR s0 k := by unfold scaleR; rw [← pow_add]; congr 1; omega
  have hRpos : ∀ i, i ≤ m → 2 ≤ scaleR s0 i := fun i hi => by
    unfold scaleR; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (show 1 ≤ s0 - i by omega))
  unfold family
  split_ifs with hf0
  · rw [card_apexFamily hk1 (by omega) hms.le, hΛ, pow_succ]
    have := hRpos k (by omega)
    have h2 : 2 ^ k * scaleR s0 k ≤ 2 ^ k * (16 * (scaleR s0 k - 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · set j := f - 1 with hj
    rw [card_bandFamily hk1 (by omega) hms.le, hΛ, pow_succ]
    have hRk : scaleR s0 k = 2 ^ j * scaleR s0 (k + j) := by
      unfold scaleR; rw [← pow_add]; congr 1; omega
    unfold scaleBelow
    split_ifs with hl
    · have hRl : scaleR s0 (k + j) = 2 * scaleR s0 (k + j + 1) := scaleR_succ (by omega)
      have h2 := hRpos (k + j + 1) (by omega)
      have hj2 : 2 ^ j ≤ 4 := by
        calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      rw [hRk, hRl]
      set R' := scaleR s0 (k + j + 1)
      have hH : 2 ^ j * (2 * R') ≤ 16 * (R' - 1) := by
        have h4 := Nat.mul_le_mul_right (2 * R') hj2; omega
      have hsub : 2 * R' - R' - 1 = R' - 1 := by omega
      calc 4 * (2 ^ k * (2 ^ j * (2 * R'))) = 4 * 2 ^ k * (2 ^ j * (2 * R')) := by ring
        _ ≤ 4 * 2 ^ k * (16 * (R' - 1)) := Nat.mul_le_mul_left _ hH
        _ = 32 * (2 ^ k * 2 * (2 * R' - R' - 1)) := by rw [hsub]; ring
    · have h2 := hRpos (k + j) (by omega)
      have hj2 : 2 ^ j ≤ 4 := by
        calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      rw [hRk]
      set R' := scaleR s0 (k + j)
      have hH : 2 ^ j * R' ≤ 16 * (R' - 1) := by
        have h4 := Nat.mul_le_mul_right R' hj2; omega
      calc 4 * (2 ^ k * (2 ^ j * R')) = 4 * 2 ^ k * (2 ^ j * R') := by ring
        _ ≤ 4 * 2 ^ k * (16 * (R' - 1)) := Nat.mul_le_mul_left _ hH
        _ = 32 * (2 ^ k * 2 * (R' - 0 - 1)) := by rw [Nat.sub_zero]; ring


theorem blockPotential_eq_of_blind {s0 m : ℕ} (hms : m ≤ s0) (a : ℕ) (K : ℤ) {c p u : ℤ}
    (hpu : p ≤ u) (h : TurnFree s0 m c p u) :
    blockPotential s0 m a K (u + c) = blockPotential s0 m a K (p + c) :=
  turnPotential_eq_of_turnFree hms _ _ _ hpu h

theorem family_fst_le_snd {s0 m k f : ℕ} {η : ℤ × ℤ} (hη : η ∈ family s0 m k f) : η.1 ≤ η.2 := by
  unfold family apexFamily bandFamily at hη
  split_ifs at hη
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hη; simp only; omega
  · obtain ⟨x, -, rfl⟩ := mem_image.mp hη
    simp only
    have h1 := Nat.cast_nonneg (α := ℤ) ((m - (k + (f - 1))) * scaleR s0 (k + (f - 1)))
    have h2 : ((x.1 + strokeLen s0 m k + x.2 : ℕ) : ℤ) = ((x.1 + strokeLen s0 m k : ℕ) : ℤ) + x.2 := by
      push_cast; ring
    rw [h2]; omega

/-- The single-head error of a hop of a family is its blind error. -/
theorem singleHead_family {s0 m k f : ℕ} (hms : m < s0) (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4)
    (a : ℕ) (K q : ℤ) {η : ℤ × ℤ} (hη : η ∈ family s0 m k f) :
    (blockPotential s0 m a K η.2 - blockPotential s0 m a K η.1 - 1) % q = familyBlindErr m a K q k f := by
  unfold family at hη
  unfold familyBlindErr blockPotential
  split_ifs at hη ⊢ with hf0
  · obtain ⟨⟨α, d⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Icc] at hx
    have hRk := scaleR_pos s0 k
    rw [turnPotential_apex hk1 (by omega) hms.le _ _ 1 hx.1 hx.2.1 (by omega)]
    rfl
  · obtain ⟨⟨α, x⟩, hx, rfl⟩ := mem_image.mp hη
    rw [mem_product, mem_Ioo] at hx
    simp only
    rw [turnPotential_band hk1 (by omega : k ≤ k + (f - 1)) (by omega) hms.le _ _ 1 hx.1
      (by omega) hx.2.2]
    rfl

/-- **Lemma 7.7(b)**: every blind hop of a family carries the blind error of the family (for the
label of its own head). -/
theorem pairHopErr_of_blind {s0 m a1 a2 : ℕ} (K1 K2 q ξ : ℤ) (hms : m < s0) {k f : ℕ} (hk1 : 1 ≤ k)
    (hkm : k + 2 ≤ m) (hf : f < 4) (h : Bool) {η : ℤ × ℤ} (hη : η ∈ family s0 m k f)
    (hbl : BlindHop s0 m ξ h η.1 η.2) :
    pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 =
      familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f := by
  have hle := family_fst_le_snd hη
  unfold BlindHop at hbl
  cases h
  · simp only [Bool.false_eq_true, ↓reduceIte] at hbl ⊢
    unfold pairHopErr
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [blockPotential_eq_of_blind hms.le a1 K1 hle hbl, sub_self, add_zero]
    exact singleHead_family hms hk1 hkm hf a2 K2 q hη
  · simp only [↓reduceIte] at hbl ⊢
    unfold pairHopErr
    simp only [↓reduceIte]
    rw [blockPotential_eq_of_blind hms.le a2 K2 hle hbl, sub_self, add_zero]
    exact singleHead_family hms hk1 hkm hf a1 K1 q hη

theorem pairHopErr_nonneg (s0 m a1 a2 : ℕ) (K1 K2 : ℤ) {q : ℤ} (hq : 0 < q) (ξ : ℤ) (h : Bool)
    (p u : ℤ) : 0 ≤ pairHopErr s0 m a1 a2 K1 K2 q ξ h p u := by
  unfold pairHopErr; split_ifs <;> exact Int.emod_nonneg _ hq.ne'

theorem family_subset_witness {s0 m k f : ℕ} (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4) :
    family s0 m k f ⊆ witnessHops s0 m k := by
  unfold witnessHops
  rw [ite_eq_left ⟨hk1, hkm⟩]
  exact Finset.subset_biUnion_of_mem (family s0 m k) (mem_range.mpr hf)

theorem sum_family_le_witnessErr {s0 m a1 a2 : ℕ} {K1 K2 q : ℤ} (hq : 0 < q) (ξ : ℤ) (h : Bool)
    {k f : ℕ} (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4) (B : Finset (ℤ × ℤ))
    (hB : B ⊆ family s0 m k f) :
    ∑ η ∈ B, pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 ≤ witnessErr s0 m a1 a2 K1 K2 q ξ h k :=
  Finset.sum_le_sum_of_subset_of_nonneg (hB.trans (family_subset_witness hk1 hkm hf))
    fun _ _ _ => pairHopErr_nonneg s0 m a1 a2 K1 K2 hq ξ h _ _

/-- **Lemma 7.7(c)**: if level `k` is `θ`-served for head `h` (on its witness hops) and family `f`
is half-blind at `ξ`, the common error of its blind hops is at most `64 θ q`. -/
theorem familyBlindErr_le_of_served {s0 m a1 a2 : ℕ} {K1 K2 q ξ : ℤ} {θ : ℝ} (hms : m < s0)
    (hq : 0 < q) {h : Bool} {k f : ℕ} (hk1 : 1 ≤ k) (hkm : k + 2 ≤ m) (hf : f < 4)
    (hserv : ServedOnWitness s0 m a1 a2 K1 K2 q ξ θ h k) (hhb : HalfBlind s0 m ξ h k f) :
    (familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f : ℝ) ≤ 64 * θ * q := by
  set e := familyBlindErr m (if h then a1 else a2) (if h then K1 else K2) q k f with he
  set B := (family s0 m k f).filter fun η => BlindHop s0 m ξ h η.1 η.2
  have he0 : 0 ≤ e := by
    rw [he]; unfold familyBlindErr
    split_ifs <;> first | exact blindApexErr_nonneg _ hq _ | exact blindBandErr_nonneg _ _ hq _ _
  have hsum : ∑ η ∈ B, pairHopErr s0 m a1 a2 K1 K2 q ξ h η.1 η.2 = B.card * e := by
    rw [Finset.sum_congr rfl fun η hη => pairHopErr_of_blind K1 K2 q ξ hms hk1 hkm hf h
      (Finset.mem_filter.mp hη).1 (Finset.mem_filter.mp hη).2, Finset.sum_const, nsmul_eq_mul]
  have hle := sum_family_le_witnessErr (a1 := a1) (a2 := a2) (K1 := K1) (K2 := K2) hq ξ h hk1 hkm hf
    B (Finset.filter_subset _ _)
  rw [hsum] at hle
  have hleR : (B.card : ℝ) * e ≤ θ * q * (4 * 2 ^ s0) := by
    have : ((B.card * e : ℤ) : ℝ) ≤ (witnessErr s0 m a1 a2 K1 K2 q ξ h k : ℝ) := by exact_mod_cast hle
    push_cast at this; unfold ServedOnWitness at hserv; linarith
  have hcard := family_card_ge (f := f) hk1 hkm hms hf
  have hB2 : (4 * 2 ^ s0 : ℝ) ≤ 64 * B.card := by
    have h2 : ((family s0 m k f).card : ℝ) ≤ 2 * B.card := by exact_mod_cast hhb
    have h32 : (4 * 2 ^ s0 : ℝ) ≤ 32 * (family s0 m k f).card := by exact_mod_cast hcard
    linarith
  have hΛ : (0 : ℝ) < 4 * 2 ^ s0 := by positivity
  have he0R : (0 : ℝ) ≤ e := by exact_mod_cast he0
  have : (4 * 2 ^ s0 : ℝ) * e ≤ (4 * 2 ^ s0) * (64 * θ * q) := by nlinarith
  exact le_of_mul_le_mul_left this hΛ

end MergeDepth
