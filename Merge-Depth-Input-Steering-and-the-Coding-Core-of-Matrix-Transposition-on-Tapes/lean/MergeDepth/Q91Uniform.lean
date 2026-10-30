import MergeDepth.Q91
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The uniformity argument of the fifth paper's Proposition 9.2

[Q9.1] is a statement about sequences. Its applications need a bound that holds at every large
size, uniformly over a family of relations. The fifth paper's Proposition 9.2 obtains it by
contradiction: a violating family yields a violating sequence. This file proves that argument once,
for an abstract family of *instances*: a predicate `Good d b Q N` on retained coordinate sets
`Q ⊆ [0, d² b)` and relations `N` on `[0, d² b)`; the relation used is the induced relation
`N_Q = inducedNeighborhood N Q` on `Q`.

Hypotheses on the family (all uniform over its instances):
* `hdeg`: the incidence graphs of the induced relations have maximum degree at most `Δ`;
* `hcard`: from some `d₁` on, `|Q| ≥ κ d² b` for a fixed `κ > 0`;
* `hshort`: for every radius `r > 0` there are `A_r` and `d_r` with at most `A_r d² b / log₂ d`
  coordinates of `Q` at paired distance at most `r` in the incidence graph of `N_Q`, for `d ≥ d_r`.

`seq_hyps` shows that every sequence of instances with `d_j ≥ j` satisfies the hypotheses of
Question 9.1. `uniform_rate_binary` (from binary [Q9.1]) and `uniform_rate` (from [Q9.1], all
alphabets, uniformly over the alphabet) give: for every `ε > 0` there is `d₀` such that at every
`d ≥ d₀`, for every width `b` and every instance, every storage code for `N_Q` has
`log_{|𝒜|} |𝒞| ≤ (1/2 + ε) |Q|`. The width `b` is arbitrary: the threshold does not depend on it.
-/

namespace MergeDepth

open Filter Topology DirectedRecovery MotionDepthCodes Finset

set_option autoImplicit false

/-- A family of instances: for every dimension `d` and width `b`, a predicate on a retained set `Q`
and a relation `N` on `Fin (d * d * b)`. -/
abbrev InstFamily : Type :=
  (d b : ℕ) → Finset (Fin (d * d * b)) → (Fin (d * d * b) → Finset (Fin (d * d * b))) → Prop

open Classical in
/-- **A sequence of instances satisfies the hypotheses of Question 9.1.** Along `d_j ≥ j`, the
induced relations have `|Q_j| → ∞`, incidence degree at most `Δ` and the paired-distance
condition. -/
theorem seq_hyps (Good : InstFamily) (Δ : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ d b Q N, Good d b Q N → 1 ≤ b)
    (hdeg : ∀ d b Q N, Good d b Q N →
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ)
    (hcard : ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b Q N, Good d b Q N → κ * (d * d * b : ℕ) ≤ Q.card)
    (hshort : ∀ r : ℕ, 0 < r → ∃ (A : ℝ) (d₁ : ℕ), ∀ d ≥ d₁, ∀ b Q N, Good d b Q N →
      ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
        A * ((d * d * b : ℕ) / Real.logb 2 d))
    (dd bb : ℕ → ℕ) (hdd : ∀ j, j ≤ dd j) (QQ : (j : ℕ) → Finset (Fin (dd j * dd j * bb j)))
    (NN : (j : ℕ) → Fin (dd j * dd j * bb j) → Finset (Fin (dd j * dd j * bb j)))
    (hgood : ∀ j, Good (dd j) (bb j) (QQ j) (NN j)) :
    Tendsto (fun j => Fintype.card (QQ j)) atTop atTop ∧
      (∀ j v, (pairedIncidenceGraph (inducedNeighborhood (NN j) (QQ j))).degree v ≤ Δ) ∧
      HasPairedDistanceSeparation (fun j => inducedNeighborhood (NN j) (QQ j)) := by
  obtain ⟨d₁, hd₁⟩ := hcard
  -- the volume grows at least like the index
  have hvol : ∀ j : ℕ, (j : ℝ) ≤ ((dd j * dd j * bb j : ℕ) : ℝ) := by
    intro j
    have h1 := hb _ _ _ _ (hgood j)
    have h2 := hdd j
    have : j ≤ dd j * dd j * bb j := by
      rcases Nat.eq_zero_or_pos (dd j) with h0 | hpos
      · omega
      · calc j ≤ dd j := h2
          _ ≤ dd j * dd j := Nat.le_mul_of_pos_right _ hpos
          _ ≤ dd j * dd j * bb j := Nat.le_mul_of_pos_right _ (by omega)
    exact_mod_cast this
  have hQcard : ∀ j : ℕ, d₁ ≤ j → κ * j ≤ ((QQ j).card : ℝ) := fun j hj =>
    le_trans (mul_le_mul_of_nonneg_left (hvol j) hκ.le) (hd₁ _ (le_trans hj (hdd j)) _ _ _ (hgood j))
  have hddt : Tendsto dd atTop atTop := tendsto_atTop_mono hdd tendsto_id
  refine ⟨?_, fun j => hdeg _ _ _ _ (hgood j), ?_⟩
  · -- `|Q_j| → ∞`
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop d₁, eventually_ge_atTop ⌈(m : ℝ) / κ⌉₊] with j hj hjm
    rw [Fintype.card_coe]
    have h1 := hQcard j hj
    have h2 : (m : ℝ) / κ ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hjm)
    have h3 : (m : ℝ) ≤ κ * j := by rw [div_le_iff₀ hκ] at h2; linarith
    exact_mod_cast h3.trans h1
  · -- the paired-distance condition
    intro K hK
    obtain ⟨A, d₂, hA⟩ := hshort K hK
    set A' := max A 0
    have hlog : Tendsto (fun j => Real.logb 2 (dd j : ℝ)) atTop atTop :=
      (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_natCast_atTop_atTop.comp hddt)
    have hlim : Tendsto (fun j => A' / (κ * Real.logb 2 (dd j : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hlog.const_mul_atTop hκ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun j => by positivity) ?_
    filter_upwards [eventually_ge_atTop d₁, eventually_ge_atTop d₂, eventually_ge_atTop 2]
      with j hj1 hj2 hj3
    rw [Fintype.card_coe]
    have hd2 : 2 ≤ dd j := le_trans hj3 (hdd j)
    have hlogpos : 0 < Real.logb 2 (dd j : ℝ) :=
      Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < dd j))
    have hL : (0 : ℝ) < ((dd j * dd j * bb j : ℕ) : ℝ) := by
      have := hvol j
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj3
      linarith
    have hQ : κ * ((dd j * dd j * bb j : ℕ) : ℝ) ≤ (QQ j).card :=
      hd₁ _ (le_trans hj1 (hdd j)) _ _ _ (hgood j)
    have hQpos : (0 : ℝ) < (QQ j).card := lt_of_lt_of_le (by positivity) hQ
    have hs := hA _ (le_trans hj2 (hdd j)) _ _ _ (hgood j)
    have hs' : ((shortPairedCoordinates (inducedNeighborhood (NN j) (QQ j)) K).card : ℝ) *
        Real.logb 2 (dd j : ℝ) ≤ A' * ((dd j * dd j * bb j : ℕ) : ℝ) := by
      have h1 : A * (((dd j * dd j * bb j : ℕ) : ℝ) / Real.logb 2 (dd j : ℝ)) ≤
          A' * (((dd j * dd j * bb j : ℕ) : ℝ) / Real.logb 2 (dd j : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h4 : A' * (((dd j * dd j * bb j : ℕ) : ℝ) / Real.logb 2 (dd j : ℝ)) *
          Real.logb 2 (dd j : ℝ) = A' * ((dd j * dd j * bb j : ℕ) : ℝ) := by
        field_simp
      calc ((shortPairedCoordinates (inducedNeighborhood (NN j) (QQ j)) K).card : ℝ) *
            Real.logb 2 (dd j : ℝ)
          ≤ A' * (((dd j * dd j * bb j : ℕ) : ℝ) / Real.logb 2 (dd j : ℝ)) *
            Real.logb 2 (dd j : ℝ) := mul_le_mul_of_nonneg_right (hs.trans h1) hlogpos.le
        _ = A' * ((dd j * dd j * bb j : ℕ) : ℝ) := h4
    rw [div_le_div_iff₀ hQpos (by positivity)]
    have hA'0 : 0 ≤ A' := le_max_right _ _
    calc ((shortPairedCoordinates (inducedNeighborhood (NN j) (QQ j)) K).card : ℝ) *
          (κ * Real.logb 2 (dd j : ℝ))
        = κ * (((shortPairedCoordinates (inducedNeighborhood (NN j) (QQ j)) K).card : ℝ) *
            Real.logb 2 (dd j : ℝ)) := by ring
      _ ≤ κ * (A' * ((dd j * dd j * bb j : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hs' hκ.le
      _ = A' * (κ * ((dd j * dd j * bb j : ℕ) : ℝ)) := by ring
      _ ≤ A' * (QQ j).card := mul_le_mul_of_nonneg_left hQ hA'0

open Classical in
/-- **The uniformity argument, binary codes.** Given binary [Q9.1] and a family of instances as in
`seq_hyps`, for every `ε > 0` there is `d₀` such that at every `d ≥ d₀`, for every width `b` and
every instance `(Q, N)`, every binary storage code for `N_Q` has `log₂ |𝒞| ≤ (1/2 + ε) |Q|`. -/
theorem uniform_rate_binary (hQ : Q91Binary) (Good : InstFamily) (Δ : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ d b Q N, Good d b Q N → 1 ≤ b)
    (hdeg : ∀ d b Q N, Good d b Q N →
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ)
    (hcard : ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b Q N, Good d b Q N → κ * (d * d * b : ℕ) ≤ Q.card)
    (hshort : ∀ r : ℕ, 0 < r → ∃ (A : ℝ) (d₁ : ℕ), ∀ d ≥ d₁, ∀ b Q N, Good d b Q N →
      ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
        A * ((d * d * b : ℕ) / Real.logb 2 d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b Q N, Good d b Q N → ∀ C : Finset (Q → Bool),
      IsStorageCode (inducedNeighborhood N Q) C → Real.logb 2 C.card ≤ (1 / 2 + ε) * Q.card := by
  by_contra hcon
  push Not at hcon
  choose dd hdd bb QQ NN hgood CC hCC hbig using hcon
  obtain ⟨hsize, hdeg', hsep⟩ := seq_hyps Good Δ hκ hb hdeg hcard hshort dd bb hdd QQ NN hgood
  have hne : ∀ j, (CC j).Nonempty := by
    intro j
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := hbig j
    rw [he, Finset.card_empty, Nat.cast_zero, Real.logb_zero] at this
    have : (0 : ℝ) ≤ (1 / 2 + ε) * (QQ j).card := by positivity
    linarith
  have hev := (hQ Δ).eventually (fun j => (QQ j : Type)) (fun j => inducedNeighborhood (NN j) (QQ j))
    hsize hdeg' hsep CC hCC hne (half_pos hε)
  obtain ⟨j, hj1, hj2⟩ := (hev.and (hsize.eventually_gt_atTop 0)).exists
  have hb' := hbig j
  rw [Fintype.card_coe] at hj2
  have hpos : (0 : ℝ) < (QQ j).card := by exact_mod_cast hj2
  unfold storageCodeRate at hj1
  rw [Fintype.card_bool, Fintype.card_coe, Nat.cast_ofNat, div_le_iff₀ hpos] at hj1
  nlinarith

open Classical in
/-- **The uniformity argument, all alphabets.** Given [Q9.1] for all alphabets, the threshold `d₀`
works for every finite alphabet with at least two letters at once. -/
theorem uniform_rate (hQ : Q91) (Good : InstFamily) (Δ : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ d b Q N, Good d b Q N → 1 ≤ b)
    (hdeg : ∀ d b Q N, Good d b Q N →
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N Q)).degree v ≤ Δ)
    (hcard : ∃ d₁ : ℕ, ∀ d ≥ d₁, ∀ b Q N, Good d b Q N → κ * (d * d * b : ℕ) ≤ Q.card)
    (hshort : ∀ r : ℕ, 0 < r → ∃ (A : ℝ) (d₁ : ℕ), ∀ d ≥ d₁, ∀ b Q N, Good d b Q N →
      ((shortPairedCoordinates (inducedNeighborhood N Q) r).card : ℝ) ≤
        A * ((d * d * b : ℕ) / Real.logb 2 d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ b Q N, Good d b Q N → ∀ (A : Type) [Fintype A],
      2 ≤ Fintype.card A → ∀ C : Finset (Q → A), IsStorageCode (inducedNeighborhood N Q) C →
        Real.logb (Fintype.card A) C.card ≤ (1 / 2 + ε) * Q.card := by
  by_contra hcon
  push Not at hcon
  choose dd hdd bb QQ NN hgood AA instA hA CC hCC hbig using hcon
  obtain ⟨hsize, hdeg', hsep⟩ := seq_hyps Good Δ hκ hb hdeg hcard hshort dd bb hdd QQ NN hgood
  have hne : ∀ j, (CC j).Nonempty := by
    intro j
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := hbig j
    rw [he, Finset.card_empty, Nat.cast_zero, Real.logb_zero] at this
    have : (0 : ℝ) ≤ (1 / 2 + ε) * (QQ j).card := by positivity
    linarith
  have hev := (hQ Δ).eventually (fun j => (QQ j : Type)) (fun j => inducedNeighborhood (NN j) (QQ j))
    hsize hdeg' hsep AA hA CC hCC hne (half_pos hε)
  obtain ⟨j, hj1, hj2⟩ := (hev.and (hsize.eventually_gt_atTop 0)).exists
  have hb' := hbig j
  rw [Fintype.card_coe] at hj2
  have hpos : (0 : ℝ) < (QQ j).card := by exact_mod_cast hj2
  unfold storageCodeRate at hj1
  rw [Fintype.card_coe, div_le_iff₀ hpos] at hj1
  nlinarith

/-! ### Paid conditioning in logarithmic form -/

/-- **Paid conditioning, logarithmic form** (the fifth paper's Lemma 2.2, Lean-verified there as
`storageCode_conditioning_bound`): if every storage code for the induced relation on `Q` has
`log_a |𝒟| ≤ u`, then every storage code for `N` has `log_a |𝒞| ≤ |V ∖ Q| + u`. -/
theorem logb_card_le_of_conditioning {V α : Type*} [DecidableEq V] [Fintype V] [Fintype α]
    (hα : 2 ≤ Fintype.card α) {N : V → Finset V} {C : Finset (V → α)} (hC : IsStorageCode N C)
    (Q : Finset V) {u : ℝ}
    (hu : ∀ D : Finset (Q → α), IsStorageCode (inducedNeighborhood N Q) D →
      Real.logb (Fintype.card α) D.card ≤ u) :
    Real.logb (Fintype.card α) C.card ≤ (Qᶜ.card : ℝ) + u := by
  have ha1 : (1 : ℝ) < Fintype.card α := by exact_mod_cast hα
  have ha0 : (0 : ℝ) < Fintype.card α := by linarith
  -- `u ≥ 0`, by the empty code
  have hu0 : 0 ≤ u := by
    have h := hu ∅ (fun x hx => by simp at hx)
    simpa using h
  have hbound : ∀ D : Finset (Q → α), IsStorageCode (inducedNeighborhood N Q) D →
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ u := by
    intro D hD
    rcases Nat.eq_zero_or_pos D.card with h0 | hpos
    · rw [h0, Nat.cast_zero]
      positivity
    · exact (Real.logb_le_iff_le_rpow ha1 (by exact_mod_cast hpos)).mp (hu D hD)
  have hC' := storageCode_conditioning_bound hC Q ha0 hbound
  have hcompl : Fintype.card {v // v ∉ Q} = Qᶜ.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  rw [hcompl] at hC'
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    positivity
  · exact (Real.logb_le_iff_le_rpow ha1 (by exact_mod_cast hpos)).mpr hC'

/-- The arithmetic of the conditioning step: with `|Qᶜ| = L - |Q|` and a rate `1/2 + ζ` on `Q`,
`|Qᶜ| + (1/2 + ζ) |Q| ≤ (1/2 + ζ) L + |Qᶜ|/2`. -/
theorem conditioning_arith {L q h ζ : ℝ} (hζ : 0 ≤ ζ) (hh : 0 ≤ h) (hqh : q + h = L) :
    h + (1 / 2 + ζ) * q ≤ (1 / 2 + ζ) * L + h / 2 := by
  have : q = L - h := by linarith
  subst this
  nlinarith

end MergeDepth
