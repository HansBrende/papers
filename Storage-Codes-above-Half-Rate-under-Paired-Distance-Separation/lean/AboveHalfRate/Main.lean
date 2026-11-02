import AboveHalfRate.Descent
import AboveHalfRate.BlowUp
import Mathlib.FieldTheory.Finiteness

/-!
# Question 9.1 from a tower of twisted quotients

The formal part of Theorem T(b) and (c) of the paper, used for Theorem A and Corollary A′. The
input is a check system on coordinates `P` with an action of `Γ` (`AboveHalfRate.Descent`), balls
of radius `R` of size at most `β`, and a tower of subgroups `Γs n` whose quotients are finite of
size tending to infinity, whose nontrivial elements move every coordinate by at least `s n → ∞`,
and which carry linear codes annihilated by the descended checks, of dimension at least `ρ` times
their length, with `ρ > 1/2`.

* `hasPairedDistanceSeparation_of_eventually`: the paired-distance condition holds as soon as, for
  every radius, eventually no coordinate is short.
* `not_Q91At_of_tower`: under these hypotheses Question 9.1 of the fifth paper has a negative
  answer at the degree bound `β - 1` (`¬ MergeDepth.Q91At (β - 1)`).
* `not_Q91BinaryAt_of_tower`: if moreover `ι : 𝔽 → (Fin b → Bool)` is injective and
  `ρ log₂ |𝔽| / b > 1/2`, it has a negative answer for binary codes at the degree bound
  `b (β - 1)`.

In the paper the check system comes from the peeling lemma (`AboveHalfRate.Peeling`) on the
Bruhat–Tits tree, the codes are the Goren–Oort Tanner codes, whose annihilation by the checks is
`AboveHalfRate.Tanner`, and their dimension is the arithmetic input, which is not formalized.
-/

namespace AboveHalf

open Filter Finset DirectedRecovery MotionDepthCodes MergeDepth

set_option autoImplicit false

/-- The paired-distance condition holds if, for every radius `K`, eventually no coordinate has its
two ports within distance `K`. -/
theorem hasPairedDistanceSeparation_of_eventually {V : ℕ → Type} [∀ n, Fintype (V n)] (N : (n : ℕ) → V n → Finset (V n))
    (h : ∀ K : ℕ, 0 < K → ∀ᶠ n in atTop,
      ∀ z, ¬ (pairedIncidenceGraph (N n)).edist (Sum.inl z) (Sum.inr z) ≤ K) :
    HasPairedDistanceSeparation N := by
  intro K hK
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h K hK] with n hn
  have : shortPairedCoordinates (N n) K = ∅ := by
    ext z
    simp only [shortPairedCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact hn z
  rw [this, Finset.card_empty, Nat.cast_zero, zero_div]

/-- The code of all words of a subspace, as a finite set of words. -/
noncomputable def wordsOf {W 𝔽 : Type} [Fintype W] [DecidableEq W] [Field 𝔽] [Fintype 𝔽]
    (C : Submodule 𝔽 (W → 𝔽)) : Finset (W → 𝔽) := by
  classical exact Finset.univ.filter (· ∈ C)

theorem mem_wordsOf {W 𝔽 : Type} [Fintype W] [DecidableEq W] [Field 𝔽] [Fintype 𝔽]
    {C : Submodule 𝔽 (W → 𝔽)} {c : W → 𝔽} : c ∈ wordsOf C ↔ c ∈ C := by
  classical
  unfold wordsOf
  simp

theorem card_wordsOf {W 𝔽 : Type} [Fintype W] [DecidableEq W] [Field 𝔽] [Fintype 𝔽]
    (C : Submodule 𝔽 (W → 𝔽)) :
    (wordsOf C).card = Fintype.card 𝔽 ^ Module.finrank 𝔽 C := by
  classical
  rw [← Module.card_eq_pow_finrank (K := 𝔽) (V := C), ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun c => mem_wordsOf)

/-- The rate of the code of all words of a subspace is its dimension over its length. -/
theorem storageCodeRate_wordsOf {W 𝔽 : Type} [Fintype W] [DecidableEq W] [Field 𝔽] [Fintype 𝔽]
    (C : Submodule 𝔽 (W → 𝔽)) :
    storageCodeRate (wordsOf C) = (Module.finrank 𝔽 C : ℝ) / Fintype.card W := by
  unfold storageCodeRate
  rw [card_wordsOf, Nat.cast_pow]
  have h1 : (1 : ℝ) < Fintype.card 𝔽 := by exact_mod_cast Fintype.one_lt_card
  rw [Real.logb_pow, Real.logb_self_eq_one h1, mul_one]

variable {P : Type} [DecidableEq P] {Γ : Type*} [Group Γ] [MulAction Γ P]
variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽]

section Tower

variable (S : CheckSystem P Γ 𝔽) (ball : P → Finset P)
  (hball : ∀ p x, x ∈ ball p ↔ S.dist p x ≤ S.R) {β : ℕ} (hβ : ∀ p, (ball p).card ≤ β)
  (Γs : ℕ → Subgroup Γ) [∀ n, Fintype (Quo (Γs n) P)]
  (s : ℕ → ℕ) (hdisp : ∀ n, ∀ γ ∈ Γs n, γ ≠ 1 → ∀ p, s n ≤ S.dist p (γ • p))
  (hs : Tendsto s atTop atTop)
  (hsize : Tendsto (fun n => Fintype.card (Quo (Γs n) P)) atTop atTop)
  (C : ∀ n, Submodule 𝔽 (Quo (Γs n) P → 𝔽))
  (hann : ∀ n, ∀ c ∈ C n, ∀ p,
    ∑ y ∈ (S.check p).support, S.check p y * c (proj (Γs n) y) = 0)
  {ρ : ℝ} (hdim : ∀ n, ρ * Fintype.card (Quo (Γs n) P) ≤ Module.finrank 𝔽 (C n))

omit [Fintype 𝔽] in
include hball hβ in
/-- Both incidence degrees of the descended relations are at most `β - 1`. -/
theorem degree_qrel_le [∀ n, DecidableEq (Quo (Γs n) P)] (n : ℕ)
    (v : Quo (Γs n) P ⊕ Quo (Γs n) P)
    [Fintype ((pairedIncidenceGraph (S.qrel (Γs n))).neighborSet v)] :
    (pairedIncidenceGraph (S.qrel (Γs n))).degree v ≤ β - 1 := by
  refine degree_le_of_bounds _ (fun z => ?_) (fun z => ?_) v
  · induction z using Quotient.inductionOn' with
    | h p => exact S.card_qrel_le ball hball hβ p
  · induction z using Quotient.inductionOn' with
    | h p => exact S.card_in_qrel_le ball hball hβ p

omit [Fintype 𝔽] [∀ n, Fintype (Quo (Γs n) P)] in
include hdisp hs in
/-- For every radius, eventually no coordinate of the descended relations is short. -/
theorem eventually_not_short [∀ n, DecidableEq (Quo (Γs n) P)] (K : ℕ) :
    ∀ᶠ n in atTop, ∀ z : Quo (Γs n) P,
      ¬ (pairedIncidenceGraph (S.qrel (Γs n))).edist (Sum.inl z) (Sum.inr z) ≤ K := by
  filter_upwards [hs.eventually_gt_atTop (S.R * K)] with n hn z hz
  have := S.le_mul_of_edist_le (hdisp n) z hz
  omega

include hball hβ hdisp hs hsize hann hdim in
/-- **Theorem T(b), formal part.** A tower of twisted quotients carrying codes of rate `ρ > 1/2`
gives a negative answer to Question 9.1 at the degree bound `β - 1`. -/
theorem not_Q91At_of_tower [∀ n, DecidableEq (Quo (Γs n) P)] (hρ : 1 / 2 < ρ) :
    ¬ Q91At (β - 1) := by
  classical
  intro hQ
  have hsep : HasPairedDistanceSeparation (fun n => S.qrel (Γs n)) :=
    hasPairedDistanceSeparation_of_eventually _ fun K _ =>
      eventually_not_short S Γs s hdisp hs K
  have hstore : ∀ n, IsStorageCode (S.qrel (Γs n)) (wordsOf (C n)) := fun n =>
    S.isStorageCode_qrel (wordsOf (C n)) fun c hc p => hann n c (mem_wordsOf.1 hc) p
  have hne : ∀ n, (wordsOf (C n)).Nonempty := fun n => ⟨0, mem_wordsOf.2 (C n).zero_mem⟩
  have hA : ∀ _n : ℕ, 2 ≤ Fintype.card 𝔽 := fun _ => Fintype.one_lt_card
  have hε : 0 < (ρ - 1 / 2) / 2 := by linarith
  obtain ⟨n, hn, hpos⟩ := ((hQ.eventually (fun n => Quo (Γs n) P) (fun n => S.qrel (Γs n)) hsize
    (fun n v => degree_qrel_le S ball hball hβ Γs n v) hsep (fun _ => 𝔽) hA
    (fun n => wordsOf (C n)) hstore hne hε).and
    (hsize.eventually_gt_atTop 0)).exists
  have hpos' : (0 : ℝ) < Fintype.card (Quo (Γs n) P) := by exact_mod_cast hpos
  have hge : ρ ≤ storageCodeRate (wordsOf (C n)) := by
    rw [storageCodeRate_wordsOf, le_div_iff₀ hpos']
    exact hdim n
  linarith

include hball hβ hdisp hs hsize hann hdim in
/-- **Theorem T(c), formal part.** With an injective encoding `ι : 𝔽 → (Fin b → Bool)` and
`ρ log₂ |𝔽| / b > 1/2`, the binary blow-up gives a negative answer to Question 9.1 for binary codes
at the degree bound `b (β - 1)`. -/
theorem not_Q91BinaryAt_of_tower [∀ n, DecidableEq (Quo (Γs n) P)] {b : ℕ}
    (ι : 𝔽 → Fin b → Bool) (hι : Function.Injective ι)
    (hρb : 1 / 2 < ρ * Real.logb 2 (Fintype.card 𝔽) / b) : ¬ Q91BinaryAt (b * (β - 1)) := by
  classical
  intro hQ
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, Nat.cast_zero, div_zero] at hρb; linarith
    · exact h
  have hsizeb : Tendsto (fun n => Fintype.card (Quo (Γs n) P × Fin b)) atTop atTop := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact hsize.atTop_mul_const' hb
  have hout : ∀ n (z : Quo (Γs n) P), (S.qrel (Γs n) z).card ≤ β - 1 := by
    intro n z
    induction z using Quotient.inductionOn' with
    | h p => exact S.card_qrel_le ball hball hβ p
  have hin : ∀ n (z : Quo (Γs n) P),
      (Finset.univ.filter (fun z' => z ∈ S.qrel (Γs n) z')).card ≤ β - 1 := by
    intro n z
    induction z using Quotient.inductionOn' with
    | h p => exact S.card_in_qrel_le ball hball hβ p
  have hsep : HasPairedDistanceSeparation (fun n => blowUp (S.qrel (Γs n)) b) := by
    refine hasPairedDistanceSeparation_of_eventually _ fun K _ => ?_
    filter_upwards [eventually_not_short S Γs s hdisp hs K] with n hn x hx
    exact hn x.1 ((edist_le_blowUp _ x).trans hx)
  have hstore : ∀ n, IsStorageCode (blowUp (S.qrel (Γs n)) b) (blowCode ι (wordsOf (C n))) :=
    fun n => isStorageCode_blowCode
      (S.isStorageCode_qrel (wordsOf (C n)) fun c hc p => hann n c (mem_wordsOf.1 hc) p) hι
  have hne : ∀ n, (blowCode ι (wordsOf (C n))).Nonempty := fun n => by
    unfold blowCode
    exact Finset.image_nonempty.2 ⟨0, mem_wordsOf.2 (C n).zero_mem⟩
  have hε : 0 < (ρ * Real.logb 2 (Fintype.card 𝔽) / b - 1 / 2) / 2 := by linarith
  obtain ⟨n, hn, hpos⟩ := ((hQ.eventually (fun n => Quo (Γs n) P × Fin b)
    (fun n => blowUp (S.qrel (Γs n)) b) hsizeb
    (fun n v => degree_blowUp_le _ (hout n) (hin n) v) hsep (fun n => blowCode ι (wordsOf (C n)))
    hstore hne hε).and (hsize.eventually_gt_atTop 0)).exists
  have hq : (1 : ℝ) < Fintype.card 𝔽 := by exact_mod_cast Fintype.one_lt_card
  have hrate : storageCodeRate (blowCode ι (wordsOf (C n))) =
      Module.finrank 𝔽 (C n) * Real.logb 2 (Fintype.card 𝔽) /
        (Fintype.card (Quo (Γs n) P) * b) := by
    unfold storageCodeRate
    rw [card_blowCode hι, card_wordsOf, Nat.cast_pow, Real.logb_pow, Fintype.card_bool,
      Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hpos' : (0 : ℝ) < Fintype.card (Quo (Γs n) P) := by exact_mod_cast hpos
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog : 0 < Real.logb 2 (Fintype.card 𝔽) := Real.logb_pos (by norm_num) hq
  have hge : ρ * Real.logb 2 (Fintype.card 𝔽) / b ≤ storageCodeRate (blowCode ι (wordsOf (C n))) := by
    rw [hrate, div_le_div_iff₀ hbpos (by positivity)]
    have := hdim n
    have h2 : ρ * Fintype.card (Quo (Γs n) P) * Real.logb 2 (Fintype.card 𝔽) ≤
        Module.finrank 𝔽 (C n) * Real.logb 2 (Fintype.card 𝔽) :=
      mul_le_mul_of_nonneg_right this hlog.le
    nlinarith
  linarith

end Tower

end AboveHalf
