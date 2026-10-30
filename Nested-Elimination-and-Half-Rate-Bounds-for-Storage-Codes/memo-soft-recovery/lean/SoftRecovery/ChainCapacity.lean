import SoftRecovery.Capacity
import SoftRecovery.Innovation

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes
open scoped BigOperators
set_option autoImplicit false

variable {A V : Type*} [DecidableEq A] [DecidableEq V]

/-- A record identity, its actual conditioning set, and the recovered coordinate. -/
abbrev RecordUse (A : Type*) := A × (Finset A × A)

def useCost (h : Finset A → ℝ) (u : RecordUse A) : ℝ :=
  innovation h u.1 u.2.1 u.2.2

/-- Preserve the exact chain-rule contexts of the ordered helper list. -/
def recordUses (v : A) : Finset A → List A → List (RecordUse A)
  | _, [] => []
  | K, e :: es => (e, (K, v)) :: recordUses v (insert e K) es

theorem recordUses_cost (h : Finset A → ℝ) (v : A) :
    ∀ (es : List A) (K : Finset A),
      ((recordUses v K es).map (useCost h)).sum = helperInnovations h v K es := by
  intro es
  induction es with
  | nil => intro K; rfl
  | cons e es ih => intro K; simp [recordUses, helperInnovations, useCost, ih]

def tagUses (e : A) (uses : List (Finset A × A)) : List (RecordUse A) :=
  uses.map fun kv => (e, kv)

theorem tagUses_cost (h : Finset A → ℝ) (e : A) (uses : List (Finset A × A)) :
    ((tagUses e uses).map (useCost h)).sum = innovationSum h e uses := by
  simp [tagUses, useCost, innovationSum, List.map_map, Function.comp_def]

variable [Fintype V] [Fintype A]

noncomputable def allRecordUses (f : V → A) (N : V → Finset V) (helpers : V → List A) :
    List (RecordUse A) :=
  univ.toList.flatMap fun v => recordUses (f v) ((N v).image f) (helpers v)

noncomputable def coveredUses (chains : A → List (List (Finset A × A))) : List (RecordUse A) :=
  univ.toList.flatMap fun e => (chains e).flatMap (tagUses e)

omit [DecidableEq V] [Fintype A] in
theorem allRecordUses_cost (h : Finset A → ℝ) (f : V → A) (N : V → Finset V)
    (helpers : V → List A) :
    ((allRecordUses f N helpers).map (useCost h)).sum =
      ∑ v, helperInnovations h (f v) ((N v).image f) (helpers v) := by
  simp [allRecordUses, List.flatMap_def, List.map_map,
    Function.comp_def, recordUses_cost]

theorem coveredUses_cost (h : Finset A → ℝ) (chains : A → List (List (Finset A × A))) :
    ((coveredUses chains).map (useCost h)).sum =
      ∑ e, ((chains e).map (innovationSum h e)).sum := by
  simp [coveredUses, List.flatMap_def, List.map_map,
    Function.comp_def, tagUses_cost]

/-- Every actual helper occurrence is covered exactly once, with its exact
record identity and context. No nesting or entropy bound is assumed. -/
structure RecordUseCover (f : V → A) (N : V → Finset V) (helpers : V → List A) where
  chains : A → List (List (Finset A × A))
  cover : (allRecordUses f N helpers).Perm (coveredUses chains)

/-- The original wholly combinatorial certificate. -/
structure RecordChainCover (f : V → A) (N : V → Finset V) (helpers : V → List A)
    extends RecordUseCover f N helpers where
  nested : ∀ e, ∀ chain ∈ chains e, NestedUses ∅ chain

noncomputable def RecordUseCover.loss {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers) (h : Finset A → ℝ) : ℝ :=
  ∑ e, ((cert.chains e).map (chainLoss h ∅)).sum

noncomputable def RecordUseCover.helperLoss {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers) (h : Finset A → ℝ) : ℝ :=
  ∑ e, ((cert.chains e).map (SoftRecovery.helperLoss h e ∅)).sum

noncomputable def RecordUseCover.terminalInformation {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers) (h : Finset A → ℝ) : ℝ :=
  ∑ e, ((cert.chains e).map fun chain => mi h e (endContext ∅ chain)).sum

omit [DecidableEq V] in
/-- Exact occurrence coverage transports any proved per-list charge. -/
theorem RecordUseCover.innovation_le_sum {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers) (h : Finset A → ℝ)
    (cost : A → List (Finset A × A) → ℝ)
    (hb : ∀ e, ∀ chain ∈ cert.chains e, innovationSum h e chain ≤ cost e chain) :
    (∑ v, helperInnovations h (f v) ((N v).image f) (helpers v)) ≤
      ∑ e, ((cert.chains e).map (cost e)).sum := by
  rw [← allRecordUses_cost, (cert.cover.map (useCost h)).sum_eq, coveredUses_cost]
  exact sum_le_sum fun e _ => List.sum_le_sum (hb e)

omit [DecidableEq V] in
theorem RecordUseCover.innovation_information_bound {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    (∑ v, helperInnovations h (f v) ((N v).image f) (helpers v)) ≤
      cert.terminalInformation h + cert.helperLoss h := by
  have hs := cert.innovation_le_sum h
    (fun e chain => mi h e (endContext ∅ chain) + SoftRecovery.helperLoss h e ∅ chain)
    (fun e chain _ => by simpa [mi_empty hh] using innovations_le_helperLoss h e chain ∅)
  simpa only [RecordUseCover.terminalInformation, RecordUseCover.helperLoss,
    List.sum_map_add, sum_add_distrib] using hs

omit [DecidableEq V] in
theorem RecordUseCover.terminalInformation_le_capacity {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    cert.terminalInformation h ≤ ∑ e, ((cert.chains e).length : ℝ) * h {e} := by
  apply sum_le_sum
  intro e _
  have hs := List.sum_le_length_nsmul
    ((cert.chains e).map fun chain => mi h e (endContext ∅ chain)) (h {e}) ?_
  · simpa using hs
  · intro x hx
    obtain ⟨chain, _, rfl⟩ := List.mem_map.mp hx
    have hm := hh.mono (subset_insert e (endContext ∅ chain))
    unfold mi
    linarith

omit [DecidableEq V] in
theorem RecordUseCover.helperLoss_le_loss {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) : cert.helperLoss h ≤ cert.loss h :=
  sum_le_sum fun e _ => List.sum_le_sum fun chain _ => helperLoss_le_chainLoss hh e chain ∅

omit [DecidableEq V] in
theorem RecordUseCover.innovation_bound_with_loss {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    (∑ v, helperInnovations h (f v) ((N v).image f) (helpers v)) ≤
      (∑ e, ((cert.chains e).length : ℝ) * h {e}) + cert.loss h := by
  exact (cert.innovation_information_bound hh).trans
    (add_le_add (cert.terminalInformation_le_capacity hh) (cert.helperLoss_le_loss hh))

omit [DecidableEq V] in
theorem RecordUseCover.loss_eq_zero {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers) {h : Finset A → ℝ}
    (hn : ∀ e, ∀ chain ∈ cert.chains e, RetainedUses h ∅ chain) : cert.loss h = 0 := by
  apply sum_eq_zero
  intro e _
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨chain, hc, rfl⟩ := List.mem_map.mp hx
  exact (hn e chain hc).loss_eq_zero

omit [DecidableEq V] in
theorem RecordUseCover.loss_contr_le {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) (Z : Finset A) :
    cert.loss (contr h Z) ≤ cert.loss h :=
  sum_le_sum fun _ _ => List.sum_le_sum fun chain _ => chainLoss_contr_le hh Z chain ∅

omit [DecidableEq V] in
theorem RecordUseCover.residual_information_bound {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    (∑ v, increment h ((N v).image f) (f v)) ≤
      cert.terminalInformation h + cert.helperLoss h +
        ∑ v, increment h ((helpers v).toFinset ∪ (N v).image f) (f v) := by
  calc
    _ = (∑ v, helperInnovations h (f v) ((N v).image f) (helpers v)) +
        ∑ v, increment h ((helpers v).toFinset ∪ (N v).image f) (f v) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v _ =>
        increment_eq_helperInnovations_add h (f v) (helpers v) ((N v).image f)
    _ ≤ _ := add_le_add (cert.innovation_information_bound hh) le_rfl

omit [DecidableEq V] in
theorem RecordUseCover.residual_bound_with_loss {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordUseCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    (∑ v, increment h ((N v).image f) (f v)) ≤
      (∑ e, ((cert.chains e).length : ℝ) * h {e}) + cert.loss h +
        ∑ v, increment h ((helpers v).toFinset ∪ (N v).image f) (f v) := by
  exact (cert.residual_information_bound hh).trans
    (add_le_add (add_le_add (cert.terminalInformation_le_capacity hh)
      (cert.helperLoss_le_loss hh)) le_rfl)

omit [DecidableEq V] in
theorem RecordChainCover.innovation_bound {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordChainCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h) :
    (∑ v, helperInnovations h (f v) ((N v).image f) (helpers v)) ≤
      ∑ e, ((cert.chains e).length : ℝ) * h {e} := by
  simpa [cert.toRecordUseCover.loss_eq_zero
    (fun e chain hc => (cert.nested e chain hc).retained h)] using
    cert.toRecordUseCover.innovation_bound_with_loss hh

omit [DecidableEq V] in
theorem RecordChainCover.residual_bound {f : V → A} {N : V → Finset V}
    {helpers : V → List A} (cert : RecordChainCover f N helpers)
    {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (hr : ∀ v, increment h ((helpers v).toFinset ∪ (N v).image f) (f v) = 0) :
    (∑ v, increment h ((N v).image f) (f v)) ≤
      ∑ e, ((cert.chains e).length : ℝ) * h {e} := by
  simpa [hr, cert.toRecordUseCover.loss_eq_zero
    (fun e chain hc => (cert.nested e chain hc).retained h)] using
    cert.toRecordUseCover.residual_bound_with_loss hh

/-- Information actually revealed about the selected input, unused coordinate
capacity, terminal helper information, and helper-specific potential drops.
Every term is evaluated in the same final common context. -/
theorem RecordUseCover.information_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A) (b : V → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z) (Q : Finset A) :
    (∑ v, b v) + revealCredit h f b Z Q ≤
      2 * δ + 2 * mutualRank h (univ.image f) Q Z +
      (cert.terminalInformation (contr h (Z ∪ Q)) + cert.helperLoss (contr h (Z ∪ Q)) +
        ∑ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ (Z ∪ Q)) (f v)) := by
  apply capacity_bound_with_credit hh f Z Q b δ _ hD hlower
  simpa only [increment_contr] using cert.residual_information_bound
    (contr_isPolymatroid hh (Z ∪ Q))

/-- The previous entropy-only statement follows by dropping nonnegative
credit and replacing each information term by its capacity bound. -/
theorem RecordUseCover.entropy_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A) (b : V → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hb : ∀ v, increment h Z (f v) ≤ b v)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z) (Q : Finset A) :
    (∑ v, b v) ≤ 2 * δ + 2 * conditionalRank h Q Z +
      ((∑ e, ((cert.chains e).length : ℝ) * increment h (Z ∪ Q) e) +
        cert.loss (contr h (Z ∪ Q)) +
        ∑ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ (Z ∪ Q)) (f v)) := by
  have hs := cert.information_bound hh f Z helpers b δ hD hlower Q
  have hcredit := revealCredit_nonneg hh f b Z Q hb
  have hinfo := mutualRank_le_right hh (univ.image f) Q Z
  have hterm := cert.terminalInformation_le_capacity (contr_isPolymatroid hh (Z ∪ Q))
  have hloss := cert.helperLoss_le_loss (contr_isPolymatroid hh (Z ∪ Q))
  have he : ∀ e, contr h (Z ∪ Q) {e} = increment h (Z ∪ Q) e := by
    intro e
    simp [contr, increment]
  simp_rw [he] at hterm
  linarith

/-- Exact semantic retention and decoding remove both error terms. Retention
is certified before `Q` is chosen, and survives every additional common reveal. -/
theorem RecordUseCover.retained_entropy_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A) (b : V → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hn : ∀ e, ∀ chain ∈ cert.chains e, RetainedUses (contr h Z) ∅ chain)
    (hb : ∀ v, increment h Z (f v) ≤ b v)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hr : ∀ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) = 0)
    (Q : Finset A) :
    (∑ v, b v) ≤ 2 * δ + 2 * conditionalRank h Q Z +
      ∑ e, ((cert.chains e).length : ℝ) * increment h (Z ∪ Q) e := by
  have hloss : cert.loss (contr h (Z ∪ Q)) = 0 := by
    apply cert.loss_eq_zero
    intro e chain hc
    simpa only [contr_contr] using (hn e chain hc).contr (contr_isPolymatroid hh Z) Q
  have hrQ : ∀ v,
      increment h (((helpers v).toFinset ∪ (N v).image f) ∪ (Z ∪ Q)) (f v) = 0 :=
    fun v => recovery_mono hh (union_subset_union (subset_refl _) subset_union_left) (hr v)
  simpa only [hloss, hrQ, sum_const_zero, add_zero] using
    cert.entropy_bound hh f Z helpers b δ hD hb hlower Q

/-- Capacity accounting for arbitrary contexts and incomplete recovery. Both
error terms may be evaluated before choosing the common reveal. -/
theorem chain_record_bound_with_loss {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A)
    (b : V → ℝ) (c : A → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hb : ∀ v, increment h Z (f v) ≤ b v) (hc : ∀ e, increment h Z e ≤ c e)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (Q : Finset A) :
    (∑ v, b v) ≤ 2 * δ + 2 * (∑ e ∈ Q, c e) +
      (∑ e, if e ∈ Q then 0 else ((cert.chains e).length : ℝ) * c e) +
      cert.loss (contr h Z) +
      ∑ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) := by
  have hQ : conditionalRank h Q Z ≤ ∑ e ∈ Q, c e := by
    apply ((contr_isPolymatroid hh Z).le_sum_singleton Q).trans
    exact sum_le_sum fun e _ => by simpa [contr, increment] using hc e
  have hcap : (∑ e, ((cert.chains e).length : ℝ) * increment h (Z ∪ Q) e) ≤
      ∑ e, if e ∈ Q then 0 else ((cert.chains e).length : ℝ) * c e := by
    apply sum_le_sum
    intro e _
    by_cases he : e ∈ Q
    · simp [he]
    · simp only [he, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left
        ((increment_antitone hh subset_union_left e).trans (hc e)) (Nat.cast_nonneg _)
  have hloss : cert.loss (contr h (Z ∪ Q)) ≤ cert.loss (contr h Z) := by
    simpa only [contr_contr] using cert.loss_contr_le (contr_isPolymatroid hh Z) Q
  have hr : (∑ v, increment h
      (((helpers v).toFinset ∪ (N v).image f) ∪ (Z ∪ Q)) (f v)) ≤
      ∑ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) :=
    sum_le_sum fun v _ => increment_antitone hh
      (union_subset_union (subset_refl _) subset_union_left) _
  have hs := cert.entropy_bound hh f Z helpers b δ hD hb hlower Q
  linarith

theorem optimized_chain_record_bound_with_loss {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A)
    (b : V → ℝ) (c : A → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hb : ∀ v, increment h Z (f v) ≤ b v) (hc : ∀ e, increment h Z e ≤ c e)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z) :
    (∑ v, b v) ≤ 2 * δ + (∑ e, c e * (min 2 (cert.chains e).length : ℕ)) +
      cert.loss (contr h Z) +
      ∑ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) := by
  have hs := chain_record_bound_with_loss hh f Z helpers b c δ hD cert hb hc hlower
    (univ.filter fun e => 2 ≤ (cert.chains e).length)
  rw [add_assoc (2 * δ), threshold_bill] at hs
  exact hs

/-- Semantic retention and exact decoding are the zero-error case. Only
conditional capacity bounds are needed. -/
theorem retained_chain_record_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A)
    (b : V → ℝ) (c : A → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hn : ∀ e, ∀ chain ∈ cert.chains e, RetainedUses (contr h Z) ∅ chain)
    (hb : ∀ v, increment h Z (f v) ≤ b v) (hc : ∀ e, increment h Z e ≤ c e)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hr : ∀ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) = 0)
    (Q : Finset A) :
    (∑ v, b v) ≤ 2 * δ + 2 * (∑ e ∈ Q, c e) +
      ∑ e, if e ∈ Q then 0 else ((cert.chains e).length : ℝ) * c e := by
  simpa only [cert.loss_eq_zero hn, hr, sum_const_zero, add_zero] using
    chain_record_bound_with_loss hh f Z helpers b c δ hD cert hb hc hlower Q

theorem optimized_retained_chain_record_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A)
    (b : V → ℝ) (c : A → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordUseCover f N helpers)
    (hn : ∀ e, ∀ chain ∈ cert.chains e, RetainedUses (contr h Z) ∅ chain)
    (hb : ∀ v, increment h Z (f v) ≤ b v) (hc : ∀ e, increment h Z e ≤ c e)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hr : ∀ v, increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) = 0) :
    (∑ v, b v) ≤ 2 * δ + ∑ e, c e * (min 2 (cert.chains e).length : ℕ) := by
  have hs := retained_chain_record_bound hh f Z helpers b c δ hD cert hn hb hc hlower hr
    (univ.filter fun e => 2 ≤ (cert.chains e).length)
  rw [add_assoc, threshold_bill] at hs
  exact hs

/-- Chain-count version of mixed record accounting. Nesting is a checkable
condition on the actual ordered decoder contexts, not on tape-cell locations.
Common conditioning preserves the same structural certificate. -/
theorem chain_record_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A)
    (b : V → ℝ) (c : A → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordChainCover f N helpers)
    (hb : ∀ v, h {f v} ≤ b v) (hc : ∀ e, h {e} ≤ c e)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hrecover : ∀ v,
      increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) = 0)
    (Q : Finset A) :
    (∑ v, b v) ≤ 2 * δ + 2 * (∑ e ∈ Q, c e) +
      ∑ e, if e ∈ Q then 0 else ((cert.chains e).length : ℝ) * c e := by
  exact retained_chain_record_bound hh f Z helpers b c δ hD cert.toRecordUseCover
    (fun e chain hc => (cert.nested e chain hc).retained (contr h Z))
    (fun v => (increment_le_singleton hh Z _).trans (hb v))
    (fun e => (increment_le_singleton hh Z e).trans (hc e)) hlower hrecover Q

theorem optimized_chain_record_bound {h : Finset A → ℝ} (hh : IsPolymatroid h)
    (f : V → A) (Z : Finset A) (helpers : V → List A)
    (b : V → ℝ) (c : A → ℝ) (δ : ℝ)
    {N : V → Finset V} {pcs : List (Finset V)} (hD : Decomp N ∅ pcs)
    (cert : RecordChainCover f N helpers)
    (hb : ∀ v, h {f v} ≤ b v) (hc : ∀ e, h {e} ≤ c e)
    (hlower : (∑ v, b v) - δ ≤ h (univ.image f ∪ Z) - h Z)
    (hrecover : ∀ v,
      increment h (((helpers v).toFinset ∪ (N v).image f) ∪ Z) (f v) = 0) :
    (∑ v, b v) ≤ 2 * δ +
      ∑ e, c e * (min 2 (cert.chains e).length : ℕ) := by
  exact optimized_retained_chain_record_bound hh f Z helpers b c δ hD cert.toRecordUseCover
    (fun e chain hc => (cert.nested e chain hc).retained (contr h Z))
    (fun v => (increment_le_singleton hh Z _).trans (hb v))
    (fun e => (increment_le_singleton hh Z e).trans (hc e)) hlower hrecover

end SoftRecovery
