import TransposeFollowup.GapBank
import TransposeFollowup.PacketInformation

/-! Entropy of the concrete near-coordinate and inverse-gap-state record.
The recovery premise is receiver correctness, not an assumed entropy bound. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

instance {d b sigma : ℕ} (A : GapBank d b sigma) (I : Finset (Fin d)) :
    Nonempty (A.State I) := ⟨A.state I (fun _ _ _ => false)⟩

namespace GapBankCode

variable {d b sigma : ℕ} (C : GapBankCode d b sigma)

def groupRecord (N : Finset (MatrixBit d b)) {J : Type*}
    (gap : J → Finset (Fin d)) (x : FiniteMatrix d b) :
    (N → Bool) × ((j : J) → C.bank.State (gap j)) :=
  (fun v => C.bank.recode x v, fun j => C.bank.state (gap j) x)

theorem log_state_card_le {s : ℝ} (hs : C.bank.StateBudget s)
    (I : Finset (Fin d)) (hI : IsRowInterval I) :
    Real.log (Fintype.card (C.bank.State I) : ℝ) ≤ s * Real.log 2 := by
  have hp : 0 < (Fintype.card (C.bank.State I) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  calc
    _ ≤ Real.log ((2 : ℝ) ^ s) := Real.log_le_log hp (hs I hI)
    _ = _ := by rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

theorem groupRecord_entropy_le {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (N : Finset (MatrixBit d b))
    (gap : J → Finset (Fin d)) (hgaps : ∀ j, IsRowInterval (gap j))
    {s : ℝ} (hs : C.bank.StateBudget s) :
    observationEntropy p (fun x => C.groupRecord N gap (X x)) ≤
      ((N.card : ℝ) + (Fintype.card J : ℝ) * s) * Real.log 2 := by
  have he := entropy_le_log_card
    (pushforward p (fun x => C.groupRecord N gap (X x)))
    (pushforward_nonneg p hp _) (by rw [sum_pushforward, hp1])
  change observationEntropy p (fun x => C.groupRecord N gap (X x)) ≤ _ at he
  have hbits : (0 : ℝ) < (2 : ℝ) ^ N.card := pow_pos (by norm_num) _
  have hstate (j : J) : (Fintype.card (C.bank.State (gap j)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (C.bank.State (gap j)) ≠ 0)
  have hprod : (∏ j : J, (Fintype.card (C.bank.State (gap j)) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hstate j)
  calc
    _ ≤ Real.log (Fintype.card ((N → Bool) × ((j : J) → C.bank.State (gap j))) : ℝ) := he
    _ = (N.card : ℝ) * Real.log 2 +
        ∑ j : J, Real.log (Fintype.card (C.bank.State (gap j)) : ℝ) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_coe, Fintype.card_pi, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_prod]
      rw [Real.log_mul (ne_of_gt hbits) hprod, Real.log_pow, Real.log_prod]
      exact fun j _ => hstate j
    _ ≤ (N.card : ℝ) * Real.log 2 + ∑ _j : J, s * Real.log 2 := by
      exact add_le_add le_rfl (Finset.sum_le_sum (fun j _ =>
        C.log_state_card_le hs (gap j) (hgaps j)))
    _ = _ := by simp; ring

/-- At a fixed transcript, a group conditioned on every other stored
coordinate has at most the entropy of its near values and gap records. -/
theorem group_conditional_entropy_le {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (m : List Bool) (hm : ∀ x, C.transcript (X x) = m)
    (S N : Finset (MatrixBit d b)) (gap : J → Finset (Fin d))
    (hgaps : ∀ j, IsRowInterval (gap j))
    (houtside : ∀ j, ∀ i ∈ gap j, ∀ c t, (i, (c, t)) ∉ S)
    (hcover : ∀ v ∈ S, v ∉ N → ∃ j, columnWindow sigma v.2.1 ⊆ gap j)
    {s : ℝ} (hs : C.bank.StateBudget s) :
    conditionalObservationEntropy p (fun x => bitView S (C.bank.recode (X x)))
      (fun x => bitView (Finset.univ \ S) (C.bank.recode (X x))) ≤
      ((N.card : ℝ) + (Fintype.card J : ℝ) * s) * Real.log 2 := by
  let outside := fun x => bitView (Finset.univ \ S) (C.bank.recode (X x))
  let records := fun x => C.groupRecord N gap (X x)
  have hf : (fun x => bitView S (C.bank.recode (X x))).FactorsThrough
      (fun x => (outside x, records x)) := by
    intro x y he
    apply (bitView_eq_iff _ _ _).mpr
    apply C.group_eq_of_records hc S N gap hgaps houtside hcover
      ⟨x, rfl⟩ ⟨y, rfl⟩ ((hm x).trans (hm y).symm)
    · intro v hv
      exact (bitView_eq_iff _ _ _).mp (congrArg Prod.fst he) v (by simp [hv])
    · intro v hv
      exact congrFun (congrArg (fun z => z.2.1) he) ⟨v, hv⟩
    · intro j
      exact congrFun (congrArg (fun z => z.2.2) he) j
  exact (conditionalObservationEntropy_le_of_factorsThrough p hp _ records outside hf).trans
    ((conditionalObservationEntropy_le_observation p hp hp1 records outside).trans
      (C.groupRecord_entropy_le p hp hp1 X N gap hgaps hs))

end GapBankCode

end TransposeFollowup
