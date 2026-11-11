import SharedDecoders.CompositionComplete
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Prod

/-! # Exact finite counting for the full-input agreement bounds -/

namespace SharedDecoders

open scoped BigOperators

variable {I B κ : Type*} [Fintype I] [Fintype κ]

noncomputable def equalClassPairs (p : I → κ) (z : I → B) : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun ce => ce.1 ≠ ce.2 ∧ p ce.1 = p ce.2 ∧ z ce.1 = z ce.2)

noncomputable def sameClassPairs (p : I → κ) : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun ce => ce.1 ≠ ce.2 ∧ p ce.1 = p ce.2)

omit [Fintype κ] in
@[simp] lemma mem_sameClassPairs (p : I → κ) (ce : I × I) :
    ce ∈ sameClassPairs p ↔ ce.1 ≠ ce.2 ∧ p ce.1 = p ce.2 := by
  classical
  simp [sameClassPairs]

omit [Fintype I] in
lemma two_mul_card_le_two_add_offDiag (s : Finset I) :
    2 * s.card ≤ 2 + s.offDiag.card := by
  rw [Finset.offDiag_card]
  have hsq : s.card ≤ s.card * s.card := by
    by_cases h : s.card = 0
    · simp [h]
    · nlinarith
  have hsub := Nat.sub_add_cancel hsq
  by_cases h : s.card ≤ 2
  · interval_cases hcard : s.card <;> simp_all
  · have h : 3 ≤ s.card := by omega
    nlinarith

/-- Each color contributes at most one unmatched item; all other successes are
paid by equal ordered pairs within that color. -/
lemma selected_card_bound (p : I → κ) (z : I → B) (S : Finset I)
    (hS : ∀ c ∈ S, ∀ e ∈ S, p c = p e → z c = z e) :
    2 * S.card ≤ 2 * Fintype.card κ + (equalClassPairs p z).card := by
  classical
  let T := equalClassPairs p z
  have hsplitS : S.card = ∑ J : κ, (S.filter (fun c => p c = J)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hsplitT : T.card = ∑ J : κ, (T.filter (fun ce => p ce.1 = J)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hlocal (J : κ) : 2 * (S.filter (fun c => p c = J)).card ≤
      2 + (T.filter (fun ce => p ce.1 = J)).card := by
    apply (two_mul_card_le_two_add_offDiag _).trans
    apply Nat.add_le_add_left
    apply Finset.card_le_card
    intro ce hce
    obtain ⟨hc, he, hne⟩ := Finset.mem_offDiag.mp hce
    obtain ⟨hcS, hcJ⟩ := Finset.mem_filter.mp hc
    obtain ⟨heS, heJ⟩ := Finset.mem_filter.mp he
    have hp := hcJ.trans heJ.symm
    simp only [T, equalClassPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hne, hp, hS _ hcS _ heS hp⟩, hcJ⟩
  have h := Finset.sum_le_sum (s := Finset.univ) (fun J _ => hlocal J)
  simpa [← Finset.mul_sum, Finset.sum_add_distrib, ← hsplitS, ← hsplitT, mul_comm]
    using h

/-- Removing one of two equal coordinates parametrizes the complete equality
fibre, including all other coordinates without restrictions. -/
noncomputable def equalCoordinatesEquiv (i j : I) (hij : i ≠ j) :
    {f : I → B // f i = f j} ≃ ({t : I // t ≠ i} → B) := by
  classical
  refine {
    toFun := fun f t => f.val t.val
    invFun := fun g => ⟨fun t => if h : t = i then g ⟨j, hij.symm⟩ else g ⟨t, h⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simp [hij.symm]
  · intro f
    apply Subtype.ext
    funext t
    by_cases ht : t = i
    · subst t
      simpa using f.property.symm
    · simp [ht]
  · intro g
    funext t
    simp [t.property]

lemma equal_coordinates_card [Fintype B] (i j : I) (hij : i ≠ j) :
    Nat.card {f : I → B // f i = f j} =
      Fintype.card B ^ (Fintype.card I - 1) := by
  classical
  rw [Nat.card_congr (equalCoordinatesEquiv (B := B) i j hij), Nat.card_eq_fintype_card]
  simp

noncomputable def receiverClassSize (p : I → κ) (J : κ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c => p c = J)).card

lemma sameClassPairs_card (p : I → κ) :
    (sameClassPairs p).card =
      ∑ J : κ, receiverClassSize p J * (receiverClassSize p J - 1) := by
  classical
  unfold receiverClassSize
  rw [Finset.card_eq_sum_card_fiberwise (f := fun ce : I × I => p ce.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro J _
  have he : ((sameClassPairs p).filter (fun ce => p ce.1 = J)) =
      (Finset.univ.filter (fun c => p c = J)).offDiag := by
    ext ce
    simp only [sameClassPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag]
    aesop
  rw [he, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

variable {d : ℕ} [NeZero d] {A : Type*}

/-- The demanded words in the phase count are independent coordinates after a
literal permutation inside each row. -/
def twistedRowsEquiv : State d A ≃ State d A where
  toFun X c i := X c (i - c)
  invFun Z c i := Z c (i + c)
  left_inv X := by funext c i; simp
  right_inv X := by funext c i; simp

lemma twisted_pair_card [Fintype A] (c e : ZMod d) (hce : c ≠ e) :
    Nat.card {X : State d A // twistedRowsEquiv X c = twistedRowsEquiv X e} =
      (Fintype.card A ^ d) ^ (d - 1) := by
  have he := Nat.card_congr ((twistedRowsEquiv (A := A)).subtypeEquiv
    (p := fun X : State d A => twistedRowsEquiv X c = twistedRowsEquiv X e)
    (q := fun X : State d A => X c = X e) (fun _ => Iff.rfl))
  rw [he, equal_coordinates_card c e hce]
  simp [ZMod.card]

end SharedDecoders
