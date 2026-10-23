import TransposeFollowup.GapBankInformation
import TransposeFollowup.FullFiberEntropy

/-! Whole-group recovery gives the leaf inequality. Geometry supplies only
coordinate sets and interval coverage; no entropy conclusion is a premise. -/

namespace TransposeFollowup.GapBankCode

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b sigma : ℕ} (C : GapBankCode d b sigma)

theorem grouped_leaf_entropy
    {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A] [DecidableEq A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (m : List Bool) (hm : ∀ x, C.transcript (X x) = m)
    (owner : MatrixBit d b → A) (R : Finset (MatrixBit d b → Bool))
    (hR : CoordinateRectangle owner R) (hXR : ∀ x, C.bank.recode (X x) ∈ R)
    (N : A → Finset (MatrixBit d b))
    (J : A → Type*) [∀ a, Fintype (J a)] (gap : (a : A) → J a → Finset (Fin d))
    (hgaps : ∀ a j, IsRowInterval (gap a j))
    (houtside : ∀ a j, ∀ i ∈ gap a j, ∀ c t, (i, (c, t)) ∉ ownedCoordinates owner a)
    (hcover : ∀ a v, v ∈ ownedCoordinates owner a → v ∉ N a →
      ∃ j, columnWindow sigma v.2.1 ⊆ gap a j)
    (K Ntotal Q : ℕ) (hnear : (∑ a, (N a).card) ≤ Ntotal)
    (hgapcount : ∀ a, Fintype.card (J a) ≤ K + 1)
    (hcount : Fintype.card A ≤ Q) {s : ℝ} (hs0 : 0 ≤ s) (hs : C.bank.StateBudget s) :
    observationEntropy p X ≤
      ((Ntotal : ℝ) + ((K + 1) * Q : ℕ) * s) * Real.log 2 +
      ((Q : ℝ) - 1) * (Real.log (R.card : ℝ) - observationEntropy p X) := by
  let Y := fun x => C.bank.recode (X x)
  have he : observationEntropy p Y = observationEntropy p X := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    exact C.bank.recode.injective.eq_iff
  have hd : 0 ≤ Real.log (R.card : ℝ) - observationEntropy p Y :=
    sub_nonneg.mpr (observationEntropy_le_log_support p hp hp1 Y R hXR)
  have hgroup (a : A) : conditionalObservationEntropy p
      (fun x => bitView (ownedCoordinates owner a) (Y x))
      (fun x => bitView (ownedCoordinates owner a)ᶜ (Y x)) ≤
        ((N a).card + (K + 1 : ℕ) * s) * Real.log 2 := by
    have h := C.group_conditional_entropy_le p hp hp1 X hc m hm
      (ownedCoordinates owner a) (N a) (gap a) (hgaps a) (houtside a) (hcover a) hs
    have hj : (Fintype.card (J a) : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast hgapcount a
    have hh := mul_le_mul_of_nonneg_right hj hs0
    have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
    apply h.trans
    exact mul_le_mul_of_nonneg_right (add_le_add_right hh _) hlog
  have hn : (∑ a, ((N a).card : ℝ)) ≤ (Ntotal : ℝ) := by exact_mod_cast hnear
  have hq : (Fintype.card A : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hcount
  have hsum : (∑ a, conditionalObservationEntropy p
      (fun x => bitView (ownedCoordinates owner a) (Y x))
      (fun x => bitView (ownedCoordinates owner a)ᶜ (Y x))) ≤
      ((Ntotal : ℝ) + ((K + 1) * Q : ℕ) * s) * Real.log 2 := by
    calc
      _ ≤ ∑ a : A, (((N a).card : ℝ) + (K + 1 : ℕ) * s) * Real.log 2 :=
        Finset.sum_le_sum (fun a _ => hgroup a)
      _ = ((∑ a, ((N a).card : ℝ)) + (Fintype.card A : ℝ) * (K + 1 : ℕ) * s) * Real.log 2 := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ ((Ntotal : ℝ) + ((K + 1) * Q : ℕ) * s) * Real.log 2 := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
        simp only [Nat.cast_mul]
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (K + 1 : ℕ) by positivity) hs0]
  have hj := coordinateRectangle_full_join p hp hp1 Y owner R hR hXR
  have hcoeff := mul_le_mul_of_nonneg_right (sub_le_sub_right hq 1) hd
  have hfinal := hj.trans (add_le_add hsum hcoeff)
  simpa only [he] using hfinal

end TransposeFollowup.GapBankCode
