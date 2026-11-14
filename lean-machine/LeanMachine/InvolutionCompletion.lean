import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Logic.Equiv.Bool
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Completing a finite partial matching

Fixed points of an involution represent unmatched vertices. On an even
finite type they can be paired without changing any existing nontrivial
pair. The empty type is included.
-/

namespace LeanMachine.InvolutionCompletion

variable {V : Type*} [Fintype V]

/-- Boolean flipping, transported through a finite equivalence, pairs any
even finite type without fixed points. -/
theorem exists_fixedPointFree_involution (hV : Even (Fintype.card V)) :
    ∃ p : V → V, Function.Involutive p ∧ ∀ v, p v ≠ v := by
  classical
  obtain ⟨n, hn⟩ := hV
  let e : V ≃ Bool × Fin n := Fintype.equivOfCardEq (by simp [hn, two_mul])
  let p : V → V := fun v => e.symm (!(e v).1, (e v).2)
  refine ⟨p, ?_, ?_⟩
  · intro v
    simp [p]
  · intro v hv
    have hb := congrArg (fun v => (e v).1) hv
    simp only [p, e.apply_symm_apply] at hb
    cases h : (e v).1 <;> simp [h] at hb

/-- The fixed-point subtype of an involution on an even finite type also
has even cardinality. -/
theorem even_natCard_fixedPoints (m : V → V) (hm : Function.Involutive m)
    (hV : Even (Fintype.card V)) : Even (Nat.card {v // m v = v}) := by
  classical
  let σ : Equiv.Perm V := hm.toPerm m
  have hσ : σ ^ 2 = 1 := by
    ext v
    exact hm v
  have hs : Even σ.support.card := even_iff_two_dvd.mpr
    (Equiv.Perm.two_dvd_card_support hσ)
  have hc : Fintype.card {v // m v = v} = Fintype.card V - σ.support.card := by
    calc
      _ = Fintype.card {v // v ∉ σ.support} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by simp [σ]))
      _ = Fintype.card V - Fintype.card {v // v ∈ σ.support} :=
        Fintype.card_subtype_compl (fun v => v ∈ σ.support)
      _ = _ := by rw [Fintype.card_coe]
  rw [Nat.card_eq_fintype_card, hc]
  exact hV.tsub hs

/-- Every involution on an even finite type extends to a fixed-point-free
one, retaining all of its nontrivial pairs. -/
theorem exists_fixedPointFree_extension (m : V → V) (hm : Function.Involutive m)
    (hV : Even (Fintype.card V)) :
    ∃ p : V → V, Function.Involutive p ∧ (∀ v, p v ≠ v) ∧
      (∀ v, m v ≠ v → p v = m v) := by
  classical
  obtain ⟨r, hr, hrf⟩ := exists_fixedPointFree_involution (V := {v // m v = v})
    (by simpa only [Nat.card_eq_fintype_card] using even_natCard_fixedPoints m hm hV)
  let p : V → V := fun v => if h : m v = v then (r ⟨v, h⟩).val else m v
  refine ⟨p, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : m v = v
    · have hv' : m (r ⟨v, hv⟩).val = (r ⟨v, hv⟩).val := (r ⟨v, hv⟩).property
      simpa only [p, dite_eq_left hv, dite_eq_left hv'] using congrArg Subtype.val (hr ⟨v, hv⟩)
    · have hv' : m (m v) ≠ m v := by rw [hm v]; exact Ne.symm hv
      simp only [p, dite_eq_right hv, dite_eq_right hv', hm v]
  · intro v hp
    by_cases hv : m v = v
    · apply hrf ⟨v, hv⟩
      exact Subtype.ext (by simpa only [p, dite_eq_left hv] using hp)
    · exact hv (by simpa only [p, dite_eq_right hv] using hp)
  · intro v hv
    exact dite_eq_right hv

end LeanMachine.InvolutionCompletion

#print axioms LeanMachine.InvolutionCompletion.exists_fixedPointFree_involution
#print axioms LeanMachine.InvolutionCompletion.even_natCard_fixedPoints
#print axioms LeanMachine.InvolutionCompletion.exists_fixedPointFree_extension
