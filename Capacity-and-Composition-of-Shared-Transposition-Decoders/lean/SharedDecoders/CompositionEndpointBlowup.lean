import SharedDecoders.CompositionSparsePatch
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # Endpoint receiver classes can grow under composition -/

namespace SharedDecoders

open scoped BigOperators CharTwo

variable {d : ℕ} [NeZero d]

/-- Add column one into column zero, independently in each row. -/
def endpointFirst (X : State d (ZMod 2)) : State d (ZMod 2) :=
  fun i c => if c = 0 then X i 0 + X i 1 else X i c

/-- Add the parity of a row to every entry of that row. -/
def endpointSecond (X : State d (ZMod 2)) : State d (ZMod 2) :=
  fun i c => X i c + ∑ j, X i j

omit [NeZero d] in
theorem endpointFirst_involutive (hd : 2 ≤ d) :
    Function.Involutive (endpointFirst (d := d)) := by
  intro X
  funext i c
  by_cases hc : c = 0
  · subst c
    simp [endpointFirst, one_ne_zero_of_two_le hd]
  · simp [endpointFirst, hc]

private theorem even_cast_zero (hd : Even d) : (d : ZMod 2) = 0 := by
  obtain ⟨k, rfl⟩ := hd
  simp [Nat.cast_add]

theorem endpointSecond_involutive (hd : Even d) :
    Function.Involutive (endpointSecond (d := d)) := by
  intro X
  funext i c
  simp only [endpointSecond, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul, even_cast_zero hd, zero_mul,
    add_zero, add_assoc, CharTwo.add_self_eq_zero]

omit [NeZero d] in
theorem endpointFirst_classUniform :
    ClassUniform singletonRest (endpointFirst (d := d)) := by
  refine ⟨fun t X i => if t then X i 0 + X i 1 else X i 0, ?_⟩
  intro X c i
  by_cases hc : c = 0
  · subst c
    simp [singletonRest, endpointFirst]
  · simp [singletonRest, endpointFirst, hc, rot]

theorem endpointSecond_equivariant : Equivariant (endpointSecond (d := d)) := by
  intro s X
  funext i c
  change X i (c+s) + ∑ j, X i (j+s) = X i (c+s) + ∑ j, X i j
  exact congrArg (X i (c+s) + ·) (Equiv.sum_comp (Equiv.addRight s) (X i))

private theorem endpointFirst_sum (X : State d (ZMod 2)) (i : ZMod d) :
    (∑ j, endpointFirst X i j) = (∑ j, X i j) + X i 1 := by
  have he (j : ZMod d) : endpointFirst X i j = X i j + if j=0 then X i 1 else 0 := by
    by_cases hj : j=0 <;> simp [endpointFirst, hj]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

/-- The normalized complete-map getter at receiver `c`. -/
def endpointGetter (c : ZMod d) (X : State d (ZMod 2)) (i : ZMod d) : ZMod 2 :=
  X i 0 + (∑ j, X i j) + if c=0 then 0 else X i (1-c)

theorem endpoint_composite_getter (X : State d (ZMod 2)) (c i : ZMod d) :
    endpointSecond (endpointFirst X) i c = endpointGetter c (rot c X) i := by
  rw [endpointSecond, endpointFirst_sum]
  have hs : (∑ j : ZMod d, X i (j+c)) = ∑ j, X i j :=
    Equiv.sum_comp (Equiv.addRight c) (X i)
  by_cases hc : c=0
  · subst c
    simp only [endpointFirst, endpointGetter, rot_apply, add_zero, ite_true]
    abel_nf
    simp
  · simp only [endpointFirst, hc, ite_false, endpointGetter, rot_apply, zero_add,
      hs, sub_add_cancel]
    ac_rfl

/-- The normalized getters are pairwise distinct, even though the two factors
use respectively two classes and one class. -/
theorem endpointGetter_injective (_hd : 2 ≤ d) :
    Function.Injective (endpointGetter (d := d)) := by
  intro c e h
  by_contra hce
  by_cases hc : c=0
  · subst c
    have he : e ≠ 0 := Ne.symm hce
    let X : State d (ZMod 2) := fun _ j => if j=1-e then 1 else 0
    have hh := congrArg (fun f => f X 0) h
    simp only [endpointGetter, ite_true, he, ite_false, add_zero] at hh
    have hz : X 0 (1-e) = 1 := by simp [X]
    rw [hz] at hh
    have hh' : (X 0 0 + ∑ j, X 0 j) + 0 = (X 0 0 + ∑ j, X 0 j) + 1 := by
      simpa only [add_zero] using hh
    exact zero_ne_one (add_left_cancel hh')
  · by_cases he : e=0
    · have h' := congrArg (fun f => f) h.symm
      let X : State d (ZMod 2) := fun _ j => if j=1-c then 1 else 0
      have hh := congrArg (fun f => f X 0) h'
      simp only [endpointGetter, he, ite_true, hc, ite_false, add_zero] at hh
      have hz : X 0 (1-c) = 1 := by simp [X]
      rw [hz] at hh
      have hh' : (X 0 0 + ∑ j, X 0 j) + 0 = (X 0 0 + ∑ j, X 0 j) + 1 := by
        simpa only [add_zero] using hh
      exact zero_ne_one (add_left_cancel hh')
    · let X : State d (ZMod 2) := fun _ j => if j=1-c then 1 else 0
      have hh := congrArg (fun f => f X 0) h
      simp only [endpointGetter, hc, he, ite_false] at hh
      have hidx : (1-e : ZMod d) ≠ 1-c := by intro hh; exact hce (sub_right_injective hh).symm
      have hx : X 0 (1-c) = 1 := by simp [X]
      have hy : X 0 (1-e) = 0 := by simp [X, hidx]
      rw [hx, hy] at hh
      exact one_ne_zero (add_left_cancel hh)

/-- Every receiver class of this actual composition is a singleton. -/
theorem endpoint_composite_requires_singletons (hd : 2 ≤ d) {κ : Type*}
    (p : ZMod d → κ)
    (hK : ClassUniform p (endpointSecond ∘ endpointFirst)) : Function.Injective p := by
  intro c e hp
  apply endpointGetter_injective hd
  funext Y i
  have hh := hK.columns_of_same_class hp (rot (-e) Y) i
  change endpointSecond (endpointFirst (rot (-e) Y)) i e =
    endpointSecond (endpointFirst (rot (e-c) (rot (-e) Y))) i c at hh
  rw [endpoint_composite_getter, endpoint_composite_getter,
    rot_rot_neg, rot_rot, rot_rot] at hh
  have hs : c + (e-c) + -e = 0 := by abel
  simpa only [hs, rot_zero] using hh.symm

end SharedDecoders
