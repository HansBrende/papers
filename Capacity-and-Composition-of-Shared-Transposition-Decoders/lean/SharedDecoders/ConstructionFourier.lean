import SharedDecoders.ConstructionBlockRecovery
import SharedDecoders.ConstructionCRT
import SharedDecoders.CompositionBand

/-! # The actual outer Fourier change of coordinates

An injective additive character supplies the complete cyclic eigenbasis.
The same transform is applied to both outer indices, preserving transpose.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F : Type*} [Field F] {m : ℕ} [NeZero m]

def fourierSynthesis (χ : AddChar (ZMod m) F) : (Fin m → F) →ₗ[F] (ZMod m → F) where
  toFun a c := ∑ i, χ ((i.val : ZMod m) * c) * a i
  map_add' a b := by funext c; simp [mul_add, Finset.sum_add_distrib]
  map_smul' k a := by funext c; simp [Finset.mul_sum, mul_left_comm]

omit [NeZero m] in
theorem fourierSynthesis_injective (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    Function.Injective (fourierSynthesis χ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hinj : Function.Injective (fun i : Fin m => χ (i.val : ZMod m)) := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg ZMod.val (hχ hij)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hh
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
  intro j
  have hh := congrFun ha (j.val : ZMod m)
  change (∑ i : Fin m, χ ((i.val : ZMod m) * (j.val : ZMod m)) * a i) = 0 at hh
  simp only [character_nat_mul] at hh
  simpa only [mul_comm] using hh

noncomputable def fourierEquiv (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    (Fin m → F) ≃ₗ[F] (ZMod m → F) :=
  (fourierSynthesis χ).linearEquivOfInjective (fourierSynthesis_injective χ hχ)
    (by simp [Module.finrank_fintype_fun_eq_card, ZMod.card])

@[simp] theorem fourierEquiv_apply (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (a : Fin m → F) (c : ZMod m) :
    fourierEquiv χ hχ a c = ∑ i, χ ((i.val : ZMod m) * c) * a i := rfl

def outerFourier {I : Type*} (χ : AddChar (ZMod m) F) :
    (Fin m → Fin m → I → I → F) →ₗ[F] LiftState (ZMod m) I F where
  toFun X ar hc := ∑ i, ∑ j,
    χ ((i.val : ZMod m) * ar.1) * χ ((j.val : ZMod m) * hc.1) * X i j ar.2 hc.2
  map_add' X Y := by funext ar hc; simp [mul_add, Finset.sum_add_distrib]
  map_smul' k X := by funext ar hc; simp [Finset.mul_sum, mul_left_comm]

omit [NeZero m] in
theorem outerFourier_injective {I : Type*}
    (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    Function.Injective (outerFourier (I := I) χ) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  have rowzero (a : ZMod m) (r c : I) :
      (fun j : Fin m => ∑ i, χ ((i.val : ZMod m) * a) * X i j r c) = 0 := by
    apply (fourierSynthesis_injective χ hχ)
    rw [map_zero]
    funext h
    have hh := congrFun (congrFun hX (a,r)) (h,c)
    change (∑ i, ∑ j, χ ((i.val : ZMod m) * a) * χ ((j.val : ZMod m) * h) * X i j r c) = 0 at hh
    change (∑ j, χ ((j.val : ZMod m) * h) * ∑ i, χ ((i.val : ZMod m) * a) * X i j r c) = 0
    rw [Finset.sum_comm] at hh
    simpa only [Finset.mul_sum, mul_left_comm, mul_assoc] using hh
  funext i j r c
  have colzero : (fun i : Fin m => X i j r c) = 0 := by
    apply (fourierSynthesis_injective χ hχ)
    rw [map_zero]
    funext a
    exact congrFun (rowzero a r c) j
  exact congrFun colzero i

noncomputable def outerFourierEquiv {I : Type*} [Fintype I]
    (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ) :
    (Fin m → Fin m → I → I → F) ≃ₗ[F] LiftState (ZMod m) I F :=
  (outerFourier χ).linearEquivOfInjective (outerFourier_injective χ hχ)
    (by simp only [Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fin, Fintype.card_prod, ZMod.card, Nat.cast_mul]; ring)

omit [NeZero m] in
theorem outerFourier_swap {I : Type*} (χ : AddChar (ZMod m) F)
    (X : Fin m → Fin m → I → I → F) :
    outerFourier χ (fun i j r c => X j i c r) = liftSwap (outerFourier χ X) := by
  funext ar hc
  change (∑ i, ∑ j, χ ((i.val : ZMod m) * ar.1) * χ ((j.val : ZMod m) * hc.1) * X j i hc.2 ar.2) =
    ∑ i, ∑ j, χ ((i.val : ZMod m) * hc.1) * χ ((j.val : ZMod m) * ar.1) * X i j hc.2 ar.2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end SharedDecoders
