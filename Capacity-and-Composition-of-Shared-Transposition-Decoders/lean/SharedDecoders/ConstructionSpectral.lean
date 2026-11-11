import SharedDecoders.ConstructionFourier

/-! # Compression of a periodic shared rule to actual seed rules -/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F κ : Type*} [Field F] {m s : ℕ} [NeZero m]

def spectralBlock (χ : AddChar (ZMod m) F) (i j : Fin m) :
    State s F →ₗ[F] LiftState (ZMod m) (ZMod s) F where
  toFun X ar hc := χ ((i.val : ZMod m) * ar.1) *
    χ ((j.val : ZMod m) * hc.1) * X ar.2 hc.2
  map_add' X Y := by funext ar hc; simp [mul_add]
  map_smul' k X := by funext ar hc; simp [mul_left_comm]

noncomputable def rowAnalysis (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (i : Fin m) : (ZMod m × ZMod s → F) →ₗ[F] (ZMod s → F) where
  toFun Y r := (fourierEquiv χ hχ).symm (fun a => Y (a,r)) i
  map_add' X Y := by
    funext r
    change (fourierEquiv χ hχ).symm ((fun a => X (a,r)) + (fun a => Y (a,r))) i = _
    rw [map_add]
    rfl
  map_smul' k X := by
    funext r
    change (fourierEquiv χ hχ).symm (k • (fun a => X (a,r))) i = _
    rw [map_smul]
    rfl

theorem rowAnalysis_outerFourier (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (X : Fin m → Fin m → State s F) (u : ZMod m) (v : ZMod s) (i : Fin m) (r : ZMod s) :
    rowAnalysis χ hχ i ((outerFourier χ X) (u,v)) r =
      ∑ j, χ ((j.val : ZMod m) * u) * X j i v r := by
  have hh : (fun a => (outerFourier χ X) (u,v) (a,r)) =
      fourierEquiv χ hχ (fun i => ∑ j, χ ((j.val : ZMod m) * u) * X j i v r) := by
    funext a
    change (∑ j, ∑ i, χ ((j.val : ZMod m) * u) * χ ((i.val : ZMod m) * a) * X j i v r) = _
    rw [Finset.sum_comm]
    simp only [fourierEquiv_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (fourierEquiv χ hχ).symm (fun a => (outerFourier χ X) (u,v) (a,r)) i = _
  rw [hh, LinearEquiv.symm_apply_apply]

omit [NeZero m] in
theorem liftRot_outerFourier (χ : AddChar (ZMod m) F)
    (X : Fin m → Fin m → State s F) (u : ZMod m) (v : ZMod s) :
    liftRot u v (outerFourier χ X) =
      ∑ j, χ ((j.val : ZMod m) * u) • ∑ a, spectralBlock χ a j (rot v (X a j)) := by
  funext ar hc
  change (∑ a, ∑ j, χ ((a.val : ZMod m) * ar.1) *
    χ ((j.val : ZMod m) * (hc.1 + u)) * X a j ar.2 (hc.2 + v)) = _
  rw [Finset.sum_comm]
  simp only [mul_add, χ.map_add_eq_mul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  change χ ((a.val : ZMod m) * ar.1) *
    (χ ((j.val : ZMod m) * hc.1) * χ ((j.val : ZMod m) * u)) * X a j ar.2 (hc.2 + v) =
    χ ((j.val : ZMod m) * u) *
    (χ ((a.val : ZMod m) * ar.1) * χ ((j.val : ZMod m) * hc.1) * X a j ar.2 (hc.2 + v))
  ring

def IsProductLinearSharedCode (p : ZMod s → κ)
    (C : Submodule F (LiftState (ZMod m) (ZMod s) F)) : Prop :=
  ∃ f : κ → LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F),
    ∀ X ∈ C, ∀ u v, X (u,v) = f (p v) (liftRot u v X)

noncomputable def compressedDecoder (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (f : κ → LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F))
    (j i a : Fin m) (J : κ) : State s F →ₗ[F] (ZMod s → F) :=
  (rowAnalysis χ hχ i).comp ((f J).comp (spectralBlock χ a j))

noncomputable def compressedRule (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (p : ZMod s → κ)
    (f : κ → LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F))
    (j i a : Fin m) : State s F →ₗ[F] State s F where
  toFun X r c := compressedDecoder χ hχ f j i a (p c) (rot c X) r
  map_add' X Y := by
    funext r c
    change compressedDecoder χ hχ f j i a (p c) (rot c X + rot c Y) r = _
    rw [map_add]
    rfl
  map_smul' k X := by
    funext r c
    change compressedDecoder χ hχ f j i a (p c) (k • rot c X) r = _
    rw [map_smul]
    rfl

def seedSwapEquiv : State s F ≃ₗ[F] State s F where
  toFun := swap
  invFun := swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem seedSwapEquiv_apply (X : State s F) (r c : ZMod s) :
    seedSwapEquiv (F := F) X r c = X c r := rfl

@[simp] theorem compressedRule_apply (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (p : ZMod s → κ)
    (f : κ → LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F))
    (j i a : Fin m) (X : State s F) (r c : ZMod s) :
    compressedRule χ hχ p f j i a X r c =
      compressedDecoder χ hχ f j i a (p c) (rot c X) r := rfl

theorem compressedAgreement (χ : AddChar (ZMod m) F) (hχ : Function.Injective χ)
    (p : ZMod s → κ)
    (f : κ → LiftState (ZMod m) (ZMod s) F →ₗ[F] (ZMod m × ZMod s → F))
    (X : Fin m → Fin m → State s F)
    (hX : ∀ u v, outerFourier χ X (u,v) = f (p v) (liftRot u v (outerFourier χ X))) :
    X ∈ blockAgreement seedSwapEquiv (compressedRule χ hχ p f) := by
  intro j i
  funext r v
  have hcoeff :
      (fun j => X j i v r) =
      (fun j => ∑ a, compressedDecoder χ hχ f j i a (p v) (rot v (X a j)) r) := by
    apply fourierSynthesis_injective χ hχ
    funext u
    have hh := congrFun (congrArg (rowAnalysis χ hχ i) (hX u v)) r
    rw [rowAnalysis_outerFourier, liftRot_outerFourier, map_sum] at hh
    simp only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    exact hh
  simpa only [Finset.sum_apply, seedSwapEquiv_apply, compressedRule_apply] using congrFun hcoeff j

end SharedDecoders
