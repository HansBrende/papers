import SharedDecoders.ConstructionSymmetric

/-! # The cyclic anti-diagonal averaging projector

The outer indices are any finite abelian group. The seed coordinates are an
arbitrary type; no Fourier diagonalization, division by two or scalar decoder
linearity is involved in the projector identities.
-/

namespace SharedDecoders

open Module
open scoped BigOperators

variable {F A G I : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup G] [Fintype G]

abbrev LiftState (G I A : Type*) := (G × I) → (G × I) → A

def orbitAverage : LiftState G I A →ₗ[F] (G → I → I → A) where
  toFun X z r c := (Fintype.card G : F)⁻¹ • ∑ a : G, X (a, r) (z - a, c)
  map_add' X Y := by
    funext z r c
    simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add]
  map_smul' k X := by
    funext z r c
    simp only [Pi.smul_apply, ← Finset.smul_sum]
    exact smul_comm _ k _

def orbitInflate : (G → I → I → A) →ₗ[F] LiftState G I A where
  toFun Y ar hc := Y (ar.1 + hc.1) ar.2 hc.2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem orbitAverage_apply (X : LiftState G I A) (z : G) (r c : I) :
    orbitAverage (F := F) X z r c =
      (Fintype.card G : F)⁻¹ • ∑ a : G, X (a, r) (z - a, c) := rfl

omit [Fintype G] in
@[simp] theorem orbitInflate_apply (Y : G → I → I → A) (ar hc : G × I) :
    orbitInflate (F := F) Y ar hc = Y (ar.1 + hc.1) ar.2 hc.2 := rfl

theorem orbitAverage_inflate (hG : (Fintype.card G : F) ≠ 0) (Y : G → I → I → A) :
    orbitAverage (F := F) (orbitInflate (F := F) Y) = Y := by
  funext z r c
  have hsub (a : G) : a + (z - a) = z := by abel
  simp only [orbitAverage_apply, orbitInflate_apply, hsub, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hG, one_smul]

def cyclicProjector : LiftState G I A →ₗ[F] LiftState G I A :=
  (orbitInflate (F := F)).comp (orbitAverage (F := F))

theorem cyclicProjector_idempotent (hG : (Fintype.card G : F) ≠ 0)
    (X : LiftState G I A) :
    cyclicProjector (F := F) (cyclicProjector (F := F) X) = cyclicProjector (F := F) X := by
  exact congrArg (orbitInflate (F := F)) (orbitAverage_inflate hG (orbitAverage (F := F) X))

def liftSwap (X : LiftState G I A) : LiftState G I A := fun ar hc => X hc ar

theorem orbitAverage_swap (X : LiftState G I A) (z : G) (r c : I) :
    orbitAverage (F := F) (liftSwap X) z r c = orbitAverage (F := F) X z c r := by
  simp only [orbitAverage_apply, liftSwap]
  congr 1
  let e : G ≃ G :=
    { toFun := fun a => z - a
      invFun := fun a => z - a
      left_inv := by intro a; exact sub_sub_cancel z a
      right_inv := by intro a; exact sub_sub_cancel z a }
  have hh := e.sum_comp (fun a => X (a, c) (z - a, r))
  simpa only [e, Equiv.coe_fn_mk, sub_sub_cancel] using hh

theorem cyclicProjector_swap (X : LiftState G I A) :
    cyclicProjector (F := F) (liftSwap X) = liftSwap (cyclicProjector (F := F) X) := by
  funext ar hc
  change orbitAverage (F := F) (liftSwap X) (ar.1 + hc.1) ar.2 hc.2 =
    orbitAverage (F := F) X (hc.1 + ar.1) hc.2 ar.2
  rw [orbitAverage_swap, add_comm]

variable [AddCommGroup I]

def liftRot (u : G) (v : I) (X : LiftState G I A) : LiftState G I A :=
  fun ar hc => X ar (hc.1 + u, hc.2 + v)

theorem orbitAverage_rot (X : LiftState G I A) (u z : G) (v r c : I) :
    orbitAverage (F := F) (liftRot u v X) z r c =
      orbitAverage (F := F) X (z + u) r (c + v) := by
  simp only [orbitAverage_apply, liftRot]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  abel

theorem cyclicProjector_rot (X : LiftState G I A) (u : G) (v : I) :
    cyclicProjector (F := F) (liftRot u v X) = liftRot u v (cyclicProjector (F := F) X) := by
  funext ar hc
  change orbitAverage (F := F) (liftRot u v X) (ar.1 + hc.1) ar.2 hc.2 =
    orbitAverage (F := F) X (ar.1 + (hc.1 + u)) ar.2 (hc.2 + v)
  rw [orbitAverage_rot, add_assoc]

end SharedDecoders
