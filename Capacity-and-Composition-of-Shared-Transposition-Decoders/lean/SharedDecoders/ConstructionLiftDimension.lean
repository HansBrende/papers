import SharedDecoders.ConstructionLift

/-! # Exact dimensions of the cyclic lift, in every allowed characteristic -/

namespace SharedDecoders

open Module LinearMap

variable {F A G I : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup G] [Fintype G]

def averageSymmetric : symmetricSpace (F := F) (A := A) (I := G × I) →ₗ[F]
    (G → symmetricSpace (F := F) (A := A) (I := I)) where
  toFun X z := ⟨orbitAverage (F := F) (X : LiftState G I A) z, by
    intro r c
    have hswap : liftSwap (X : LiftState G I A) = X := by
      funext ar hc
      exact X.2 hc ar
    have hh := orbitAverage_swap (F := F) (X : LiftState G I A) z r c
    rwa [hswap] at hh⟩
  map_add' X Y := by funext z; apply Subtype.ext; exact congrFun (map_add (orbitAverage (F := F)) _ _) z
  map_smul' a X := by funext z; apply Subtype.ext; exact congrFun (map_smul (orbitAverage (F := F)) a _) z

theorem averageSymmetric_surjective (hG : (Fintype.card G : F) ≠ 0) :
    Function.Surjective (averageSymmetric (F := F) (A := A) (G := G) (I := I)) := by
  intro Y
  let Z : G → I → I → A := fun z => (Y z : I → I → A)
  have hsym : orbitInflate (F := F) Z ∈ symmetricSpace (F := F) := by
    intro ar hc
    change Z (ar.1 + hc.1) ar.2 hc.2 = Z (hc.1 + ar.1) hc.2 ar.2
    rw [add_comm hc.1 ar.1]
    exact (Y (ar.1 + hc.1)).2 _ _
  refine ⟨⟨orbitInflate (F := F) Z, hsym⟩, ?_⟩
  funext z
  apply Subtype.ext
  exact congrFun (orbitAverage_inflate hG Z) z

variable [Fintype I] [FiniteDimensional F A]

omit [Fintype I] [FiniteDimensional F A] in
theorem finrank_averageSymmetric_ker :
    finrank F (LinearMap.ker (averageSymmetric (F := F) (A := A) (G := G) (I := I))) =
      finrank F (liftNull (F := F) (A := A) (G := G) (I := I)) := by
  let S := symmetricSpace (F := F) (A := A) (I := G × I)
  let P := orbitAverage (F := F) (A := A) (G := G) (I := I)
  have hker : LinearMap.ker averageSymmetric = P.ker.comap S.subtype := by
    ext X
    constructor
    · intro h
      have hh := LinearMap.mem_ker.mp h
      apply LinearMap.mem_ker.mpr
      funext z r c
      exact congrFun (congrFun (congrArg Subtype.val (congrFun hh z)) r) c
    · intro h
      apply LinearMap.mem_ker.mpr
      funext z
      apply Subtype.ext
      exact congrFun (LinearMap.mem_ker.mp h) z
  rw [hker]
  have hco : (S ⊓ P.ker).comap S.subtype = P.ker.comap S.subtype := by
    ext x
    simp
  rw [← hco]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : S ⊓ P.ker ≤ S)).finrank_eq

theorem symmetric_dimension_split (hG : (Fintype.card G : F) ≠ 0) :
    Fintype.card G * finrank F (symmetricSpace (F := F) (A := A) (I := I)) +
      finrank F (liftNull (F := F) (A := A) (G := G) (I := I)) =
      finrank F (symmetricSpace (F := F) (A := A) (I := G × I)) := by
  have hh := LinearMap.finrank_range_add_finrank_ker
    (averageSymmetric (F := F) (A := A) (G := G) (I := I))
  rw [LinearMap.range_eq_top.mpr (averageSymmetric_surjective hG), finrank_top,
    finrank_averageSymmetric_ker] at hh
  simpa [Module.finrank_pi_fintype] using hh

theorem finrank_inflateSeed_range (hG : (Fintype.card G : F) ≠ 0)
    (C : Submodule F (I → I → A)) :
    finrank F (LinearMap.range (inflateSeed (G := G) C)) = Fintype.card G * finrank F C := by
  have hinj : Function.Injective (inflateSeed (G := G) C) := by
    intro X Y h
    change orbitInflate (F := F) (fun z => (X z : I → I → A)) =
      orbitInflate (F := F) (fun z => (Y z : I → I → A)) at h
    have hh := orbitInflate_injective hG h
    funext z
    apply Subtype.ext
    exact congrFun hh z
  rw [LinearMap.finrank_range_of_inj hinj]
  simp [Module.finrank_pi_fintype]

theorem finrank_liftedCode (hG : (Fintype.card G : F) ≠ 0)
    (C : Submodule F (I → I → A)) :
    finrank F (liftedCode (G := G) C) =
      finrank F (liftNull (F := F) (A := A) (G := G) (I := I)) +
      Fintype.card G * finrank F C := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (liftNull (F := F) (G := G)) (LinearMap.range (inflateSeed (G := G) C))
  rw [(liftNull_disjoint_seed hG C).eq_bot, finrank_bot, add_zero,
    finrank_inflateSeed_range hG C] at hh
  exact hh

/-- The exact lifted dimension without divisions or characteristic restrictions
other than the invertibility of the outer group cardinality. -/
theorem two_mul_finrank_liftedCode (hG : (Fintype.card G : F) ≠ 0)
    (C : Submodule F (I → I → A)) :
    2 * finrank F (liftedCode (G := G) C) +
      Fintype.card G * (Fintype.card I * Fintype.card I * finrank F A) =
      (Fintype.card G * Fintype.card I) * (Fintype.card G * Fintype.card I) * finrank F A +
      2 * Fintype.card G * finrank F C := by
  have hsplit := symmetric_dimension_split (A := A) (I := I) hG
  have hbig := two_mul_finrank_symmetricSpace (F := F) (A := A) (I := G × I)
  have hsmall := congrArg (fun n => Fintype.card G * n)
    (two_mul_finrank_symmetricSpace (F := F) (A := A) (I := I))
  have hcode := finrank_liftedCode hG C
  rw [Fintype.card_prod] at hbig
  nlinarith only [hsplit, hbig, hsmall, hcode]

end SharedDecoders
