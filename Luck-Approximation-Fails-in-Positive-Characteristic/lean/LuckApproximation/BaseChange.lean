import LuckApproximation.Sanity
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Ranks under a field extension

For a field extension `k → K` and a matrix `A` over `k[G]`, the kernel of `φ_{G/N}` can only grow when the
coefficients of `A` are mapped to `K` (`finrank_ker_le_map`): a `k`-basis of the kernel stays linearly
independent over `K`, by Mathlib's `linearIndependent_algebraMap_comp_iff` applied to coordinates in the basis
of group elements. (Equality holds, since ranks of matrices over a field do not change under extension, but only
this inequality is used: it transfers a non-negligible kernel from `𝔽₃` to every field of characteristic 3.)
-/

namespace Luck

open Module

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {G : Type*} [Group G]

/-- Mapping coefficients commutes with passing to a quotient group. -/
theorem quotientMatrix_map (N : Subgroup G) [N.Normal] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra k G)) :
    quotientMatrix K N (A.map (MonoidAlgebra.mapRingHom G (algebraMap k K))) =
      (quotientMatrix k N A).map (MonoidAlgebra.mapRingHom (G ⧸ N) (algebraMap k K)) := by
  have h : (MonoidAlgebra.mapDomainRingHom K (QuotientGroup.mk' N)).comp
      (MonoidAlgebra.mapRingHom G (algebraMap k K)) =
      (MonoidAlgebra.mapRingHom (G ⧸ N) (algebraMap k K)).comp
        (MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' N)) := by
    apply MonoidAlgebra.ringHom_ext <;> intros <;>
      simp [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single]
  funext i j
  simp only [quotientMatrix, Matrix.map_apply]
  exact DFunLike.congr_fun h (A i j)

/-- Coordinates of a vector over `R[Q]` in the basis of group elements. -/
def coordsLin (R : Type*) [CommSemiring R] (n : ℕ) (Q : Type*) :
    (Fin n → MonoidAlgebra R Q) →ₗ[R] (Fin n × Q → R) where
  toFun x p := (x p.1).coeff p.2
  map_add' x y := by funext p; simp
  map_smul' c x := by funext p; simp

theorem coordsLin_injective (R : Type*) [CommSemiring R] (n : ℕ) (Q : Type*) :
    Function.Injective (coordsLin R n Q) := by
  intro x y h
  funext i
  apply MonoidAlgebra.coeff_injective
  ext q
  exact congrFun h (i, q)

/-- The kernel only grows under a field extension. -/
theorem finrank_ker_le_map (N : Subgroup G) [N.Normal] [N.FiniteIndex] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (MonoidAlgebra k G)) :
    finrank k (LinearMap.ker (phi k N A)) ≤
      finrank K (LinearMap.ker (phi K N (A.map (MonoidAlgebra.mapRingHom G (algebraMap k K))))) := by
  classical
  have : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  have := finiteDimensional_quotient k N
  have := finiteDimensional_quotient K N
  have : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).mpr (algebraMap k K).injective
  set f := MonoidAlgebra.mapRingHom (G ⧸ N) (algebraMap k K)
  set V := LinearMap.ker (phi k N A)
  set b := Module.finBasis k V
  let v : Fin (finrank k V) → (Fin n → MonoidAlgebra K (G ⧸ N)) := fun i => f ∘ (b i : V).1
  have hv_mem : ∀ i, v i ∈ LinearMap.ker (phi K N (A.map (MonoidAlgebra.mapRingHom G (algebraMap k K)))) := by
    intro i
    have hb : phi k N A (b i : V).1 = 0 := (b i).2
    rw [LinearMap.mem_ker]
    funext j
    have := congrArg f (congrFun hb j)
    simp only [phi, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, map_zero] at this ⊢
    rw [quotientMatrix_map, ← RingHom.map_vecMul]
    exact this
  have h1 : LinearIndependent k (fun i => coordsLin k n (G ⧸ N) (b i : V).1) :=
    (b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)).map' _
      (LinearMap.ker_eq_bot.mpr (coordsLin_injective k n _))
  have h2 := (linearIndependent_algebraMap_comp_iff (R := k) (S := K)).mpr h1
  have h3 : (fun i => algebraMap k K ∘ coordsLin k n (G ⧸ N) (b i : V).1) =
      coordsLin K n (G ⧸ N) ∘ v := by
    funext i p
    simp [v, coordsLin, f, MonoidAlgebra.coeff_mapRingHom]
  rw [h3] at h2
  have hli : LinearIndependent K v := h2.of_comp _
  let w : Fin (finrank k V) →
      LinearMap.ker (phi K N (A.map (MonoidAlgebra.mapRingHom G (algebraMap k K)))) :=
    fun i => ⟨v i, hv_mem i⟩
  have hw : LinearIndependent K w := LinearIndependent.of_comp (Submodule.subtype _) hli
  simpa using hw.fintype_card_le_finrank

end Luck
