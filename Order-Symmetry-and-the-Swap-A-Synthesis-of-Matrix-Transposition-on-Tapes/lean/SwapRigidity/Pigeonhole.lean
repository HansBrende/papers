import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.CompleteLattice.Finset

/-!
# The pigeonhole lemma against a translate

Let `τ`, `K`, `T` be linear endomorphisms of a finite-dimensional space `V` over a field `F`.
The *code* of the rule `K` for the demand `τ` is `ker (τ - K)`.  This file proves the
exercise-level linear algebra behind the translate pigeonhole:

* `finrank_range_commutator_le`: a commutator `[S, T]` has rank at most twice the rank of `S`;
* `two_mul_finrank_ker_sub_le_ker`, `two_mul_finrank_ker_sub_le`,
  `two_mul_finrank_ker_sub_le_of_commute`: the bound
  `2 * dim ker (τ - K) ≤ dim V + dim ker [τ, T] + rank [K, T]`;
* `finrank_range_commutator_comp_le`: commutator rank is subadditive under composition;
* `card_mul_finrank_add_le_iInf_comap`, `mul_finrank_le_add_finrank_iInf_comap`: the
  multi-translate count, `(s + 1) * dim 𝒳 ≤ s * dim V + dim ⋂ᵢ Tᵢ⁻¹ 𝒳`.

Here `[S, T]` is written out as `S ∘ₗ T - T ∘ₗ S`.
-/

namespace SwapRigidity

open Module LinearMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-! ### Rank of sums and composites -/

/-- The rank of a sum of two linear maps is at most the sum of their ranks. -/
theorem finrank_range_add_le (f g : V →ₗ[F] V) :
    finrank F (range (f + g)) ≤ finrank F (range f) + finrank F (range g) :=
  (Submodule.finrank_mono (range_add_le f g)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a difference of two linear maps is at most the sum of their ranks. -/
theorem finrank_range_sub_le (f g : V →ₗ[F] V) :
    finrank F (range (f - g)) ≤ finrank F (range f) + finrank F (range g) := by
  have h := finrank_range_add_le f (-g)
  rwa [← sub_eq_add_neg, LinearMap.range_neg] at h

/-- The rank of a composite is at most the rank of the outer map. -/
theorem finrank_range_comp_le_left (g f : V →ₗ[F] V) :
    finrank F (range (g ∘ₗ f)) ≤ finrank F (range g) :=
  Submodule.finrank_mono (range_comp_le_range f g)

/-- The rank of a composite is at most the rank of the inner map. -/
theorem finrank_range_comp_le_right (g f : V →ₗ[F] V) :
    finrank F (range (g ∘ₗ f)) ≤ finrank F (range f) := by
  rw [range_comp]
  exact Submodule.finrank_map_le g _

/-! ### The commutator lemma -/

/-- A commutator has rank at most twice the rank of either factor:
`rank [S, T] ≤ 2 * rank S`. -/
theorem finrank_range_commutator_le (S T : V →ₗ[F] V) :
    finrank F (range (S ∘ₗ T - T ∘ₗ S)) ≤ 2 * finrank F (range S) := by
  have h1 := finrank_range_sub_le (S ∘ₗ T) (T ∘ₗ S)
  have h2 := finrank_range_comp_le_left S T
  have h3 := finrank_range_comp_le_right T S
  omega

/-- **Pigeonhole lemma, first inequality.**
`2 * dim ker (τ - K) ≤ dim V + dim ker [τ - K, T]` for all endomorphisms `τ`, `K`, `T`. -/
theorem two_mul_finrank_ker_sub_le_ker (τ K T : V →ₗ[F] V) :
    2 * finrank F (ker (τ - K)) ≤
      finrank F V + finrank F (ker ((τ - K) ∘ₗ T - T ∘ₗ (τ - K))) := by
  have h1 := finrank_range_commutator_le (τ - K) T
  have h2 := finrank_range_add_finrank_ker (τ - K)
  have h3 := finrank_range_add_finrank_ker ((τ - K) ∘ₗ T - T ∘ₗ (τ - K))
  omega

/-- The kernel of `[τ - K, T]` is no larger than `dim ker [τ, T] + rank [K, T]`. -/
theorem finrank_ker_commutator_sub_le (τ K T : V →ₗ[F] V) :
    finrank F (ker ((τ - K) ∘ₗ T - T ∘ₗ (τ - K))) ≤
      finrank F (ker (τ ∘ₗ T - T ∘ₗ τ)) + finrank F (range (K ∘ₗ T - T ∘ₗ K)) := by
  have e : τ ∘ₗ T - T ∘ₗ τ =
      ((τ - K) ∘ₗ T - T ∘ₗ (τ - K)) + (K ∘ₗ T - T ∘ₗ K) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub]
    abel
  have h1 := finrank_range_add_le ((τ - K) ∘ₗ T - T ∘ₗ (τ - K)) (K ∘ₗ T - T ∘ₗ K)
  rw [← e] at h1
  have h2 := finrank_range_add_finrank_ker (τ ∘ₗ T - T ∘ₗ τ)
  have h3 := finrank_range_add_finrank_ker ((τ - K) ∘ₗ T - T ∘ₗ (τ - K))
  omega

/-- **Pigeonhole lemma.**
`2 * dim ker (τ - K) ≤ dim V + dim ker [τ, T] + rank [K, T]` for all endomorphisms
`τ`, `K`, `T` of a finite-dimensional space. -/
theorem two_mul_finrank_ker_sub_le (τ K T : V →ₗ[F] V) :
    2 * finrank F (ker (τ - K)) ≤
      finrank F V + finrank F (ker (τ ∘ₗ T - T ∘ₗ τ)) +
        finrank F (range (K ∘ₗ T - T ∘ₗ K)) := by
  have h1 := two_mul_finrank_ker_sub_le_ker τ K T
  have h2 := finrank_ker_commutator_sub_le τ K T
  omega

/-- **Pigeonhole lemma, commuting case.**  If the rule `K` commutes with `T`, then
`2 * dim ker (τ - K) ≤ dim V + dim ker [τ, T]`. -/
theorem two_mul_finrank_ker_sub_le_of_commute (τ K T : V →ₗ[F] V) (h : K ∘ₗ T = T ∘ₗ K) :
    2 * finrank F (ker (τ - K)) ≤ finrank F V + finrank F (ker (τ ∘ₗ T - T ∘ₗ τ)) := by
  have h1 := two_mul_finrank_ker_sub_le τ K T
  rw [h, sub_self, LinearMap.range_zero, finrank_bot] at h1
  omega

/-- **Commutator rank is subadditive under composition.**
`rank [K₂ K₁, T] ≤ rank [K₁, T] + rank [K₂, T]`, because
`[K₂ K₁, T] = K₂ [K₁, T] + [K₂, T] K₁`. -/
theorem finrank_range_commutator_comp_le (K₁ K₂ T : V →ₗ[F] V) :
    finrank F (range ((K₂ ∘ₗ K₁) ∘ₗ T - T ∘ₗ (K₂ ∘ₗ K₁))) ≤
      finrank F (range (K₁ ∘ₗ T - T ∘ₗ K₁)) + finrank F (range (K₂ ∘ₗ T - T ∘ₗ K₂)) := by
  have e : (K₂ ∘ₗ K₁) ∘ₗ T - T ∘ₗ (K₂ ∘ₗ K₁) =
      K₂ ∘ₗ (K₁ ∘ₗ T - T ∘ₗ K₁) + (K₂ ∘ₗ T - T ∘ₗ K₂) ∘ₗ K₁ := by
    ext x
    simp
  rw [e]
  have h1 := finrank_range_add_le (K₂ ∘ₗ (K₁ ∘ₗ T - T ∘ₗ K₁)) ((K₂ ∘ₗ T - T ∘ₗ K₂) ∘ₗ K₁)
  have h2 := finrank_range_comp_le_right K₂ (K₁ ∘ₗ T - T ∘ₗ K₁)
  have h3 := finrank_range_comp_le_left (K₂ ∘ₗ T - T ∘ₗ K₂) K₁
  omega

/-! ### The multi-translate count -/

/-- Codimension does not grow under preimages: for `f : W → V` and a subspace `𝒳 ≤ V`,
`dim W + dim 𝒳 ≤ dim V + dim f⁻¹ 𝒳`. -/
theorem finrank_add_le_finrank_add_finrank_comap {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (𝒳 : Submodule F V) (f : W →ₗ[F] V) :
    finrank F W + finrank F 𝒳 ≤ finrank F V + finrank F (𝒳.comap f) := by
  have e : 𝒳.comap f = ker (𝒳.mkQ ∘ₗ f) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h1 := finrank_range_add_finrank_ker (𝒳.mkQ ∘ₗ f)
  have h2 : finrank F (range (𝒳.mkQ ∘ₗ f)) ≤ finrank F (V ⧸ 𝒳) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank 𝒳
  rw [e]
  omega

/-- The preimage of a subspace under an endomorphism is at least as large as the subspace. -/
theorem finrank_le_finrank_comap (𝒳 : Submodule F V) (f : V →ₗ[F] V) :
    finrank F 𝒳 ≤ finrank F (𝒳.comap f) := by
  have h := finrank_add_le_finrank_add_finrank_comap 𝒳 f
  omega

/-- Codimension is subadditive under intersection:
`dim A + dim B ≤ dim V + dim (A ⊓ B)`. -/
theorem finrank_add_finrank_le_add_finrank_inf (A B : Submodule F V) :
    finrank F A + finrank F B ≤ finrank F V + finrank F (A ⊓ B : Submodule F V) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h2 := Submodule.finrank_le (A ⊔ B)
  omega

/-- **Multi-translate count, finset form.**  For a subspace `𝒳`, a finite set `I` of indices
and endomorphisms `T i`, the common preimage `⨅ i ∈ I, (T i)⁻¹ 𝒳` satisfies
`|I| * dim 𝒳 + dim V ≤ |I| * dim V + dim ⨅ i ∈ I, (T i)⁻¹ 𝒳`. -/
theorem card_mul_finrank_add_le_iInf_comap {ι : Type*} (I : Finset ι) (𝒳 : Submodule F V)
    (T : ι → V →ₗ[F] V) :
    I.card * finrank F 𝒳 + finrank F V ≤
      I.card * finrank F V + finrank F (⨅ i ∈ I, 𝒳.comap (T i) : Submodule F V) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have e : (⨅ i ∈ (∅ : Finset ι), 𝒳.comap (T i) : Submodule F V) = ⊤ := by simp
    rw [e, finrank_top, Finset.card_empty, zero_mul, zero_mul]
  | insert a I ha ih =>
    rw [Finset.card_insert_of_notMem ha, Finset.iInf_insert, add_mul, add_mul, one_mul, one_mul]
    have h1 := finrank_le_finrank_comap 𝒳 (T a)
    have h2 := finrank_add_finrank_le_add_finrank_inf (𝒳.comap (T a))
      (⨅ i ∈ I, 𝒳.comap (T i))
    omega

/-- **Multi-translate count.**  For a subspace `𝒳` and `s + 1` endomorphisms `T i`,
`(s + 1) * dim 𝒳 ≤ s * dim V + dim ⨅ i, (T i)⁻¹ 𝒳`. -/
theorem mul_finrank_le_add_finrank_iInf_comap {s : ℕ} (𝒳 : Submodule F V)
    (T : Fin (s + 1) → V →ₗ[F] V) :
    (s + 1) * finrank F 𝒳 ≤
      s * finrank F V + finrank F (⨅ i, 𝒳.comap (T i) : Submodule F V) := by
  have h := card_mul_finrank_add_le_iInf_comap Finset.univ 𝒳 T
  have e : (⨅ i ∈ (Finset.univ : Finset (Fin (s + 1))), 𝒳.comap (T i) : Submodule F V) =
      ⨅ i, 𝒳.comap (T i) := by simp
  rw [e, Finset.card_univ, Fintype.card_fin, add_mul, one_mul, add_mul, one_mul] at h
  rw [add_mul, one_mul]
  omega

end SwapRigidity
