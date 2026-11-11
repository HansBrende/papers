import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Restricted ranks and a modular subspace bound

These lemmas charge the rank of a map that vanishes on a retained subspace and
on its intersection with a second space. The dimensions are actual subspaces,
not an externally supplied rank certificate.
-/

namespace SharedDecoders

open Module

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V]

theorem finrank_map_add_inf_ker (C : Submodule F V) (f : V →ₗ[F] W) :
    finrank F (C.map f) + finrank F (C ⊓ LinearMap.ker f : Submodule F V) = finrank F C := by
  have hn := (f.comp C.subtype).finrank_range_add_finrank_ker
  have hk : finrank F (LinearMap.ker (f.comp C.subtype)) =
      finrank F (C ⊓ LinearMap.ker f : Submodule F V) := by
    rw [LinearMap.ker_comp]
    have he : (C ⊓ f.ker).comap C.subtype = f.ker.comap C.subtype := by ext x; simp
    rw [← he]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ f.ker ≤ C)).finrank_eq
  rw [LinearMap.range_comp, Submodule.range_subtype, hk] at hn
  exact hn

theorem restricted_rank_modular_bound (C U H : Submodule F V) (f : V →ₗ[F] W)
    (hUC : U ≤ C) (hkill : U ⊔ (C ⊓ H) ≤ LinearMap.ker f) :
    finrank F (C.map f) + finrank F (U ⊔ H : Submodule F V) ≤
      finrank F (C ⊔ H : Submodule F V) := by
  have hle : U ⊔ (C ⊓ H) ≤ C ⊓ LinearMap.ker f :=
    le_inf (sup_le hUC inf_le_left) hkill
  have hk := Submodule.finrank_mono hle
  have hn := finrank_map_add_inf_ker C f
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq U (C ⊓ H)
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq U H
  have h₃ := Submodule.finrank_sup_add_finrank_inf_eq C H
  rw [← inf_assoc, inf_eq_left.mpr hUC] at h₁
  omega

theorem restricted_rank_ambient_bound (C U H : Submodule F V) (f : V →ₗ[F] W)
    (hUC : U ≤ C) (hkill : U ⊔ (C ⊓ H) ≤ LinearMap.ker f) :
    finrank F (C.map f) + finrank F (U ⊔ H : Submodule F V) ≤ finrank F V :=
  (restricted_rank_modular_bound C U H f hUC hkill).trans (Submodule.finrank_le _)

end SharedDecoders
