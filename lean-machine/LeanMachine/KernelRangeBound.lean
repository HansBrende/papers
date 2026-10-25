import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A rank-nullity interface for a code in a kernel and locally generated
vectors in the range. Graph locality is a separate hypothesis to supply. -/

namespace LeanMachine

open Module

variable {K W : Type*} [DivisionRing K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem finrank_add_le_of_ker_range (H : W →ₗ[K] W) (C L : Submodule K W)
    (hC : C ≤ LinearMap.ker H) (hL : L ≤ LinearMap.range H) :
    finrank K C + finrank K L ≤ finrank K W := by
  have h₁ := Submodule.finrank_mono hC
  have h₂ := Submodule.finrank_mono hL
  have h₃ := H.finrank_range_add_finrank_ker
  omega

/-- The part of `C` outside `L` has at least twice the code dimension minus
the ambient dimension. The subtraction-free form also handles negative deficits. -/
theorem twice_finrank_le_quotient_add_of_ker_range
    (H : W →ₗ[K] W) (C L : Submodule K W) (hLC : L ≤ C)
    (hC : C ≤ LinearMap.ker H) (hL : L ≤ LinearMap.range H) :
    2 * finrank K C ≤ finrank K (C ⧸ L.comap C.subtype) + finrank K W := by
  have hd := finrank_add_le_of_ker_range H C L hC hL
  have hq := (L.comap C.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hLC).finrank_eq] at hq
  omega

/-- A general split-generator criterion. Graph-locality arguments can supply
the split `x = s + A s`; no claim that `s` is itself a codeword is needed. -/
theorem finrank_add_span_le_of_split_generators
    (A : W →ₗ[K] W) (C : Submodule K W) (S : Set W)
    (hC : C ≤ LinearMap.ker (LinearMap.id + A))
    (hS : ∀ x ∈ S, ∃ s, x = s + A s) :
    finrank K C + finrank K (Submodule.span K S) ≤ finrank K W := by
  apply finrank_add_le_of_ker_range (LinearMap.id + A) C
  · exact hC
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨s, hs⟩ := hS x hx
    exact ⟨s, hs.symm⟩

end LeanMachine
