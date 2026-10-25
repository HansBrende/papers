import LeanMachine.KernelRangeBound

/-! Public interface to the shared dimension lemma. The manuscript separately
proves that graph-local codewords supply its range-containment hypothesis. -/

namespace CoverStorage

open Module

theorem kernel_range_dimension_bound {K W : Type*} [DivisionRing K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (H : W →ₗ[K] W) (C L : Submodule K W)
    (hC : C ≤ LinearMap.ker H) (hL : L ≤ LinearMap.range H) :
    finrank K C + finrank K L ≤ finrank K W :=
  LeanMachine.finrank_add_le_of_ker_range H C L hC hL

/-- Deficit bound for the quotient by the local span. -/
theorem quotient_dimension_bound {K W : Type*} [DivisionRing K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (H : W →ₗ[K] W) (C L : Submodule K W) (hLC : L ≤ C)
    (hC : C ≤ LinearMap.ker H) (hL : L ≤ LinearMap.range H) :
    2 * finrank K C ≤ finrank K (C ⧸ L.comap C.subtype) + finrank K W :=
  LeanMachine.twice_finrank_le_quotient_add_of_ker_range H C L hLC hC hL

/-- Algebraic endpoint of the graph parity-split argument. -/
theorem split_generator_dimension_bound {K W : Type*} [DivisionRing K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : W →ₗ[K] W) (C : Submodule K W) (S : Set W)
    (hC : C ≤ LinearMap.ker (LinearMap.id + A))
    (hS : ∀ x ∈ S, ∃ s, x = s + A s) :
    finrank K C + finrank K (Submodule.span K S) ≤ finrank K W :=
  LeanMachine.finrank_add_span_le_of_split_generators A C S hC hS

end CoverStorage
