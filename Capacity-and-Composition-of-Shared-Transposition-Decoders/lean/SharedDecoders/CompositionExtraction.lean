import SharedDecoders.CompositionBand

/-! # One global error and an actual band of correct intermediate states -/

namespace SharedDecoders

open Module

variable {F V U : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup U] [Module F U]

/-- The kernels of `I-AB` and `I-BA` are canonically isomorphic, even when both
factors are singular. -/
def productKernelEquiv (A B : V →ₗ[F] V) :
    LinearMap.ker (LinearMap.id - A.comp B) ≃ₗ[F]
      LinearMap.ker (LinearMap.id - B.comp A) where
  toFun x := ⟨B x.val, by
    have hx : x.val = A (B x.val) := sub_eq_zero.mp x.property
    change B x.val - B (A (B x.val)) = 0
    rw [← hx, sub_self]⟩
  invFun y := ⟨A y.val, by
    have hy : y.val = B (A y.val) := sub_eq_zero.mp y.property
    change A y.val - A (B (A y.val)) = 0
    rw [← hy, sub_self]⟩
  left_inv x := by
    apply Subtype.ext
    exact (sub_eq_zero.mp x.property).symm
  right_inv y := by
    apply Subtype.ext
    exact (sub_eq_zero.mp y.property).symm
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem product_error_rank_eq [FiniteDimensional F V] (A B : V →ₗ[F] V) :
    finrank F (LinearMap.range (LinearMap.id - A.comp B)) =
      finrank F (LinearMap.range (LinearMap.id - B.comp A)) := by
  have h := (productKernelEquiv A B).finrank_eq
  have h₁ := (LinearMap.id - A.comp B).finrank_range_add_finrank_ker
  have h₂ := (LinearMap.id - B.comp A).finrank_range_add_finrank_ker
  omega

theorem band_correct_dimension [FiniteDimensional F V] [FiniteDimensional F U]
    (A B : V →ₗ[F] V) (E : U →ₗ[F] V) :
    finrank F U ≤ finrank F (LinearMap.ker ((LinearMap.id - A.comp B).comp E)) +
      finrank F (LinearMap.range (LinearMap.id - B.comp A)) := by
  have hr : finrank F (LinearMap.range ((LinearMap.id - A.comp B).comp E)) ≤
      finrank F (LinearMap.range (LinearMap.id - A.comp B)) := by
    apply Submodule.finrank_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨E x, rfl⟩
  rw [product_error_rank_eq A B] at hr
  have hn := ((LinearMap.id - A.comp B).comp E).finrank_range_add_finrank_ker
  omega

theorem band_correct_map_injective (A B : V →ₗ[F] V) (E : U →ₗ[F] V)
    (hE : Function.Injective E) :
    Function.Injective ((B.comp E).comp
      (LinearMap.ker ((LinearMap.id - A.comp B).comp E)).subtype) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  apply hE
  have he : E x.val = A (B (E x.val)) := sub_eq_zero.mp x.property
  change B (E x.val) = 0 at hx
  simpa [hx] using he

end SharedDecoders
