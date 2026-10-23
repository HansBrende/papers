import TransposeFollowup.ExpanderShearGraph
import TransposeFollowup.UnconditionalPaidPadding

/-! Existence of one fixed rational family with positive uniform expansion
for the exact simple incidence matrices of the generated shear pages. -/
namespace TransposeFollowup.ExpanderShear
open Classical MeasureTheory Set
set_option autoImplicit false

/-- Expansion is proved for the same rational coefficients used by the paid
page generator, uniformly at every positive half-dimension. -/
theorem exists_rational_shear_family :
    ∃ (r : ℕ) (F : Fin (r+1) → RationalMobius) (eta : ℝ),
      0 < eta ∧ eta ≤ 1 ∧
      ∀ m : ℕ, 0 < m → ∀ S : Finset (Row m), 2*S.card ≤ 2*m →
        eta*S.card ≤ (outsideNeighbors (coreGraph (rationalMatrix F)) S).card := by
  obtain ⟨r,F,eps,heps,hmap,hexp⟩ := exists_rational_continuous_expander
  refine ⟨r+1+r,rationalSymmetricFamily F,min 1 (eps/2),
    lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro m hm S hS
  exact (mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (eps/2))
    (Nat.cast_nonneg S.card)).trans
      (rationalSymmetric_core_expansion F hm hmap eps heps.le hexp S hS)

end TransposeFollowup.ExpanderShear
