import TransposeFollowup.RationalWordArithmetic
import Mathlib.GroupTheory.Commutator.Basic

/-! Exact denominator propagation and an original-coordinate lower bound
for a nontrivial rational bicommutator. No change of basis is involved. -/
namespace TransposeFollowup.RationalFreePair
open Classical
open scoped commutatorElement
set_option autoImplicit false

theorem denominatorCarrier_commutator {D : ℕ} {a x : RealMobius.Group}
    (ha : a ∈ denominatorCarrier D) (hx : x ∈ denominatorCarrier D) :
    ⁅a, x⁆ ∈ denominatorCarrier (D ^ 4) := by
  have h := denominatorCarrier_mul
    (denominatorCarrier_mul (denominatorCarrier_mul ha hx) (denominatorCarrier_inv ha))
    (denominatorCarrier_inv hx)
  simpa only [commutatorElement_def, show D * D * D * D = D ^ 4 by ring] using h

theorem rational_bicommutator_separated {D : ℕ} (hD : 0 < D)
    {a x y : RealMobius.Group} (ha : a ∈ denominatorCarrier D)
    (hx : x ∈ denominatorCarrier D) (hy : y ∈ denominatorCarrier D)
    (hne : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ≠ 1) :
    ⁅⁅a, x⁆, ⁅a, y⁆⁆ ∈ denominatorCarrier (D ^ 16) ∧
      ∃ i j : Fin 2, 1 / (D : ℝ) ^ 16 ≤
        |⁅⁅a, x⁆, ⁅a, y⁆⁆ i j - (1 : RealMobius.Group) i j| := by
  have hc : ⁅⁅a, x⁆, ⁅a, y⁆⁆ ∈ denominatorCarrier (D ^ 16) := by
    have h := denominatorCarrier_commutator
      (denominatorCarrier_commutator ha hx) (denominatorCarrier_commutator ha hy)
    simpa only [← pow_mul, show 4 * 4 = 16 from rfl] using h
  refine ⟨hc, ?_⟩
  simpa only [Nat.cast_pow] using denominatorCarrier_separated (pow_pos hD 16) hc
    (denominatorCarrier_one (D ^ 16)) hne

end TransposeFollowup.RationalFreePair
