import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing

/-!
# A rank certificate from an intertwining defect

The elementary identity `L - R = (A * L - R * A) + (1 - A) * L - R * (1 - A)`
bounds the rank of `L - R` by the intertwining defect and twice the rank of `1 - A`.
All ranks below are dimensions of ranges. No commutativity or invertibility of the
endomorphisms is assumed.
-/

open Module

namespace LeanMachine.RankCertificate

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private theorem finrank_range_add_le (f g : Module.End F V) :
    finrank F (LinearMap.range (f + g)) ≤
      finrank F (LinearMap.range f) + finrank F (LinearMap.range g) := by
  exact (Submodule.finrank_mono (LinearMap.range_add_le f g)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem finrank_range_sub_le (f g : Module.End F V) :
    finrank F (LinearMap.range (f - g)) ≤
      finrank F (LinearMap.range f) + finrank F (LinearMap.range g) := by
  have h := finrank_range_add_le f (-g)
  have hneg : LinearMap.range (-g) = LinearMap.range g := LinearMap.range_neg g
  rw [hneg] at h
  rw [show f - g = f + -g from sub_eq_add_neg f g]
  exact h

private theorem finrank_range_mul_le_left (f g : Module.End F V) :
    finrank F (LinearMap.range (f * g)) ≤ finrank F (LinearMap.range f) := by
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left g f)
    (Module.rank_lt_aleph0 F _)

private theorem finrank_range_mul_le_right (f g : Module.End F V) :
    finrank F (LinearMap.range (f * g)) ≤ finrank F (LinearMap.range g) := by
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_right g f)
    (Module.rank_lt_aleph0 F _)

/-- The rank of a difference is controlled by the intertwining defect and twice
the rank of the identity minus `A`. This additive form avoids truncated subtraction. -/
theorem rank_identity (A L R : Module.End F V) :
    finrank F (LinearMap.range (L - R)) ≤
      finrank F (LinearMap.range (A * L - R * A)) +
        2 * finrank F (LinearMap.range (1 - A)) := by
  have hid : L - R = (A * L - R * A) + (1 - A) * L - R * (1 - A) := by
    noncomm_ring
  have h₁ := finrank_range_sub_le ((A * L - R * A) + (1 - A) * L) (R * (1 - A))
  rw [← hid] at h₁
  have h₂ := finrank_range_add_le (A * L - R * A) ((1 - A) * L)
  have h₃ := finrank_range_mul_le_left (1 - A) L
  have h₄ := finrank_range_mul_le_right R (1 - A)
  omega

/-- The rank certificate with ordinary integer subtraction, equivalent to
`rank_identity` and to the usual displayed rank inequality. -/
theorem rank_identity_int (A L R : Module.End F V) :
    (finrank F (LinearMap.range (L - R)) : ℤ) -
      (finrank F (LinearMap.range (A * L - R * A)) : ℤ) ≤
        2 * (finrank F (LinearMap.range (1 - A)) : ℤ) := by
  have h := rank_identity A L R
  omega

end LeanMachine.RankCertificate
