import LeanMachine.RankCertificate

/-!
# The appendix rank identity

The general finite-dimensional result is supplied by `lean-machine`. The theorem
below is the exact ordinary-subtraction form of the manuscript's rank identity.
It covers arbitrary finite-dimensional vector spaces over arbitrary fields.
-/

namespace DirectedRecovery

open Module

/-- The appendix rank identity, with ranks embedded into the integers so that
the subtraction is the ordinary mathematical subtraction. -/
theorem rank_identity {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A L R : Module.End F V) :
    (finrank F (LinearMap.range (L - R)) : ℤ) -
      (finrank F (LinearMap.range (A * L - R * A)) : ℤ) ≤
        2 * (finrank F (LinearMap.range (1 - A)) : ℤ) :=
  LeanMachine.RankCertificate.rank_identity_int A L R

end DirectedRecovery
