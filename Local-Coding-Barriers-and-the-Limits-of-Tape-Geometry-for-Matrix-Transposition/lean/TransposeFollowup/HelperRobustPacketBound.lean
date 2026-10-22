import TransposeFollowup.HelperPacketAveraging
import TransposeFollowup.RobustPacketBound

/-! Robust bounds for actual helper-selected packet codes. Conditional
single-code bounds are derived from the selected banks and decoders; they
are not hypotheses of the final theorem. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

namespace HelperInverseLocalPacketCode

variable {d b : ℕ} {H Ω : Type*} [Fintype H] [Fintype Ω]
    (C : HelperInverseLocalPacketCode d b H)

omit [Fintype H] [Fintype Ω] in
/-- Restricting a correct helper-selected code to one sample fiber gives a
correct fixed code on precisely that fiber's raw matrix range. -/
theorem correctOn_fiber (X : Ω → FiniteMatrix d b)
    (hc : C.CorrectOn (Set.range X)) (a : H) :
    (C.branch a).CorrectOn
      (Set.range (fun x : HelperFiber (fun z => C.helper (X z)) a => X x)) := by
  intro x hx j
  obtain ⟨z, rfl⟩ := hx
  exact hc a (X z) ⟨⟨z.val, rfl⟩, z.property⟩ j

/-- Expected packet and inverse-near budgets under an arbitrary normalized
finite input law. A deterministic helper may select every part of the code.
Only its selected branch must decode each input, using the original row. -/
theorem robust_broadcast_bound
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (G : H → SimpleGraph (Fin d)) (ell K : ℕ) (hell : 0 < ell)
    (hlocal : ∀ a, (C.branch a).LocalTo (G a))
    (hdegree : ∀ a i,
      (inverseSupportGraph (C.branch a).bank.support (G a) ell).degree i ≤ K) :
    ((ell : ℝ) + 1) * ((d*d*b : ℕ) -
        ∑ x, p x * (C.length (C.helper (X x)) : ℝ)) ≤
      (d*d*b : ℕ) + (ell : ℝ) * (∑ x, p x *
        ((inverseNearBits (b := b) (C.branch (C.helper (X x))).bank.support
          (G (C.helper (X x))) ell).card : ℝ)) +
      (ell : ℝ) * (1 + min (d : ℝ) (16 * ((K : ℝ) + 1)^2)) *
        ((d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
          observationEntropy p (fun x => C.helper (X x)) / Real.log 2) := by
  apply helper_packet_bound_of_fiber_bounds p hp hp1 X
    (fun x => C.helper (X x)) (fun _ _ h => congrArg C.helper h)
    C.length (fun a => (inverseNearBits (b := b)
      (C.branch a).bank.support (G a) ell).card) ell
    (1 + min (d : ℝ) (16 * ((K : ℝ) + 1)^2))
  intro a ha
  exact (C.branch a).broadcast_lower_bound_of_distribution
    (helperConditionalWeight p (fun x => C.helper (X x)) a)
    (helperConditionalWeight_nonneg p hp _ a)
    (sum_helperConditionalWeight p _ a (ne_of_gt ha))
    (fun x : HelperFiber (fun z => C.helper (X z)) a => X x)
    (C.correctOn_fiber X hc a) (G a) (hlocal a) ell K hell (hdegree a)

end HelperInverseLocalPacketCode
end TransposeFollowup
