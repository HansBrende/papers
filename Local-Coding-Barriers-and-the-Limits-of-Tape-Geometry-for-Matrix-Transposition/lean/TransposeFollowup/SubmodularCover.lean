import TransposeFollowup.WeightedSubmodularCover

/-! The finite covering inequality needed for the coordinate two-cover proof.
Its hypotheses will be proved for entropy, rather than assumed by a coding
theorem. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

/-- Shearer's covering inequality for a normalized monotone submodular
function. The lower bound on covering multiplicity can be any real. -/
theorem submodular_cover {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (U : Finset ι) (f : Finset ι → ℝ)
    (hzero : f ∅ = 0)
    (hmono : Monotone f)
    (hsub : ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B)
    (S : κ → Finset ι) (hS : ∀ a, S a ⊆ U)
    (k : ℝ)
    (hcover : ∀ i ∈ U, k ≤ ∑ a, if i ∈ S a then (1 : ℝ) else 0) :
    k * f U ≤ ∑ a, f (S a) := by
  simpa only [one_mul] using
    weighted_submodular_cover U f hzero hmono hsub S hS
      (fun _ => 1) (fun _ => zero_le_one) k hcover

end TransposeFollowup
