import TransposeFollowup.AdaptiveBankStrategy
import TransposeFollowup.AdaptiveForestHelperBound

/-! The forest bound for public strategies that need terminate only on the
correct input family. Truncation preserves every actual support occurrence. -/

namespace TransposeFollowup.HelperGapBankStrategy

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b sigma : ℕ} {H Ω : Type*} [Fintype H] [Fintype Ω]
    (C : HelperGapBankStrategy d b sigma H)

theorem forest_expected_length
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (message : FiniteMatrix d b → List Bool)
    (ht : C.TerminatesOn (Set.range X) message) (hc : C.CorrectOn (Set.range X) message)
    (R M D : ℕ) (hR : 0 < R) (hM : 0 < M) (hd : 0 < d) (hD : 2 ≤ D)
    (hforest : ∀ x, ((C.strategy (C.helper (X x))).bankInteractionGraph [] (message (X x))).IsAcyclic)
    (hpair : ∀ x, (C.strategy (C.helper (X x))).Along (fun S => S.card ≤ 2) [] (message (X x)))
    (G : H → List Bool → SimpleGraph (Fin d))
    (hlocal : ∀ x, ∀ v w : MatrixBit d b,
      ((C.strategy (C.helper (X x))).bankInteractionGraph [] (message (X x))).Adj v w →
        v.1 = w.1 ∨ (G (C.helper (X x)) (message (X x))).Adj v.1 w.1)
    (hdegree : ∀ x i, (G (C.helper (X x)) (message (X x))).degree i ≤ D)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : ∀ a, (C.bank a).StateBudget s) :
    (d*d*b : ℕ) -
      ((d*b*D^(2*R)*(d ⌈/⌉ M + 2*sigma) : ℕ) +
        ((D^R+1)*bucketPatternCount M (D^R) : ℕ)*s) -
      (bucketPatternCount M (D^R) : ℝ) *
        ((d*d*b : ℕ) - observationEntropy p X / Real.log 2 +
          observationEntropy p (fun x => C.helper (X x)) / Real.log 2) ≤
      (1 + 1 / (R : ℝ)) * ∑ x, p x * ((message (X x)).length : ℝ) := by
  let F : Finset (FiniteMatrix d b) := Finset.univ.image X
  have hF : (F : Set (FiniteMatrix d b)) = Set.range X := by
    ext x
    simp [F]
  have hx (x : Ω) : X x ∈ F := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have htF : C.TerminatesOn F message := by rwa [hF]
  have hcF : C.CorrectOn F message := by rwa [hF]
  let E := C.compile F message
  have hEc : E.CorrectOn (Set.range X) := by
    rw [← hF]
    exact C.compile_correct F message htF hcF
  have hmsg (x : Ω) : (E.branch (E.helper (X x))).transcript (X x) = message (X x) :=
    C.compile_transcript F message htF (X x) (hx x)
  have hgraph (x : Ω) : (E.branch (E.helper (X x))).protocol.interactionGraph
      ((E.branch (E.helper (X x))).transcript (X x)) =
      (C.strategy (C.helper (X x))).bankInteractionGraph [] (message (X x)) :=
    C.compile_graph F message htF (X x) (hx x)
  have hb := E.forest_expected_length p hp hp1 X hEc R M D hR hM hd hD
    (fun x => (hgraph x) ▸ hforest x)
    (fun x => C.compile_along F message htF (X x) (hx x) _ (hpair x)) G
    (fun x => by
      intro v w hvw
      rw [hgraph x] at hvw
      rw [hmsg x]
      change v.1 = w.1 ∨ (G (C.helper (X x)) (message (X x))).Adj v.1 w.1
      exact hlocal x v w hvw)
    (fun x i => by
      rw [hmsg x]
      exact hdegree x i) hs0 hs
  have hlen (x : Ω) : E.length (X x) = (message (X x)).length :=
    congrArg List.length (hmsg x)
  simpa only [hlen, show E.helper = C.helper from rfl] using hb

end TransposeFollowup.HelperGapBankStrategy
