import TransposeFollowup.ComponentPartition
import TransposeFollowup.StrategySeparator

/-! Canonical graph-component form of the adaptive separator theorem. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def graphSeparatorLoss {n : ℕ} (b : ℕ) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  n * b * S.card + b * ∑ C ∈ graphComponents G S, C.card ^ 2

/-- All queries on the supplied transcript are included. A completed execution
has exactly this interaction graph regardless of later strategy behavior. -/
def PublicStrategy.interactionGraph {ι : Type*} {V : ι → Type*}
    (s : PublicStrategy ι V) (h m : List Bool) : SimpleGraph ι :=
  (s.truncate m.length h).interactionGraph m

theorem PublicStrategy.along_componentSet {ι : Type*} {V : ι → Type*} [Fintype ι]
    (s : PublicStrategy ι V) (x : (i : ι) → V i) {h m : List Bool}
    (hrun : s.Executes x h m) (S : Finset ι) :
    s.Along (PublicProtocol.Separated S (componentSet (s.interactionGraph h m) S)) h m := by
  apply s.along_of_truncate x _ hrun m.length le_rfl
  exact (s.truncate m.length h).along_componentSet m S

/-- Expected separator theorem using the actual graph components. The
separator may be any function of the helper and completed public transcript;
each finite query support contributes a clique. There are no additional
compatibility, support-size, entropy, or fiber assumptions. -/
theorem graph_expected_separator_bound_of_distribution {n b : ℕ} {H : Type*} [Fintype H]
    (F : Finset (FiniteMatrix n b))
    (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)
    (S : H → List Bool → Finset (Fin n)) :
    (∑ x : F, w x * ((M x.val).length : ℝ)) ≥
      (n * n * b : ℕ) -
      (∑ x : F, w x *
        (graphSeparatorLoss b ((strategy (helper x.val)).interactionGraph [] (M x.val))
          (S (helper x.val) (M x.val)) : ℝ)) -
      2 * ((n * n * b : ℕ) - entropy w / Real.log 2) -
      2 * (observationEntropy w (fun x : F => helper x.val) / Real.log 2) := by
  classical
  have h := strategy_expected_separator_bound_of_distribution F w hw hw1 helper strategy decode M hrun hcorrect S
    (fun z m => componentSet ((strategy z).interactionGraph [] m) (S z m))
    (fun x hx => (strategy (helper x)).along_componentSet x (hrun x hx) (S (helper x) (M x)))
  simp only [card_internalFreeBits_components] at h
  exact h

theorem graph_expected_separator_bound {n b : ℕ} {H : Type*} [Fintype H]
    (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)
    (S : H → List Bool → Finset (Fin n)) :
    (∑ x : F, uniformWeight F x * ((M x.val).length : ℝ)) ≥
      (n * n * b : ℕ) -
      (∑ x : F, uniformWeight F x *
        (graphSeparatorLoss b ((strategy (helper x.val)).interactionGraph [] (M x.val))
          (S (helper x.val) (M x.val)) : ℝ)) -
      2 * ((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) -
      2 * (observationEntropy (uniformWeight F) (fun x : F => helper x.val) / Real.log 2) := by
  simpa only [entropy_uniformWeight, Fintype.card_coe] using
    graph_expected_separator_bound_of_distribution F (uniformWeight F)
      (uniformWeight_nonneg F) (sum_uniformWeight F) helper strategy decode M hrun hcorrect S

open Classical in
/-- Worst-case graph-component form, with only attained helper values charged. -/
theorem graph_worst_case_separator_bound {n b : ℕ} {H : Type*} [Fintype H]
    (F : Finset (FiniteMatrix n b)) [Nonempty F]
    (helper : FiniteMatrix n b → H)
    (strategy : H → PublicStrategy (Fin n) (fun _ => Row n b))
    (decode : H → Fin n → Row n b → List Bool → Row n b)
    (M : FiniteMatrix n b → List Bool)
    (hrun : ∀ x ∈ F, (strategy (helper x)).Executes x [] (M x))
    (hcorrect : ∀ x ∈ F, ∀ j, decode (helper x) j (x j) (M x) = transposed x j)
    (S : H → List Bool → Finset (Fin n))
    (B L g : ℕ) (hB : ∀ x ∈ F, (M x).length ≤ B)
    (hL : ∀ x ∈ F, graphSeparatorLoss b ((strategy (helper x)).interactionGraph [] (M x))
      (S (helper x) (M x)) ≤ L)
    (hg : (F.image helper).card ≤ 2 ^ g) :
    (B : ℝ) ≥ (n * n * b : ℕ) - L -
      2 * (((n * n * b : ℕ) - Real.log (F.card : ℝ) / Real.log 2) + g) := by
  classical
  apply strategy_worst_case_separator_bound F helper strategy decode M hrun hcorrect S
    (fun z m => componentSet ((strategy z).interactionGraph [] m) (S z m))
    (fun x hx => (strategy (helper x)).along_componentSet x (hrun x hx) (S (helper x) (M x)))
    B L g hB _ hg
  intro x hx
  simpa only [graphSeparatorLoss, card_internalFreeBits_components] using hL x hx

end TransposeFollowup
