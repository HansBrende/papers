import TransposeFollowup.ConditionalObservation
import TransposeFollowup.CoordinateEntropy
import TransposeFollowup.WeightedSubmodularCover

/-! Conditional coordinate entropy, including finite covering inequalities. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def conditionalCoordinateEntropy {Ω ι C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype C]
    (p : Ω → ℝ) (X : Ω → ι → Bool) (w : Ω → C) (S : Finset ι) : ℝ :=
  conditionalObservationEntropy p (fun x => bitView S (X x)) w

theorem conditionalCoordinateEntropy_empty {Ω ι C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (w : Ω → C) :
    conditionalCoordinateEntropy p X w ∅ = 0 := by
  apply conditionalObservationEntropy_eq_zero p hp
  intro x y _
  funext i
  simp [bitView]

theorem conditionalCoordinateEntropy_univ {Ω ι C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype C]
    (p : Ω → ℝ) (X : Ω → ι → Bool) (w : Ω → C) :
    conditionalCoordinateEntropy p X w Finset.univ = conditionalObservationEntropy p X w := by
  have heq : (fun x => bitView Finset.univ (X x)) = X := by
    funext x i
    simp [bitView]
  simp only [conditionalCoordinateEntropy, heq]

theorem conditionalCoordinateEntropy_mono {Ω ι C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (w : Ω → C) :
    Monotone (conditionalCoordinateEntropy p X w) := by
  intro S T hST
  apply conditionalObservationEntropy_le_of_factorsThrough p hp
  intro x y hxy
  exact bitView_factorsThrough X hST (congrArg (fun z : C × (ι → Bool) => z.2) hxy)

theorem conditionalCoordinateEntropy_submodular {Ω ι C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (w : Ω → C)
    (S T : Finset ι) :
    conditionalCoordinateEntropy p X w (S ∪ T) +
        conditionalCoordinateEntropy p X w (S ∩ T) ≤
      conditionalCoordinateEntropy p X w S + conditionalCoordinateEntropy p X w T := by
  let a := fun x => (w x, bitView S (X x))
  let b := fun x => (w x, bitView T (X x))
  let c := fun x => (w x, bitView (S ∩ T) (X x))
  have hca : c.FactorsThrough a := by
    intro x y hxy
    have hw := congrArg (fun z : C × (ι → Bool) => z.1) hxy
    have hb := congrArg (fun z : C × (ι → Bool) => z.2) hxy
    exact Prod.ext hw (bitView_factorsThrough X Finset.inter_subset_left hb)
  have hcb : c.FactorsThrough b := by
    intro x y hxy
    have hw := congrArg (fun z : C × (ι → Bool) => z.1) hxy
    have hb := congrArg (fun z : C × (ι → Bool) => z.2) hxy
    exact Prod.ext hw (bitView_factorsThrough X Finset.inter_subset_right hb)
  have hcab : c.FactorsThrough (fun x => (a x, b x)) :=
    fun _ _ h => hca (congrArg Prod.fst h)
  have hs := observationEntropy_strong_subadditive p hp a b c
  rw [observationEntropy_pair_of_factorsThrough p hp _ c hcab,
    observationEntropy_pair_of_factorsThrough p hp a c hca,
    observationEntropy_pair_of_factorsThrough p hp b c hcb] at hs
  have heq : observationEntropy p (fun x => (a x, b x)) =
      observationEntropy p (fun x => (w x, bitView (S ∪ T) (X x))) := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    simp only [a, b, Prod.mk.injEq, bitView_eq_iff, Finset.mem_union]
    constructor
    · rintro ⟨⟨hw, hS⟩, ⟨_, hT⟩⟩
      exact ⟨hw, fun i hi => hi.elim (hS i) (hT i)⟩
    · rintro ⟨hw, hU⟩
      exact ⟨⟨hw, fun i hi => hU i (Or.inl hi)⟩,
        ⟨hw, fun i hi => hU i (Or.inr hi)⟩⟩
  rw [heq] at hs
  dsimp only [a, b, c] at hs
  dsimp only [conditionalCoordinateEntropy, conditionalObservationEntropy]
  linarith

theorem conditionalCoordinateEntropy_weighted_cover {Ω ι κ C : Type*}
    [Fintype Ω] [Fintype ι] [Fintype κ] [DecidableEq ι]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (w : Ω → C)
    (S : κ → Finset ι) (weight : κ → ℝ) (hw : ∀ a, 0 ≤ weight a) (k : ℝ)
    (hcover : ∀ i, k ≤ ∑ a, if i ∈ S a then weight a else 0) :
    k * conditionalObservationEntropy p X w ≤
      ∑ a, weight a * conditionalCoordinateEntropy p X w (S a) := by
  have h := weighted_submodular_cover Finset.univ (conditionalCoordinateEntropy p X w)
    (conditionalCoordinateEntropy_empty p hp X w)
    (conditionalCoordinateEntropy_mono p hp X w)
    (conditionalCoordinateEntropy_submodular p hp X w) S (fun _ => Finset.subset_univ _)
    weight hw k (fun i _ => hcover i)
  rwa [conditionalCoordinateEntropy_univ] at h

theorem conditionalCoordinateEntropy_cover {Ω ι κ C : Type*}
    [Fintype Ω] [Fintype ι] [Fintype κ] [DecidableEq ι]
    [Fintype C] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (w : Ω → C)
    (S : κ → Finset ι) (k : ℝ)
    (hcover : ∀ i, k ≤ ∑ a, if i ∈ S a then (1 : ℝ) else 0) :
    k * conditionalObservationEntropy p X w ≤
      ∑ a, conditionalCoordinateEntropy p X w (S a) := by
  simpa only [one_mul] using
    conditionalCoordinateEntropy_weighted_cover p hp X w S
      (fun _ => 1) (fun _ => zero_le_one) k hcover

end TransposeFollowup
