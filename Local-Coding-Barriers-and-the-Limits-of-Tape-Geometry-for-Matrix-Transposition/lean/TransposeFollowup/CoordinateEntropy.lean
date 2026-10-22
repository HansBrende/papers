import TransposeFollowup.EntropyObservation
import TransposeFollowup.SubmodularCover

/-! Coordinate entropy and the two-cover inequality. The sample law may be
arbitrarily correlated; only nonnegativity and total mass one are required. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

def bitView {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → Bool) : ι → Bool :=
  fun i => if i ∈ S then x i else false

theorem bitView_eq_iff {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x y : ι → Bool) :
    bitView S x = bitView S y ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    simpa only [bitView, hi, ite_true] using congrFun h i
  · intro h
    funext i
    by_cases hi : i ∈ S <;> simp [bitView, hi, h]

theorem bitView_factorsThrough {Ω ι : Type*} [DecidableEq ι]
    (X : Ω → ι → Bool) {S T : Finset ι} (hST : S ⊆ T) :
    (fun x => bitView S (X x)).FactorsThrough (fun x => bitView T (X x)) := by
  intro x y hxy
  apply (bitView_eq_iff S _ _).mpr
  intro i hi
  exact (bitView_eq_iff T _ _).mp hxy i (hST hi)

noncomputable def coordinateEntropy {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (X : Ω → ι → Bool) (S : Finset ι) : ℝ :=
  observationEntropy p (fun x => bitView S (X x))

theorem coordinateEntropy_empty {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp1 : ∑ x, p x = 1) (X : Ω → ι → Bool) :
    coordinateEntropy p X ∅ = 0 := by
  have heq : (fun x => bitView (∅ : Finset ι) (X x)) = fun _ _ => false := by
    funext x i
    simp [bitView]
  rw [coordinateEntropy, heq, observationEntropy_const, hp1, Real.negMulLog_one]

theorem coordinateEntropy_univ {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (X : Ω → ι → Bool) :
    coordinateEntropy p X Finset.univ = observationEntropy p X := by
  have heq : (fun x => bitView Finset.univ (X x)) = X := by
    funext x i
    simp [bitView]
  rw [coordinateEntropy, heq]

theorem coordinateEntropy_mono {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) :
    Monotone (coordinateEntropy p X) := by
  intro S T hST
  exact observationEntropy_le_of_factorsThrough p hp _ _ (bitView_factorsThrough X hST)

theorem coordinateEntropy_union {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (S T : Finset ι) :
    observationEntropy p (fun x => (bitView S (X x), bitView T (X x))) =
      coordinateEntropy p X (S ∪ T) := by
  apply observationEntropy_eq_of_same_fibers p hp
  intro x y
  simp only [Prod.mk.injEq, bitView_eq_iff, Finset.mem_union]
  constructor
  · rintro ⟨hS, hT⟩ i (hi | hi)
    · exact hS i hi
    · exact hT i hi
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩

theorem coordinateEntropy_submodular {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (S T : Finset ι) :
    coordinateEntropy p X (S ∪ T) + coordinateEntropy p X (S ∩ T) ≤
      coordinateEntropy p X S + coordinateEntropy p X T := by
  let a := fun x => bitView S (X x)
  let b := fun x => bitView T (X x)
  let c := fun x => bitView (S ∩ T) (X x)
  have hca : c.FactorsThrough a := bitView_factorsThrough X Finset.inter_subset_left
  have hcb : c.FactorsThrough b := bitView_factorsThrough X Finset.inter_subset_right
  have hcab : c.FactorsThrough (fun x => (a x, b x)) :=
    fun _ _ h => hca (congrArg Prod.fst h)
  have h := observationEntropy_strong_subadditive p hp a b c
  rw [observationEntropy_pair_of_factorsThrough p hp _ c hcab,
    observationEntropy_pair_of_factorsThrough p hp a c hca,
    observationEntropy_pair_of_factorsThrough p hp b c hcb] at h
  rw [coordinateEntropy_union p hp X S T] at h
  exact h

/-- Every bit included at least `k` times gives the usual Shearer lower
bound, even when the bits are correlated by the correct-input restriction. -/
theorem coordinateEntropy_cover {Ω ι κ : Type*}
    [Fintype Ω] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (S : κ → Finset ι) (k : ℝ)
    (hcover : ∀ i, k ≤ ∑ a, if i ∈ S a then (1 : ℝ) else 0) :
    k * observationEntropy p X ≤ ∑ a, coordinateEntropy p X (S a) := by
  have h := submodular_cover Finset.univ (coordinateEntropy p X)
    (coordinateEntropy_empty p hp1 X) (coordinateEntropy_mono p hp X)
    (coordinateEntropy_submodular p hp X) S (fun _ => Finset.subset_univ _)
    k (fun i _ => hcover i)
  rwa [coordinateEntropy_univ] at h

theorem coordinateEntropy_le_card {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (S : Finset ι) :
    coordinateEntropy p X S ≤ (S.card : ℝ) * Real.log 2 := by
  let f := fun x (i : S) => X x i
  have heq : coordinateEntropy p X S = observationEntropy p f := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    rw [bitView_eq_iff]
    constructor
    · intro h
      funext i
      exact h i i.property
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
  rw [heq]
  have h := entropy_le_log_card (pushforward p f) (pushforward_nonneg p hp f)
    (by rw [sum_pushforward, hp1])
  simpa only [observationEntropy, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

/-- Coordinates fixed throughout the sample family contribute no entropy,
even if they belong to the queried set. -/
theorem coordinateEntropy_remove_fixed {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (X : Ω → ι → Bool) (S F : Finset ι)
    (hfixed : ∀ x y i, i ∈ F → X x i = X y i) :
    coordinateEntropy p X S = coordinateEntropy p X (S \ F) := by
  apply le_antisymm
  · apply observationEntropy_le_of_factorsThrough p hp
    intro x y hxy
    apply (bitView_eq_iff _ _ _).mpr
    intro i hi
    by_cases hif : i ∈ F
    · exact hfixed x y i hif
    · exact (bitView_eq_iff _ _ _).mp hxy i (Finset.mem_sdiff.mpr ⟨hi, hif⟩)
  · exact coordinateEntropy_mono p hp X Finset.sdiff_subset

end TransposeFollowup
