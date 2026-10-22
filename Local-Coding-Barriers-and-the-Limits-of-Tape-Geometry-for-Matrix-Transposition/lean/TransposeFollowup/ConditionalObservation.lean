import TransposeFollowup.EntropyObservation
import TransposeFollowup.SubmodularCover

/-! Conditional entropy for finite deterministic observations. All quantities
use natural logarithms and the existing finite-weight entropy definitions. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def conditionalObservationEntropy {Ω A C : Type*}
    [Fintype Ω] [Fintype A] [Fintype C]
    (p : Ω → ℝ) (f : Ω → A) (w : Ω → C) : ℝ :=
  observationEntropy p (fun x => (w x, f x)) - observationEntropy p w

theorem observationEntropy_pair_swap {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (g : Ω → B) :
    observationEntropy p (fun x => (f x, g x)) =
      observationEntropy p (fun x => (g x, f x)) := by
  apply observationEntropy_eq_of_same_fibers p hp
  intro x y
  simp only [Prod.mk.injEq, and_comm]

theorem conditionalObservationEntropy_nonneg {Ω A C : Type*}
    [Fintype Ω] [Fintype A] [Fintype C] [Nonempty A] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (w : Ω → C) :
    0 ≤ conditionalObservationEntropy p f w := by
  apply sub_nonneg.mpr
  exact observationEntropy_le_of_factorsThrough p hp _ w
    (fun _ _ h => congrArg Prod.fst h)

theorem conditionalObservationEntropy_eq_zero {Ω A C : Type*}
    [Fintype Ω] [Fintype A] [Fintype C] [Nonempty A] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (w : Ω → C)
    (h : f.FactorsThrough w) : conditionalObservationEntropy p f w = 0 := by
  have heq : observationEntropy p (fun x => (w x, f x)) = observationEntropy p w := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    exact ⟨fun he => congrArg Prod.fst he, fun he => Prod.ext he (h he)⟩
  simp only [conditionalObservationEntropy, heq, sub_self]

theorem conditionalObservationEntropy_le_of_factorsThrough {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (g : Ω → B) (w : Ω → C)
    (h : f.FactorsThrough (fun x => (w x, g x))) :
    conditionalObservationEntropy p f w ≤ conditionalObservationEntropy p g w := by
  apply sub_le_sub_right
  apply observationEntropy_le_of_factorsThrough p hp
    (fun x => (w x, g x)) (fun x => (w x, f x))
  intro x y he
  exact Prod.ext (congrArg (fun z : C × B => z.1) he) (h he)

theorem conditionalObservationEntropy_eq_of_same_fibers {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (g : Ω → B) (w : Ω → C)
    (h : ∀ x y, w x = w y → (f x = f y ↔ g x = g y)) :
    conditionalObservationEntropy p f w = conditionalObservationEntropy p g w := by
  apply le_antisymm
  · apply conditionalObservationEntropy_le_of_factorsThrough p hp
    intro x y he
    exact (h x y (congrArg Prod.fst he)).mpr (congrArg Prod.snd he)
  · apply conditionalObservationEntropy_le_of_factorsThrough p hp
    intro x y he
    exact (h x y (congrArg Prod.fst he)).mp (congrArg Prod.snd he)

theorem conditionalObservationEntropy_condition_le {Ω A C D : Type*}
    [Fintype Ω] [Fintype A] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty C] [Nonempty D]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (w : Ω → C) (v : Ω → D) (h : w.FactorsThrough v) :
    conditionalObservationEntropy p f v ≤ conditionalObservationEntropy p f w := by
  have hs := observationEntropy_strong_subadditive p hp f v w
  have hwfv : w.FactorsThrough (fun x => (f x, v x)) :=
    fun _ _ he => h (congrArg Prod.snd he)
  rw [observationEntropy_pair_of_factorsThrough p hp _ w hwfv,
    observationEntropy_pair_of_factorsThrough p hp v w h,
    observationEntropy_pair_swap p hp f v] at hs
  dsimp only [conditionalObservationEntropy]
  linarith

theorem conditionalObservationEntropy_pair {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (g : Ω → B) (w : Ω → C) :
    conditionalObservationEntropy p (fun x => (f x, g x)) w =
      conditionalObservationEntropy p f w +
      conditionalObservationEntropy p g (fun x => (w x, f x)) := by
  have heq : observationEntropy p (fun x => (w x, (f x, g x))) =
      observationEntropy p (fun x => ((w x, f x), g x)) := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    simp only [Prod.mk.injEq, and_assoc]
  dsimp only [conditionalObservationEntropy]
  rw [heq]
  ring

theorem conditionalObservationEntropy_subadditive {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (g : Ω → B) (w : Ω → C) :
    conditionalObservationEntropy p (fun x => (f x, g x)) w ≤
      conditionalObservationEntropy p f w + conditionalObservationEntropy p g w := by
  have hs := observationEntropy_strong_subadditive p hp f g w
  dsimp only [conditionalObservationEntropy]
  linarith


noncomputable def finiteView {ι α : Type*} [DecidableEq ι] [Nonempty α]
    (S : Finset ι) (x : ι → α) : ι → α :=
  fun i => if i ∈ S then x i else Classical.choice ‹Nonempty α›

theorem finiteView_eq_iff {ι α : Type*} [DecidableEq ι] [Nonempty α]
    (S : Finset ι) (x y : ι → α) :
    finiteView S x = finiteView S y ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    simpa only [finiteView, hi, ite_true] using congrFun h i
  · intro h
    funext i
    by_cases hi : i ∈ S <;> simp [finiteView, hi, h]

theorem conditionalObservationEntropy_pi_le_sum {Ω ι α C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype C]
    [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (A : Ω → ι → α) (w : Ω → C) :
    conditionalObservationEntropy p A w ≤
      ∑ i, conditionalObservationEntropy p (fun x => A x i) w := by
  classical
  have hS : ∀ S : Finset ι,
      conditionalObservationEntropy p (fun x => finiteView S (A x)) w ≤
        ∑ i ∈ S, conditionalObservationEntropy p (fun x => A x i) w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      apply le_of_eq
      apply conditionalObservationEntropy_eq_zero p hp
      intro x y _
      funext i
      simp [finiteView]
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      have hfac : (fun x => finiteView (insert i S) (A x)).FactorsThrough
          (fun x => (w x, (A x i, finiteView S (A x)))) := by
        intro x y he
        apply (finiteView_eq_iff _ _ _).mpr
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          exact congrArg (fun z : C × (α × (ι → α)) => z.2.1) he
        · have hs := congrArg (fun z : C × (α × (ι → α)) => z.2.2) he
          exact (finiteView_eq_iff _ _ _).mp hs j hj
      exact (conditionalObservationEntropy_le_of_factorsThrough p hp _ _ w hfac).trans
        ((conditionalObservationEntropy_subadditive p hp _ _ w).trans
          (add_le_add le_rfl ih))
  have h := hS Finset.univ
  have heq : (fun x => finiteView Finset.univ (A x)) = A := by
    funext x i
    simp [finiteView]
  simpa only [heq] using h

theorem conditionalObservationEntropy_condition_eq_of_same_fibers {Ω A C D : Type*}
    [Fintype Ω] [Fintype A] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty C] [Nonempty D]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (w : Ω → C) (v : Ω → D)
    (h : ∀ x y, w x = w y ↔ v x = v y) :
    conditionalObservationEntropy p f w = conditionalObservationEntropy p f v := by
  apply le_antisymm
  · exact conditionalObservationEntropy_condition_le p hp f v w
      (fun x y he => (h x y).mp he)
  · exact conditionalObservationEntropy_condition_le p hp f w v
      (fun x y he => (h x y).mpr he)


theorem conditionalObservationEntropy_chain_of_factorsThrough {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (g : Ω → B) (w : Ω → C)
    (h : g.FactorsThrough (fun x => (w x, f x))) :
    conditionalObservationEntropy p f w =
      conditionalObservationEntropy p g w +
      conditionalObservationEntropy p f (fun x => (w x, g x)) := by
  have heq : conditionalObservationEntropy p (fun x => (g x, f x)) w =
      conditionalObservationEntropy p f w := by
    apply conditionalObservationEntropy_eq_of_same_fibers p hp
    intro x y hw
    constructor
    · exact fun he => congrArg Prod.snd he
    · exact fun he => Prod.ext (h (Prod.ext hw he)) he
  rw [← heq]
  exact conditionalObservationEntropy_pair p hp g f w

end TransposeFollowup
