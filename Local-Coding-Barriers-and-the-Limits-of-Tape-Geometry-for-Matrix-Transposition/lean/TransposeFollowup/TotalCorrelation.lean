import TransposeFollowup.ConditionalObservation

/-! Finite conditional total correlation and deterministic local processing. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def conditionalTotalCorrelation {Ω ι α C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype C]
    (p : Ω → ℝ) (A : Ω → ι → α) (w : Ω → C) : ℝ :=
  (∑ i, conditionalObservationEntropy p (fun x => A x i) w) -
    conditionalObservationEntropy p A w

theorem conditionalTotalCorrelation_nonneg {Ω ι α C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype C]
    [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (A : Ω → ι → α) (w : Ω → C) :
    0 ≤ conditionalTotalCorrelation p A w :=
  sub_nonneg.mpr (conditionalObservationEntropy_pi_le_sum p hp A w)

theorem local_observation_factorsThrough {Ω ι α β C : Type*}
    (A : Ω → ι → α) (M : Ω → ι → β) (w : Ω → C)
    (h : ∀ i, (fun x => M x i).FactorsThrough (fun x => (w x, A x i))) :
    M.FactorsThrough (fun x => (w x, A x)) := by
  intro x y he
  funext i
  exact h i (Prod.ext (congrArg (fun z : C × (ι → α) => z.1) he)
    (congrFun (congrArg (fun z : C × (ι → α) => z.2) he) i))

/-- Publicly observing a separate deterministic function of each block does
not increase the blocks' conditional total correlation. -/
theorem conditionalTotalCorrelation_local_observation_le {Ω ι α β C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β] [Fintype C]
    [Nonempty α] [Nonempty β] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (M : Ω → ι → β) (w : Ω → C)
    (h : ∀ i, (fun x => M x i).FactorsThrough (fun x => (w x, A x i))) :
    conditionalTotalCorrelation p A (fun x => (w x, M x)) ≤
      conditionalTotalCorrelation p A w := by
  have hlocal : ∀ i,
      conditionalObservationEntropy p (fun x => A x i) (fun x => (w x, M x)) +
        conditionalObservationEntropy p (fun x => M x i) w ≤
      conditionalObservationEntropy p (fun x => A x i) w := by
    intro i
    have hc := conditionalObservationEntropy_chain_of_factorsThrough p hp
      (fun x => A x i) (fun x => M x i) w (h i)
    have hm := conditionalObservationEntropy_condition_le p hp (fun x => A x i)
      (fun x => (w x, M x i)) (fun x => (w x, M x))
      (fun x y he => Prod.ext (congrArg (fun z : C × (ι → β) => z.1) he)
        (congrFun (congrArg (fun z : C × (ι → β) => z.2) he) i))
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
  rw [Finset.sum_add_distrib] at hs
  have hc := conditionalObservationEntropy_chain_of_factorsThrough p hp A M w
    (local_observation_factorsThrough A M w h)
  have hm := conditionalObservationEntropy_pi_le_sum p hp M w
  dsimp only [conditionalTotalCorrelation]
  linarith

/-- Applying separate deterministic maps to the blocks cannot increase total
correlation, even when each map also knows the conditioning observation. -/
theorem conditionalTotalCorrelation_local_processing_le {Ω ι α β C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β] [Fintype C]
    [Nonempty α] [Nonempty β] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (M : Ω → ι → β) (w : Ω → C)
    (h : ∀ i, (fun x => M x i).FactorsThrough (fun x => (w x, A x i))) :
    conditionalTotalCorrelation p M w ≤ conditionalTotalCorrelation p A w := by
  have heach : ∀ i,
      conditionalObservationEntropy p (fun x => A x i) w =
        conditionalObservationEntropy p (fun x => M x i) w +
        conditionalObservationEntropy p (fun x => A x i) (fun x => (w x, M x i)) :=
    fun i => conditionalObservationEntropy_chain_of_factorsThrough p hp
      (fun x => A x i) (fun x => M x i) w (h i)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => heach i)
  rw [Finset.sum_add_distrib] at hsum
  have hc := conditionalObservationEntropy_chain_of_factorsThrough p hp A M w
    (local_observation_factorsThrough A M w h)
  have hm := conditionalObservationEntropy_pi_le_sum p hp A (fun x => (w x, M x))
  have hcond := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    conditionalObservationEntropy_condition_le p hp (fun x => A x i)
      (fun x => (w x, M x i)) (fun x => (w x, M x))
      (fun x y he => Prod.ext (congrArg (fun z : C × (ι → β) => z.1) he)
        (congrFun (congrArg (fun z : C × (ι → β) => z.2) he) i)))
  dsimp only [conditionalTotalCorrelation]
  linarith


theorem conditionalTotalCorrelation_condition_eq_of_same_fibers {Ω ι α C D : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype C] [Fintype D]
    [Nonempty α] [Nonempty C] [Nonempty D]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (w : Ω → C) (v : Ω → D)
    (h : ∀ x y, w x = w y ↔ v x = v y) :
    conditionalTotalCorrelation p A w = conditionalTotalCorrelation p A v := by
  unfold conditionalTotalCorrelation
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact conditionalObservationEntropy_condition_eq_of_same_fibers p hp _ w v h
  · exact conditionalObservationEntropy_condition_eq_of_same_fibers p hp A w v h

/-- Combining a partition of coordinates into larger blocks decreases total
correlation. The partition may have empty parts. -/
theorem conditionalTotalCorrelation_grouping_le {Ω ι κ α C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Fintype C] [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (w : Ω → C) (owner : ι → κ) :
    conditionalTotalCorrelation p
      (fun x j => finiteView (Finset.univ.filter (fun i => owner i = j)) (A x)) w ≤
      conditionalTotalCorrelation p A w := by
  classical
  let G := fun x j => finiteView (Finset.univ.filter (fun i => owner i = j)) (A x)
  have heach : ∀ j i,
      conditionalObservationEntropy p (fun x => G x j i) w =
        if owner i = j then conditionalObservationEntropy p (fun x => A x i) w else 0 := by
    intro j i
    by_cases hij : owner i = j
    · simp only [hij, ite_true]
      congr 1
      funext x
      simp [G, finiteView, hij]
    · simp only [hij, ite_false]
      apply conditionalObservationEntropy_eq_zero p hp
      intro x y _
      simp [G, finiteView, hij]
  have hg : ∀ j, conditionalObservationEntropy p (fun x => G x j) w ≤
      ∑ i, if owner i = j then conditionalObservationEntropy p (fun x => A x i) w else 0 := by
    intro j
    simpa only [heach] using conditionalObservationEntropy_pi_le_sum p hp (fun x => G x j) w
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hg j)
  rw [Finset.sum_comm] at hsum
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
  have heq : conditionalObservationEntropy p G w = conditionalObservationEntropy p A w := by
    apply conditionalObservationEntropy_eq_of_same_fibers p hp
    intro x y _
    constructor
    · intro hxy
      funext i
      have hh := congrFun (congrFun hxy (owner i)) i
      simpa [G, finiteView] using hh
    · intro hxy
      simp only [G, hxy]
  change (∑ j, conditionalObservationEntropy p (fun x => G x j) w) -
      conditionalObservationEntropy p G w ≤ _
  rw [heq]
  exact sub_le_sub_right hsum _

/-- A coordinate determined by the conditioning observation contributes
nothing to total correlation and can be discarded. -/
theorem conditionalTotalCorrelation_option {Ω ι α C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype C]
    [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (A : Ω → Option ι → α) (w : Ω → C)
    (h : (fun x => A x none).FactorsThrough w) :
    conditionalTotalCorrelation p A w =
      conditionalTotalCorrelation p (fun x i => A x (some i)) w := by
  have heq : conditionalObservationEntropy p A w =
      conditionalObservationEntropy p (fun x i => A x (some i)) w := by
    apply conditionalObservationEntropy_eq_of_same_fibers p hp
    intro x y hw
    constructor
    · exact fun he => funext (fun i => congrFun he (some i))
    · intro he
      funext i
      cases i with
      | none => exact h hw
      | some j => exact congrFun he j
  simp only [conditionalTotalCorrelation, Fintype.sum_option,
    conditionalObservationEntropy_eq_zero p hp _ w h, zero_add, heq]


/-- Separate functions of disjoint groups of latent coordinates cannot
increase conditional total correlation; unused coordinates are discarded. -/
theorem conditionalTotalCorrelation_disjoint_processing_le {Ω ι κ α β C : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype α] [Fintype β] [Fintype C]
    [Nonempty α] [Nonempty β] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : Ω → ι → α) (M : Ω → κ → β) (w : Ω → C) (R : κ → Finset ι)
    (hR : ∀ i j, i ≠ j → Disjoint (R i) (R j))
    (h : ∀ j, (fun x => M x j).FactorsThrough
      (fun x => (w x, finiteView (R j) (A x)))) :
    conditionalTotalCorrelation p M w ≤ conditionalTotalCorrelation p A w := by
  classical
  let owner : ι → Option κ := fun t =>
    if ht : ∃ j, t ∈ R j then some (Classical.choose ht) else none
  have howner : ∀ t j, owner t = some j ↔ t ∈ R j := by
    intro t j
    by_cases ht : ∃ j, t ∈ R j
    · simp only [owner, dite_eq_left ht, Option.some.injEq]
      constructor
      · intro he
        simpa only [he] using Classical.choose_spec ht
      · intro hj
        by_contra hne
        exact Finset.disjoint_left.mp (hR _ _ hne) (Classical.choose_spec ht) hj
    · simp only [owner, dite_eq_right ht, reduceCtorEq, false_iff]
      exact fun hj => ht ⟨j, hj⟩
  let G := fun x j => finiteView (Finset.univ.filter (fun t => owner t = j)) (A x)
  let N := fun x j => Option.elim j (Classical.choice ‹Nonempty β›) (M x)
  have hG : ∀ j, (fun x => G x (some j)) = fun x => finiteView (R j) (A x) := by
    intro j
    have he : Finset.univ.filter (fun t => owner t = some j) = R j := by
      ext t
      simp [howner]
    simp only [G, he]
  have hlocal : ∀ j, (fun x => N x j).FactorsThrough (fun x => (w x, G x j)) := by
    intro j
    cases j with
    | none => exact fun _ _ _ => rfl
    | some j =>
      intro x y he
      apply h j
      have hw := congrArg (fun z : C × (ι → α) => z.1) he
      have hg := congrArg (fun z : C × (ι → α) => z.2) he
      change G x (some j) = G y (some j) at hg
      rw [congrFun (hG j) x, congrFun (hG j) y] at hg
      exact Prod.ext hw hg
  have hg := conditionalTotalCorrelation_grouping_le p hp A w owner
  have hn := conditionalTotalCorrelation_local_processing_le p hp G N w hlocal
  have heq := conditionalTotalCorrelation_option p hp N w (fun _ _ _ => rfl)
  change conditionalTotalCorrelation p N w = conditionalTotalCorrelation p M w at heq
  rw [← heq]
  exact hn.trans hg

end TransposeFollowup
