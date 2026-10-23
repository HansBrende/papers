import TransposeFollowup.RectangleEntropy
import TransposeFollowup.TotalCorrelation
import TransposeFollowup.EntropyFibers
import TransposeFollowup.ConditionalEntropyFibers

/-!
# Entropy assembly for full rectangular transcript fibers

All entropies use natural logarithms. The source distribution may be
correlated; rectangularity is a property of a containing full fiber only.
-/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

theorem conditionalObservationEntropy_finiteView_le_sum
    {Ω ι α C : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype C] [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ι → α)
    (w : Ω → C) (S : Finset ι) :
    conditionalObservationEntropy p (fun x => finiteView S (Y x)) w ≤
      ∑ i ∈ S, conditionalObservationEntropy p (fun x => Y x i) w := by
  have h := conditionalObservationEntropy_pi_le_sum p hp
    (fun x => finiteView S (Y x)) w
  have he (i : ι) : conditionalObservationEntropy p
      (fun x => finiteView S (Y x) i) w =
      if i ∈ S then conditionalObservationEntropy p (fun x => Y x i) w else 0 := by
    by_cases hi : i ∈ S
    · simp [finiteView, hi]
    · simp only [hi, ↓reduceIte]
      apply conditionalObservationEntropy_eq_zero p hp
      intro x y _
      simp [finiteView, hi]
  simpa only [he, Finset.sum_ite_mem, Finset.univ_inter] using h

/-- A coordinate tuple is determined by one coordinate and its complement. -/
theorem conditionalObservationEntropy_coordinate_complement
    {Ω ι α C : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype C] [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ι → α)
    (w : Ω → C) (i : ι) :
    conditionalObservationEntropy p Y w =
      conditionalObservationEntropy p
        (fun x => finiteView (Finset.univ.erase i) (Y x)) w +
      conditionalObservationEntropy p (fun x => Y x i)
        (fun x => (w x, finiteView (Finset.univ.erase i) (Y x))) := by
  have he : conditionalObservationEntropy p Y w =
      conditionalObservationEntropy p
        (fun x => (finiteView (Finset.univ.erase i) (Y x), Y x i)) w := by
    apply conditionalObservationEntropy_eq_of_same_fibers p hp
    intro x y _
    constructor
    · intro h
      rw [h]
    · intro h
      funext j
      by_cases hj : j = i
      · simpa [hj] using congrArg Prod.snd h
      · exact (finiteView_eq_iff _ _ _).mp (congrArg Prod.fst h) j (by simp [hj])
  rw [he]
  exact conditionalObservationEntropy_pair p hp _ _ w

/-- Summing the complement bounds counts each marginal exactly `card - 1`
times. No independence assumption is used. -/
theorem sum_conditional_complement_entropy_le
    {Ω ι α C : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype C] [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ι → α)
    (w : Ω → C) :
    (∑ i, conditionalObservationEntropy p
      (fun x => finiteView (Finset.univ.erase i) (Y x)) w) ≤
      ((Fintype.card ι : ℝ) - 1) *
        ∑ i, conditionalObservationEntropy p (fun x => Y x i) w := by
  calc
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
        conditionalObservationEntropy p (fun x => Y x j) w := by
      exact Finset.sum_le_sum (fun i _ =>
        conditionalObservationEntropy_finiteView_le_sum p hp Y w _)
    _ = _ := by
      have he (i : ι) :
          (∑ j ∈ Finset.univ.erase i,
            conditionalObservationEntropy p (fun x => Y x j) w) =
          (∑ j, conditionalObservationEntropy p (fun x => Y x j) w) -
            conditionalObservationEntropy p (fun x => Y x i) w := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      simp_rw [he]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The full-conditional entropy join. Correlations are explicitly charged
once through the total correlation of the tuple. -/
theorem conditionalObservationEntropy_full_join
    {Ω ι α C : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype C] [Nonempty α] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (Y : Ω → ι → α)
    (w : Ω → C) :
    conditionalObservationEntropy p Y w ≤
      (∑ i, conditionalObservationEntropy p (fun x => Y x i)
        (fun x => (w x, finiteView (Finset.univ.erase i) (Y x)))) +
      ((Fintype.card ι : ℝ) - 1) * conditionalTotalCorrelation p Y w := by
  have hc := sum_conditional_complement_entropy_le p hp Y w
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset ι)) rfl
    (fun i _ => conditionalObservationEntropy_coordinate_complement p hp Y w i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_add_distrib] at he
  dsimp only [conditionalTotalCorrelation]
  nlinarith

theorem conditionalObservationEntropy_const_condition
    {Ω A C : Type*} [Fintype Ω] [Fintype A] [Fintype C]
    [Nonempty A] [Nonempty C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (Y : Ω → A) (c : C) :
    conditionalObservationEntropy p Y (fun _ => c) = observationEntropy p Y := by
  have he : observationEntropy p (fun x => (c, Y x)) = observationEntropy p Y := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    simp
  simp only [conditionalObservationEntropy, he, observationEntropy_const, hp1,
    Real.negMulLog_one, sub_zero]

/-- Unconditional form of the full-conditional join. -/
theorem observationEntropy_full_join
    {Ω ι α : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (Y : Ω → ι → α) :
    observationEntropy p Y ≤
      (∑ i, conditionalObservationEntropy p (fun x => Y x i)
        (fun x => finiteView (Finset.univ.erase i) (Y x))) +
      ((Fintype.card ι : ℝ) - 1) *
        ((∑ i, observationEntropy p (fun x => Y x i)) - observationEntropy p Y) := by
  have h := conditionalObservationEntropy_full_join p hp Y (fun _ => ())
  have he (i : ι) : conditionalObservationEntropy p (fun x => Y x i)
      (fun x => ((), finiteView (Finset.univ.erase i) (Y x))) =
      conditionalObservationEntropy p (fun x => Y x i)
        (fun x => finiteView (Finset.univ.erase i) (Y x)) := by
    apply conditionalObservationEntropy_condition_eq_of_same_fibers p hp
    intro x y
    simp
  simpa only [conditionalTotalCorrelation, conditionalObservationEntropy_const_condition p hp hp1,
    he] using h

/-- Gibbs' inequality against the actual uniform full-fiber distribution.
The observation is applied to a larger full domain; the source need not be
uniform or cover that domain. -/
theorem fullFiberReference_budget
    {Ω V A : Type*} [Fintype Ω] [Fintype V] [Nonempty V] [Fintype A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (Y : Ω → V) (f : V → A) :
    observationEntropy p (f ∘ Y) +
      (∑ x, p x * Real.log (fiberCard f (f (Y x)) : ℝ)) ≤
      Real.log (Fintype.card V : ℝ) := by
  let q := pushforward (uniformWeight V) f
  have hv : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hf (x : Ω) : 0 < (fiberCard f (f (Y x)) : ℝ) := by
    apply Nat.cast_pos.mpr
    unfold fiberCard
    exact Finset.card_pos.mpr
      ⟨Y x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hq (x : Ω) : 0 < q (f (Y x)) := by
    rw [show q = pushforward (uniformWeight V) f from rfl, pushforward_uniformWeight]
    exact div_pos (hf x) hv
  have hsupport (a : A) (ha : 0 < pushforward p (f ∘ Y) a) : 0 < q a := by
    have hex : ∃ x, f (Y x) = a := by
      by_contra hn
      have hz : pushforward p (f ∘ Y) a = 0 := by
        simp [pushforward, not_exists.mp hn]
      linarith
    obtain ⟨x, rfl⟩ := hex
    exact hq x
  have h := entropy_le_crossEntropy (pushforward p (f ∘ Y)) q
    (pushforward_nonneg p hp _) (pushforward_nonneg _ (uniformWeight_nonneg V) _)
    (by rw [sum_pushforward, hp1])
    (by rw [show q = pushforward (uniformWeight V) f from rfl,
      sum_pushforward, sum_uniformWeight]) hsupport
  rw [sum_pushforward_mul] at h
  have hl (x : Ω) : Real.log (q (f (Y x))) =
      Real.log (fiberCard f (f (Y x)) : ℝ) - Real.log (Fintype.card V : ℝ) := by
    rw [show q = pushforward (uniformWeight V) f from rfl, pushforward_uniformWeight,
      Real.log_div (hf x).ne' hv.ne']
  simp only [Function.comp_apply, hl, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hp1, one_mul] at h
  change observationEntropy p (f ∘ Y) ≤ _ at h
  linarith

/-- Expected full-fiber entropy deficit is bounded by the original source
deficit. The transcript is not charged again as independent information. -/
theorem fullFiberReference_deficit
    {Ω V A : Type*} [Fintype Ω] [Fintype V] [Nonempty V]
    [Fintype A] [Nonempty A]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (Y : Ω → V) (f : V → A) :
    (∑ x, p x * Real.log (fiberCard f (f (Y x)) : ℝ)) -
      conditionalObservationEntropy p Y (f ∘ Y) ≤
      Real.log (Fintype.card V : ℝ) - observationEntropy p Y := by
  have hb := fullFiberReference_budget p hp hp1 Y f
  have he := observationEntropy_pair_of_factorsThrough p hp Y (f ∘ Y)
    (fun _ _ h => congrArg f h)
  dsimp only [conditionalObservationEntropy]
  rw [he]
  linarith

/-- Full-fiber entropy join directly in the coordinate-rectangle interface.
Only the containing reference fiber is rectangular; its actual sublaw may
have arbitrary correlations. -/
theorem coordinateRectangle_full_join
    {Ω ι κ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [Fintype κ]
    [Nonempty κ] [DecidableEq ι] [DecidableEq κ]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → ι → Bool) (owner : ι → κ)
    (R : Finset (ι → Bool)) (hR : CoordinateRectangle owner R)
    (hXR : ∀ x, X x ∈ R) :
    observationEntropy p X ≤
      (∑ a, conditionalObservationEntropy p
        (fun x => bitView (ownedCoordinates owner a) (X x))
        (fun x => bitView (ownedCoordinates owner a)ᶜ (X x))) +
      ((Fintype.card κ : ℝ) - 1) *
        (Real.log (R.card : ℝ) - observationEntropy p X) := by
  let Y := fun x a => bitView (ownedCoordinates owner a) (X x)
  have hjoint : observationEntropy p Y = observationEntropy p X := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    constructor
    · intro h
      funext i
      have hi := congrArg (fun z => z (owner i) i) h
      simpa [Y, bitView, ownedCoordinates] using hi
    · intro h
      simp [Y, h]
  have hcond (a : κ) :
      conditionalObservationEntropy p (fun x => Y x a)
        (fun x => finiteView (Finset.univ.erase a) (Y x)) =
      conditionalObservationEntropy p
        (fun x => bitView (ownedCoordinates owner a) (X x))
        (fun x => bitView (ownedCoordinates owner a)ᶜ (X x)) := by
    apply conditionalObservationEntropy_condition_eq_of_same_fibers p hp
    intro x y
    rw [finiteView_eq_iff, bitView_eq_iff]
    constructor
    · intro h i hi
      have hia : owner i ≠ a := by simpa [ownedCoordinates] using hi
      have hb := h (owner i) (by simp [hia])
      have hv := congrFun hb i
      simpa [Y, bitView, ownedCoordinates] using hv
    · intro h c hc
      apply (bitView_eq_iff _ _ _).mpr
      intro i hi
      have hic : owner i = c := by simpa [ownedCoordinates] using hi
      have hca : c ≠ a := (Finset.mem_erase.mp hc).1
      exact h i (by simp [ownedCoordinates, hic, hca])
  have hj := observationEntropy_full_join p hp hp1 Y
  simp only [hjoint, hcond] at hj
  have hm := sum_owned_entropy_le_log_rectangle p hp hp1 X owner R hR hXR
  have hq : 0 ≤ (Fintype.card κ : ℝ) - 1 := by
    have hpos : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
    linarith
  have hmul := mul_le_mul_of_nonneg_left hm hq
  change (∑ a, observationEntropy p (fun x => Y x a)) ≤ _ at hm
  dsimp only [coordinateEntropy] at hmul
  dsimp only [Y] at hj
  nlinarith

end TransposeFollowup
