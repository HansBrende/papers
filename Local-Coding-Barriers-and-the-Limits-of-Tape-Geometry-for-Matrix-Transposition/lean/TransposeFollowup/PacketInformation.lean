import TransposeFollowup.PacketComponentViews
import TransposeFollowup.TotalCorrelation

/-! The information budget of a selected family of deficient components.
The distribution may be correlated and correctness is not used here. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false

theorem observationEntropy_pair_le_sum {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : Ω → A) (g : Ω → B) :
    observationEntropy p (fun x => (f x, g x)) ≤
      observationEntropy p f + observationEntropy p g := by
  let q := pushforward p (fun x => (f x, g x))
  have h := entropy_subadditive q (pushforward_nonneg p hp _)
  have hq : ∑ x, q x = 1 := (sum_pushforward p _).trans hp1
  rw [hq, Real.negMulLog_one, add_zero] at h
  simpa only [q, pushforward_comp, Function.comp_def, observationEntropy] using h

theorem conditionalObservationEntropy_le_observation {Ω A C : Type*}
    [Fintype Ω] [Fintype A] [Fintype C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : Ω → A) (w : Ω → C) :
    conditionalObservationEntropy p f w ≤ observationEntropy p f := by
  have h := observationEntropy_pair_le_sum p hp hp1 w f
  dsimp only [conditionalObservationEntropy]
  linarith

noncomputable def coordinateBlockViews {Ω V : Type*} [Fintype V]
    (U : Finset (Finset V)) (Y : Ω → V → Bool) : Ω → U → (V → Bool) :=
  fun x S => bitView S.val (Y x)

theorem coordinateBlockViews_joint_eq {Ω V : Type*} [Fintype Ω] [Fintype V]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (U : Finset (Finset V)) (Y : Ω → V → Bool) :
    observationEntropy p (fun x =>
      (bitView (CoordinateSystem.outsideCoordinates U) (Y x), coordinateBlockViews U Y x)) =
      observationEntropy p Y := by
  apply observationEntropy_eq_of_same_fibers p hp
  intro x y
  constructor
  · intro h
    funext v
    by_cases hv : v ∈ U.biUnion id
    · obtain ⟨S, hSU, hvS⟩ := Finset.mem_biUnion.mp hv
      have he := congrFun (congrArg Prod.snd h) (⟨S, hSU⟩ : U)
      exact (bitView_eq_iff S _ _).mp he v hvS
    · exact (bitView_eq_iff _ _ _).mp (congrArg Prod.fst h) v
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩)
  · intro h
    apply Prod.ext
    · exact congrArg (bitView (CoordinateSystem.outsideCoordinates U)) h
    · funext S
      exact congrArg (bitView S.val) h

theorem coordinateBlockViews_tc_le_deficit {Ω V : Type*} [Fintype Ω] [Fintype V]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (U : Finset (Finset V)) (hdis : (U : Set (Finset V)).PairwiseDisjoint id)
    (Y : Ω → V → Bool) :
    conditionalTotalCorrelation p (coordinateBlockViews U Y)
      (fun x => bitView (CoordinateSystem.outsideCoordinates U) (Y x)) ≤
      (Fintype.card V : ℝ) * Real.log 2 - observationEntropy p Y := by
  let E := fun x => bitView (CoordinateSystem.outsideCoordinates U) (Y x)
  have hsum : (∑ S : U, conditionalObservationEntropy p
      (fun x => coordinateBlockViews U Y x S) E) ≤
      ∑ S : U, (S.val.card : ℝ) * Real.log 2 := by
    apply Finset.sum_le_sum
    intro S _
    exact (conditionalObservationEntropy_le_observation p hp hp1 _ E).trans
      (coordinateEntropy_le_card p hp hp1 Y S.val)
  have houtside := coordinateEntropy_le_card p hp hp1 Y (CoordinateSystem.outsideCoordinates U)
  have hjoint := coordinateBlockViews_joint_eq p hp U Y
  have hcards : (∑ S : U, (S.val.card : ℝ)) = ((U.biUnion id).card : ℝ) := by
    have hn : (∑ S : U, S.val.card) = (U.biUnion id).card := by
      calc
        _ = ∑ S ∈ U, S.card := by exact Finset.sum_coe_sort U Finset.card
        _ = _ := (Finset.card_biUnion hdis).symm
    exact_mod_cast hn
  have htotal : ((CoordinateSystem.outsideCoordinates U).card : ℝ) +
      ((U.biUnion id).card : ℝ) = Fintype.card V := by
    exact_mod_cast (show (CoordinateSystem.outsideCoordinates U).card +
      (U.biUnion id).card = Fintype.card V from by
        simpa only [CoordinateSystem.outsideCoordinates, Finset.card_univ] using
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (U.biUnion id)))
  rw [← Finset.sum_mul, hcards] at hsum
  dsimp only [conditionalTotalCorrelation, conditionalObservationEntropy]
  change (∑ S : U, conditionalObservationEntropy p
      (fun x => coordinateBlockViews U Y x S) E) -
      (observationEntropy p (fun x => (E x, coordinateBlockViews U Y x)) -
       observationEntropy p E) ≤ _
  change observationEntropy p (fun x => (E x, coordinateBlockViews U Y x)) = _ at hjoint
  change observationEntropy p E ≤ _ at houtside
  rw [hjoint, ← htotal, add_mul]
  linarith

namespace CoordinateSystem

variable {Ω V : Type*} [Fintype Ω] [Fintype V] {B : ℕ} (C : CoordinateSystem V B)

theorem selected_record_entropy (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (Y : Ω → V → Bool) :
    observationEntropy p (fun x =>
      (bitView (outsideCoordinates U) (Y x), C.broadcast (Y x))) ≤
      ((Fintype.card V : ℝ) - U.card) * Real.log 2 := by
  have hcomp : U ⊆ C.components := fun _ h => ((C.mem_deficient _).mp (hU h)).1
  have hfac : (fun x => (bitView (outsideCoordinates U) (Y x), C.broadcast (Y x))).FactorsThrough
      (fun x => (bitView (outsideCoordinates U) (Y x),
        bitView (C.selectedPackets U) (C.broadcast (Y x)))) := by
    intro x y h
    exact C.selected_view_factors U hcomp h
  have hle := observationEntropy_le_of_factorsThrough p hp _ _ hfac
  have hpair := observationEntropy_pair_le_sum p hp hp1
    (fun x => bitView (outsideCoordinates U) (Y x))
    (fun x => bitView (C.selectedPackets U) (C.broadcast (Y x)))
  have hleft := coordinateEntropy_le_card p hp hp1 Y (outsideCoordinates U)
  have hright := coordinateEntropy_le_card p hp hp1 (fun x => C.broadcast (Y x)) (C.selectedPackets U)
  have hcard : ((outsideCoordinates U).card : ℝ) + (C.selectedPackets U).card + U.card =
      Fintype.card V := by exact_mod_cast C.selected_record_card U hU
  change observationEntropy p (fun x => bitView (outsideCoordinates U) (Y x)) ≤ _ at hleft
  change observationEntropy p (fun x => bitView (C.selectedPackets U) (C.broadcast (Y x))) ≤ _ at hright
  have hc : (Fintype.card V : ℝ) - U.card =
      (outsideCoordinates U).card + (C.selectedPackets U).card := by linarith
  rw [hc, add_mul]
  linarith

theorem selected_conditional_entropy_lower (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (Y : Ω → V → Bool) :
    (U.card : ℝ) * Real.log 2 -
      ((Fintype.card V : ℝ) * Real.log 2 - observationEntropy p Y) ≤
    conditionalObservationEntropy p Y
      (fun x => (bitView (outsideCoordinates U) (Y x), C.broadcast (Y x))) := by
  have h := C.selected_record_entropy p hp hp1 U hU Y
  have he : observationEntropy p (fun x =>
      ((bitView (outsideCoordinates U) (Y x), C.broadcast (Y x)), Y x)) =
      observationEntropy p Y := by
    apply observationEntropy_pair_of_factorsThrough p hp Y
    intro x y hxy
    simp only [hxy]
  dsimp only [conditionalObservationEntropy]
  rw [he]
  nlinarith

/-- Revealing each component's own packet values cannot increase total
correlation. Once outside coordinates are fixed, these local values and the
complete broadcast have exactly the same fibers. No independence or
correctness premise is needed. -/
theorem selected_tc_le_deficit (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (U : Finset (Finset V)) (hU : U ⊆ C.deficient)
    (Y : Ω → V → Bool) :
    conditionalTotalCorrelation p (coordinateBlockViews U Y)
      (fun x => (bitView (outsideCoordinates U) (Y x), C.broadcast (Y x))) ≤
      (Fintype.card V : ℝ) * Real.log 2 - observationEntropy p Y := by
  let A := coordinateBlockViews U Y
  let E := fun x => bitView (outsideCoordinates U) (Y x)
  let M : Ω → U → (Fin B → Bool) :=
    fun x S => bitView (C.packetIndices S.val) (C.broadcast (Y x))
  have hcomp : U ⊆ C.components := fun _ h => ((C.mem_deficient _).mp (hU h)).1
  have hdis : (U : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS T hT hne
    exact C.components_disjoint (hcomp hS) (hcomp hT) hne
  have hlocal : ∀ S : U, (fun x => M x S).FactorsThrough (fun x => (E x, A x S)) := by
    intro S x y h
    exact C.local_packet_view_factors S.val (congrArg Prod.snd h)
  have hle := conditionalTotalCorrelation_local_observation_le p hp A M E hlocal
  have heq : conditionalTotalCorrelation p A
      (fun x => (E x, C.broadcast (Y x))) =
      conditionalTotalCorrelation p A (fun x => (E x, M x)) := by
    apply conditionalTotalCorrelation_condition_eq_of_same_fibers p hp
    intro x y
    constructor
    · intro h
      have hE : E x = E y := congrArg (fun z : (V → Bool) × (Fin B → Bool) => z.1) h
      refine Prod.ext hE ?_
      funext S
      exact congrArg (bitView (C.packetIndices S.val)) (congrArg Prod.snd h)
    · intro h
      have hE : E x = E y := congrArg (fun z : (V → Bool) × (U → Fin B → Bool) => z.1) h
      refine Prod.ext hE ?_
      apply C.broadcast_eq_of_local_views U hcomp hE
      intro S hS
      exact congrFun (congrArg Prod.snd h) ⟨S, hS⟩
  change conditionalTotalCorrelation p A (fun x => (E x, C.broadcast (Y x))) ≤ _
  rw [heq]
  exact hle.trans (coordinateBlockViews_tc_le_deficit p hp hp1 U hdis Y)

end CoordinateSystem
end TransposeFollowup
