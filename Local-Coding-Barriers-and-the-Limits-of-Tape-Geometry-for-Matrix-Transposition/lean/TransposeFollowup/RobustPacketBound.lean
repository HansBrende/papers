import TransposeFollowup.PacketDemandViews
import TransposeFollowup.PacketComponentCount
import TransposeFollowup.SharedDemandEntropy

/-! A distribution-sensitive lower bound for arbitrary two-coordinate packets
after a globally bijective recoding with bounded inverse row support. -/

namespace TransposeFollowup.InverseLocalPacketCode

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b B : ℕ} {Ω : Type*} [Fintype Ω]

theorem input_deficit_nonneg (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (X : Ω → FiniteMatrix d b) :
    0 ≤ ((d * d * b : ℕ) : ℝ) - observationEntropy p X / Real.log 2 := by
  have he : observationEntropy p (fun x => matrixBits (X x)) =
      observationEntropy p X := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    exact ⟨fun h => matrixBits_injective d b h, fun h => congrArg matrixBits h⟩
  have hcap := coordinateEntropy_le_card p hp hp1
    (fun x => matrixBits (X x)) Finset.univ
  rw [coordinateEntropy_univ, he] at hcap
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    ← Nat.mul_assoc] at hcap
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact sub_nonneg.mpr ((div_le_iff₀ hlog).mpr hcap)

set_option maxHeartbeats 1200000 in
/-- The graph is on stored rows. The receivers still know their original raw
rows, and the source distribution need not be uniform or have full support. -/
theorem broadcast_lower_bound_of_distribution (C : InverseLocalPacketCode d b B)
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (G : SimpleGraph (Fin d)) (hG : C.LocalTo G) (ell K : ℕ) (hell : 0 < ell)
    (hdegree : ∀ i, (inverseSupportGraph C.bank.support G ell).degree i ≤ K) :
    ((ell : ℝ) + 1) * (((d * d * b : ℕ) : ℝ) - (B : ℝ)) ≤
      ((d * d * b : ℕ) : ℝ) +
      (ell : ℝ) * (inverseNearBits (b := b) C.bank.support G ell).card +
      (ell : ℝ) * (1 + min (d : ℝ) (16 * ((K : ℝ) + 1) ^ 2)) *
        (((d * d * b : ℕ) : ℝ) - observationEntropy p X / Real.log 2) := by
  let : DecidableEq (MatrixBit d b) := Classical.decEq _
  let U := C.system.smallComponents ell
  let Y := fun x => C.bank.recode (X x)
  let W := C.publicView U X
  let A := C.componentVariables U X
  let N := inverseNearBits (b := b) C.bank.support G ell
  let Z : Ω → C.farCoordinates G ell → Bool :=
    fun x v => matrixBits (X x) v.val
  let m := min (d : ℝ) (16 * ((K : ℝ) + 1) ^ 2)
  let D := ((d * d * b : ℕ) : ℝ) * Real.log 2 - observationEntropy p X
  have hU : U ⊆ C.system.deficient := by
    intro S hS
    exact (Finset.mem_filter.mp hS).1
  have hcomp : ∀ S ∈ U, S ∈ C.system.components ∧ S.card ≤ ell := by
    intro S hS
    obtain ⟨hdef, hsize⟩ := Finset.mem_filter.mp hS
    exact ⟨((C.system.mem_deficient S).mp hdef).1, hsize⟩
  have hY : observationEntropy p Y = observationEntropy p X := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    exact ⟨fun h => C.bank.recode.injective h, fun h => congrArg C.bank.recode h⟩
  have hcondY : conditionalObservationEntropy p Y W =
      conditionalObservationEntropy p X W := by
    apply conditionalObservationEntropy_eq_of_same_fibers p hp
    intro x y _
    exact ⟨fun h => C.bank.recode.injective h, fun h => congrArg C.bank.recode h⟩
  have hW : (fun x => (bitView (CoordinateSystem.outsideCoordinates U) (Y x),
      C.system.broadcast (Y x))) = W := by
    funext x
    apply Prod.ext
    · funext v
      simp only [W, publicView, Y, bitView]
      split_ifs <;> rfl
    · rfl
  have hA : coordinateBlockViews U Y = A := by
    funext x S v
    simp only [A, componentVariables, coordinateBlockViews, Y, bitView]
  have hlow : (U.card : ℝ) * Real.log 2 - D ≤
      conditionalObservationEntropy p X W := by
    have h := C.system.selected_conditional_entropy_lower p hp hp1 U hU Y
    rw [hW, hcondY, hY] at h
    simpa only [D, Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc] using h
  have htc : conditionalTotalCorrelation p A W ≤ D := by
    have h := C.system.selected_tc_le_deficit p hp hp1 U hU Y
    rw [hW, hA, hY] at h
    simpa only [D, Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc] using h
  have hfar : conditionalObservationEntropy p Z W ≤ m * D := by
    have h := sharedDemand_conditionalEntropy_le_min p hp A Z W
      (C.latentRowComponents U) (fun v => v.val.1) (fun v => v.val.2.1)
      (inverseSupportGraph C.bank.support G ell) K hdegree
      (fun v => (C.far_endpoints v).1) (fun v => (C.far_endpoints v).2)
      (by
        intro i j hij hnot
        apply C.latentRowComponents_disjoint hG U hcomp
        intro hn
        exact hnot ⟨hij, hn⟩)
      (by
        intro v x y he
        have hw : W x = W y := congrArg
          (fun z : ((MatrixBit d b → Bool) × (Fin B → Bool)) ×
            (U → MatrixBit d b → Bool) => z.1) he
        apply C.far_source_factors U X v
        apply Prod.ext
        · exact hw
        · funext S
          by_cases hS : S ∈ C.latentRowComponents U v.val.1
          · have hv := (finiteView_eq_iff _ _ _).mp (congrArg Prod.snd he) S hS
            simpa [finiteView, hS] using hv
          · simp [finiteView, hS])
      (by
        intro v x y he
        have hw : W x = W y := congrArg
          (fun z : ((MatrixBit d b → Bool) × (Fin B → Bool)) ×
            (U → MatrixBit d b → Bool) => z.1) he
        apply C.far_receiver_factors U X hc v
        apply Prod.ext
        · exact hw
        · funext S
          by_cases hS : S ∈ C.latentRowComponents U v.val.2.1
          · have hv := (finiteView_eq_iff _ _ _).mp (congrArg Prod.snd he) S hS
            simpa [finiteView, hS] using hv
          · simp [finiteView, hS])
    have hm : 0 ≤ m := le_min (Nat.cast_nonneg _) (by positivity)
    have h' : conditionalObservationEntropy p Z W ≤
        m * conditionalTotalCorrelation p A W := by
      simpa only [Fintype.card_fin, m] using h
    exact h'.trans (mul_le_mul_of_nonneg_left htc hm)
  let near := fun x => bitView N (matrixBits (X x))
  have hsplit : X.FactorsThrough (fun x => (W x, (near x, Z x))) := by
    intro x y he
    apply matrixBits_injective d b
    funext v
    by_cases hv : v ∈ N
    · have hn : near x = near y := congrArg
        (fun z : ((MatrixBit d b → Bool) × (Fin B → Bool)) ×
          ((MatrixBit d b → Bool) × (C.farCoordinates G ell → Bool)) => z.2.1) he
      exact (bitView_eq_iff N _ _).mp hn v hv
    · have hf : Z x = Z y := congrArg
        (fun z : ((MatrixBit d b → Bool) × (Fin B → Bool)) ×
          ((MatrixBit d b → Bool) × (C.farCoordinates G ell → Bool)) => z.2.2) he
      have hvf : v ∈ C.farCoordinates G ell := by
        simp only [farCoordinates, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact hv
      exact congrFun hf ⟨v, hvf⟩
  have hnear : conditionalObservationEntropy p near W ≤ (N.card : ℝ) * Real.log 2 :=
    (conditionalObservationEntropy_le_observation p hp hp1 near W).trans
      (coordinateEntropy_le_card p hp hp1 (fun x => matrixBits (X x)) N)
  have hupper : conditionalObservationEntropy p X W ≤
      (N.card : ℝ) * Real.log 2 + m * D := by
    exact (conditionalObservationEntropy_le_of_factorsThrough p hp X
      (fun x => (near x, Z x)) W hsplit).trans
      ((conditionalObservationEntropy_subadditive p hp near Z W).trans
        (add_le_add hnear hfar))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : D = (((d * d * b : ℕ) : ℝ) -
      observationEntropy p X / Real.log 2) * Real.log 2 := by
    dsimp only [D]
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hlog)]
  have hsmall : (U.card : ℝ) ≤ (N.card : ℝ) + (1 + m) *
      (((d * d * b : ℕ) : ℝ) - observationEntropy p X / Real.log 2) := by
    apply (mul_le_mul_iff_left₀ hlog).mp
    rw [add_mul, mul_assoc, ← hD]
    linarith
  have hcount : ((d * d * b : ℕ) : ℝ) ≤ (B : ℝ) + C.system.deficient.card := by
    have h := C.system.coordinate_count_le_broadcast_add_deficient
    simp only [Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc] at h
    exact_mod_cast h
  have hsize : ((ell : ℝ) + 1) * C.system.deficient.card ≤
      ((d * d * b : ℕ) : ℝ) + (ell : ℝ) * U.card := by
    have h := C.system.deficient_size_bound ell
    simp only [Fintype.card_prod, Fintype.card_fin, ← Nat.mul_assoc] at h
    exact_mod_cast h
  have hell0 : 0 ≤ (ell : ℝ) := le_of_lt (Nat.cast_pos.mpr hell)
  have hpre : ((ell : ℝ) + 1) * (((d * d * b : ℕ) : ℝ) - (B : ℝ)) ≤
      ((d * d * b : ℕ) : ℝ) + (ell : ℝ) * U.card := by
    have h := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ (ell : ℝ) + 1)
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsmall hell0
  change _ ≤ ((d * d * b : ℕ) : ℝ) + (ell : ℝ) * (N.card : ℝ) +
    (ell : ℝ) * (1 + m) *
      (((d * d * b : ℕ) : ℝ) - observationEntropy p X / Real.log 2)
  nlinarith

end TransposeFollowup.InverseLocalPacketCode
