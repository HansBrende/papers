import AdaptiveTransfer.FeedbackWindows
import TransposeFollowup.PacketInformation

/-! Finite output-coordinate covers. Rectangles need not be disjoint; each
source coordinate only has to appear in a window. All bounds use the same
arbitrary law and one common producer transcript. -/

namespace AdaptiveTransfer
open TransposeFollowup LeanMachine Finset Classical
open scoped BigOperators

variable {ι κ W Ω Z C : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype W] [DecidableEq W] [Nonempty W]
  [Fintype Ω] [Nonempty Ω] [Fintype Z] [Nonempty Z] [Fintype C] [Nonempty C]

noncomputable def feedbackProjection (owner : ι → κ) (columns : W → Finset ι)
    (X : Ω → ι → Bool) (w : W) (x : Ω) (a : κ) : ι → Bool :=
  bitView (ownedCoordinates owner a ∩ columns w) (X x)

/-- A coordinate-cover version retaining the exact queried rectangle sizes.
The recovery premise is discharged by actual read-only evaluation below. -/
theorem feedback_coordinate_bound
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (owner : ι → κ) (X : Ω → ι → Bool) (z : (ι → Bool) → Z)
    (hrect : ∀ a, CoordinateRectangle owner (univ.filter (fun x => z x = a)))
    (columns : W → Finset ι) (hcover : ∀ i, ∃ w, i ∈ columns w)
    (entry : W → Ω → C) (queried : W → Finset κ)
    (hdecode : ∀ w, (feedbackProjection owner columns X w).FactorsThrough
      (fun x => (z (X x), finiteView (queried w)
        (fun a => bitView (ownedCoordinates owner a) (X x)), entry w x)))
    (Zbits M Δ : ℝ)
    (hz : observationEntropy μ (z ∘ X) ≤ Zbits * Real.log 2)
    (hm : (Fintype.card C : ℝ) ≤ (2 : ℝ)^M)
    (hx : (Fintype.card ι - Δ) * Real.log 2 ≤ observationEntropy μ X) :
    (Fintype.card ι : ℝ) ≤ Zbits + Fintype.card W * (M + Δ) +
      ∑ w, ∑ a ∈ queried w, ((ownedCoordinates owner a ∩ columns w).card : ℝ) := by
  let raw := fun x a => bitView (ownedCoordinates owner a) (X x)
  let common := z ∘ X
  have hlocal (w : W) (a : κ) :
      (fun x => feedbackProjection owner columns X w x a).FactorsThrough
        (fun x => (common x, raw x a)) := by
    intro x y he
    exact bitView_factorsThrough X inter_subset_left (congrArg Prod.snd he)
  have hcov (a : κ) : (fun x => raw x a).FactorsThrough
      (fun x => (common x, fun w => feedbackProjection owner columns X w x a)) := by
    intro x y he
    apply (bitView_eq_iff _ _ _).mpr
    intro i hi
    obtain ⟨w, hw⟩ := hcover i
    exact (bitView_eq_iff _ _ _).mp
      (congrFun (congrArg Prod.snd he) w) i (mem_inter.mpr ⟨hi, hw⟩)
  have hwin := feedback_windows_entropy μ hμ raw (feedbackProjection owner columns X)
    common entry queried hlocal hdecode hcov
  have hc := rectangular_transcript_correlation_le_deficit owner μ hμ hμ1 X z hrect
  have hcr : conditionalTotalCorrelation μ raw common ≤ Δ * Real.log 2 := by
    dsimp only [raw, common]
    linarith
  have hm' (w : W) : conditionalObservationEntropy μ (entry w)
      (fun x => (common x, finiteView (queried w) (raw x))) ≤ M * Real.log 2 := by
    apply (conditionalObservationEntropy_le_observation μ hμ hμ1 _ _).trans
    have hh := entropy_le_log_card (pushforward μ (entry w))
      (pushforward_nonneg μ hμ _) (by rw [sum_pushforward, hμ1])
    exact hh.trans ((Real.log_le_log (by exact_mod_cast Fintype.card_pos (α := C)) hm).trans_eq
      (Real.log_rpow (by norm_num : (0 : ℝ)<2) M))
  have hrectbits (w : W) (a : κ) :
      conditionalObservationEntropy μ (fun x => feedbackProjection owner columns X w x a) common ≤
        (ownedCoordinates owner a ∩ columns w).card * Real.log 2 :=
    (conditionalObservationEntropy_le_observation μ hμ hμ1 _ _).trans
      (coordinateEntropy_le_card μ hμ hμ1 X _)
  have hsumM := sum_le_sum (fun w (_ : w ∈ univ) => hm' w)
  have hsumR := sum_le_sum (fun w (_ : w ∈ univ) =>
    sum_le_sum (fun a (_ : a ∈ queried w) => hrectbits w a))
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsumM
  simp only [← sum_mul] at hsumR
  have hcount : (0 : ℝ) ≤ Fintype.card W - 1 := by
    have := Fintype.card_pos (α := W)
    have : (1 : ℝ) ≤ Fintype.card W := by exact_mod_cast this
    linarith
  have htc := mul_le_mul_of_nonneg_left hcr hcount
  have he : conditionalObservationEntropy μ raw common =
      observationEntropy μ X - observationEntropy μ common := by
    unfold conditionalObservationEntropy
    congr 1
    apply observationEntropy_eq_of_same_fibers μ hμ
    intro x y
    constructor
    · intro h
      funext i
      exact (bitView_eq_iff _ _ _).mp (congrFun (congrArg Prod.snd h) (owner i)) i
        (by simp [ownedCoordinates])
    · intro h
      exact Prod.ext (congrArg z h) (by dsimp [raw]; rw [h])
  rw [he] at hwin
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_right hl).mp
  nlinarith

end AdaptiveTransfer
