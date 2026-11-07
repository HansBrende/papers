import TapeStorageRates.PatchPrediction

/-! # A finite probability bound for transcript-selected patch predictors

The transcript specifies each scored target, its permitted helpers and the
prediction rule before the correctness of predictions is scored. Its cost is
the logarithm of the number of different labels attained on the event.
-/

namespace TapeStorageRates

open Finset TransposeFollowup
open scoped BigOperators
set_option autoImplicit false

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] {w r : ℕ}

/-- Any family on which the declared predictors attain the specified error
fraction pays the prediction deficit in its log-cardinality. -/
theorem PatchPredictor.log_card_le_of_mistakeCount (D : PatchPredictor V J w r)
    (C : Finset (V → Bool)) (hC : C.Nonempty) {e : ℝ} (he : e ∈ Set.Icc 0 (2:ℝ)⁻¹)
    (hr : 0 < r) {m : ℕ} (hm : m ≤ D.targetCount)
    (hmist : ∀ x ∈ C, (D.mistakeCount x : ℝ) ≤ e * D.targetCount) :
    Real.logb 2 C.card ≤ Fintype.card V - m * (1 - Real.binEntropy e / Real.log 2) / (2*r) := by
  let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
  let p := uniformWeight C
  let X (x : C) := x.val
  have hp := uniformWeight_nonneg C
  have hp1 := sum_uniformWeight C
  have hmean := D.meanError_le_of_mistakeCount p hp hp1 X he.1 fun x => hmist _ x.2
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    ⟨D.meanError_nonneg p hp X, hmean.trans he.2⟩ he hmean
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnon : 0 ≤ 1 - Real.binEntropy e / Real.log 2 :=
    sub_nonneg.mpr ((div_le_one hlog).mpr Real.binEntropy_le_log_two)
  have hobs : observationEntropy p X = Real.log C.card := by
    rw [observationEntropy_injective p hp _ Subtype.val_injective]
    simpa only [Fintype.card_coe] using entropy_uniformWeight C
  have hd := D.prediction_deficit p hp hp1 X
  rw [hobs, ← Real.logb] at hd
  have hnum : (m : ℝ) * (1 - Real.binEntropy e / Real.log 2) ≤
      (2*r) * (Fintype.card V - Real.logb 2 C.card) := by
    apply le_trans _ hd
    exact mul_le_mul (by exact_mod_cast hm)
      (sub_le_sub_left (div_le_div_of_nonneg_right hmono hlog.le) _) hnon (Nat.cast_nonneg _)
  have hdiv := (div_le_iff₀' (show (0:ℝ) < 2*r by positivity)).mpr hnum
  linarith

/-- A menu of at most 2^h predictor systems can collectively cover at
most the stated fraction of the binary cube. Any one of the listed systems
may certify an input. Both the number of patches and their data can vary. -/
theorem patch_prediction_menu_probability {Z : Type*} {Jz : Z → Type*}
    [∀ z, Fintype (Jz z)] (E : Finset (V → Bool)) (menu : Finset Z)
    (D : (z : Z) → PatchPredictor V (Jz z) w r) {m : ℕ} {h e : ℝ}
    (hlabels : (menu.card : ℝ) ≤ (2:ℝ)^h) (he : e ∈ Set.Icc 0 (2:ℝ)⁻¹)
    (hr : 0 < r) (hcover : ∀ x ∈ E, ∃ z ∈ menu, m ≤ (D z).targetCount ∧
      ((D z).mistakeCount x : ℝ) ≤ e * (D z).targetCount) :
    (E.card : ℝ) / 2^(Fintype.card V) ≤
      (2:ℝ)^(h - m * (1 - Real.binEntropy e / Real.log 2) / (2*r)) := by
  classical
  let loss := (m : ℝ) * (1 - Real.binEntropy e / Real.log 2) / (2*r)
  let F (z : Z) := E.filter fun x => m ≤ (D z).targetCount ∧
    ((D z).mistakeCount x : ℝ) ≤ e * (D z).targetCount
  have bound (z : Z) :
      ((F z).card : ℝ) ≤ (2 : ℝ)^(Fintype.card V - loss) := by
    rcases (F z).eq_empty_or_nonempty with hF | hF
    · simp only [hF, card_empty, Nat.cast_zero]
      positivity
    obtain ⟨x,hx⟩ := hF
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2)
      (show (0:ℝ) < (F z).card by exact_mod_cast (card_pos.mpr ⟨x,hx⟩))).mp
    exact (D z).log_card_le_of_mistakeCount (F z) ⟨x,hx⟩ he hr (mem_filter.mp hx).2.1
      (fun y hy => (mem_filter.mp hy).2.2)
  have hsub : E ⊆ menu.biUnion F := by
    intro x hx
    obtain ⟨z,hz,hm⟩ := hcover x hx
    exact mem_biUnion.mpr ⟨z,hz,mem_filter.mpr ⟨hx,hm⟩⟩
  have htotal : (E.card : ℝ) ≤ (2:ℝ)^h * 2^(Fintype.card V - loss) := calc
    (E.card : ℝ) ≤ ∑ z ∈ menu, ((F z).card : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _z ∈ menu, (2:ℝ)^(Fintype.card V - loss) := sum_le_sum fun z _ => bound z
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hlabels (Real.rpow_nonneg (by norm_num) _)
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(Fintype.card V))).mpr
  calc
    _ ≤ _ := htotal
    _ = _ := by
      change (2:ℝ)^h * 2^(Fintype.card V - loss) = 2^(h - loss) * 2^(Fintype.card V)
      rw [← Real.rpow_natCast 2 (Fintype.card V), ← Real.rpow_add (by norm_num : (0:ℝ)<2),
        ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring

/-- The finite transcript bound. Only attained labels on E are charged.
The label specifies the scored targets as well as their prediction rules. -/
theorem patch_prediction_event_probability {Z : Type*} [DecidableEq Z] {Jz : Z → Type*}
    [∀ z, Fintype (Jz z)] (E : Finset (V → Bool)) (label : (V → Bool) → Z)
    (D : (z : Z) → PatchPredictor V (Jz z) w r) {m : ℕ} {h e : ℝ}
    (hlabels : ((E.image label).card : ℝ) ≤ (2:ℝ)^h) (he : e ∈ Set.Icc 0 (2:ℝ)⁻¹)
    (hr : 0 < r) (hm : ∀ x ∈ E, m ≤ (D (label x)).targetCount)
    (hmist : ∀ x ∈ E, ((D (label x)).mistakeCount x : ℝ) ≤ e * (D (label x)).targetCount) :
    (E.card : ℝ) / 2^(Fintype.card V) ≤
      (2:ℝ)^(h - m * (1 - Real.binEntropy e / Real.log 2) / (2*r)) :=
  patch_prediction_menu_probability E (E.image label) D hlabels he hr fun x hx =>
    ⟨label x, mem_image_of_mem _ hx, hm x hx, hmist x hx⟩

end TapeStorageRates
