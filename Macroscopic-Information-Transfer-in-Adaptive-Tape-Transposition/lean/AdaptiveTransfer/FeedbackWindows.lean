import AdaptiveTransfer.FeedbackTranscript

/-! Window recovery under one arbitrarily correlated law. The transcript is
paid once; repeated windows pay their actual entry state and the source
correlation. This module retains explicit local recovery premises; the
fixed-word consumer evaluation discharges them separately. -/

namespace AdaptiveTransfer

open TransposeFollowup Finset Classical
open scoped BigOperators

/-- One read-only recovery window pays the entry state and the window's
queried output rectangles, rather than all bits in the queried raw rows. -/
theorem feedback_window_entropy
    {Ω I A Y Z S : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [Fintype Y] [Fintype Z] [Fintype S]
    [Nonempty A] [Nonempty Y] [Nonempty Z] [Nonempty S]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (raw : Ω → I → A) (out : Ω → I → Y) (z : Ω → Z) (state : Ω → S)
    (queried : Finset I)
    (hlocal : ∀ i, (fun x => out x i).FactorsThrough (fun x => (z x, raw x i)))
    (hdecode : out.FactorsThrough (fun x => (z x, finiteView queried (raw x), state x))) :
    (∑ i, conditionalObservationEntropy μ (fun x => out x i) z) ≤
      conditionalTotalCorrelation μ raw z +
      conditionalObservationEntropy μ state (fun x => (z x, finiteView queried (raw x))) +
      ∑ i ∈ queried, conditionalObservationEntropy μ (fun x => out x i) z := by
  let mixed : Ω → I → A ⊕ Y := fun x i =>
    if i ∈ queried then Sum.inl (raw x i) else Sum.inr (out x i)
  have hmix : ∀ i, (fun x => mixed x i).FactorsThrough (fun x => (z x, raw x i)) := by
    intro i x y he
    by_cases hi : i ∈ queried
    · simp only [mixed, hi, ite_true, Sum.inl.injEq]
      exact congrArg Prod.snd he
    · simp only [mixed, hi, ite_false, Sum.inr.injEq]
      exact hlocal i he
  have hc := conditionalTotalCorrelation_local_processing_le μ hμ raw mixed z hmix
  have heach (i : I) : conditionalObservationEntropy μ (fun x => mixed x i) z =
      if i ∈ queried then conditionalObservationEntropy μ (fun x => raw x i) z
      else conditionalObservationEntropy μ (fun x => out x i) z := by
    by_cases hi : i ∈ queried
    · simp only [hi, ite_true]
      apply conditionalObservationEntropy_eq_of_same_fibers μ hμ
      intro x y _
      simp only [mixed, hi, ite_true, Sum.inl.injEq]
    · simp only [hi, ite_false]
      apply conditionalObservationEntropy_eq_of_same_fibers μ hμ
      intro x y _
      simp only [mixed, hi, ite_false, Sum.inr.injEq]
  have hd : mixed.FactorsThrough (fun x => (z x, (finiteView queried (raw x), state x))) := by
    intro x y he
    have hz := congrArg Prod.fst he
    have hr := congrArg (fun v => v.2.1) he
    have hs := congrArg (fun v => v.2.2) he
    have ho := hdecode (Prod.ext hz (Prod.ext hr hs))
    funext i
    by_cases hi : i ∈ queried
    · simp only [mixed, hi, ite_true, Sum.inl.injEq]
      exact (finiteView_eq_iff _ _ _).mp hr i hi
    · simp only [mixed, hi, ite_false, Sum.inr.injEq]
      exact congrFun ho i
  have hb := conditionalObservationEntropy_le_of_factorsThrough μ hμ mixed
    (fun x => (finiteView queried (raw x), state x)) z hd
  rw [conditionalObservationEntropy_pair μ hμ] at hb
  have hq := conditionalObservationEntropy_finiteView_le_sum μ hμ raw z queried
  have hexpr : (∑ i, conditionalObservationEntropy μ (fun x => mixed x i) z) =
      (∑ i ∈ queried, conditionalObservationEntropy μ (fun x => raw x i) z) +
        (∑ i, conditionalObservationEntropy μ (fun x => out x i) z) -
        ∑ i ∈ queried, conditionalObservationEntropy μ (fun x => out x i) z := by
    simp_rw [heach]
    rw [sum_ite]
    simp only [univ_inter, filter_mem_eq_inter]
    have hh := sum_filter_add_sum_filter_not (s := univ) (p := fun i => i ∈ queried)
      (f := fun i => conditionalObservationEntropy μ (fun x => out x i) z)
    simp only [filter_mem_eq_inter, univ_inter] at hh
    linarith
  dsimp only [conditionalTotalCorrelation] at hc
  rw [hexpr] at hc
  dsimp only [conditionalTotalCorrelation]
  linarith

/-- All chronological output windows use the same input law and transcript.
Their local projections together recover each original owner block. -/
theorem feedback_windows_entropy
    {Ω I W A Y Z S : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] [Fintype A] [Fintype Y] [Fintype Z] [Fintype S]
    [Nonempty A] [Nonempty Y] [Nonempty Z] [Nonempty S]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (raw : Ω → I → A) (out : W → Ω → I → Y) (z : Ω → Z)
    (state : W → Ω → S) (queried : W → Finset I)
    (hlocal : ∀ w i, (fun x => out w x i).FactorsThrough (fun x => (z x, raw x i)))
    (hdecode : ∀ w, (out w).FactorsThrough
      (fun x => (z x, finiteView (queried w) (raw x), state w x)))
    (hcover : ∀ i, (fun x => raw x i).FactorsThrough (fun x => (z x, fun w => out w x i))) :
    conditionalObservationEntropy μ raw z ≤
      ((Fintype.card W : ℝ) - 1) * conditionalTotalCorrelation μ raw z +
      (∑ w, conditionalObservationEntropy μ (state w)
        (fun x => (z x, finiteView (queried w) (raw x)))) +
      ∑ w, ∑ i ∈ queried w, conditionalObservationEntropy μ (fun x => out w x i) z := by
  have hsum := sum_le_sum (fun w (_ : w ∈ univ) =>
    feedback_window_entropy μ hμ raw (out w) z (state w) (queried w) (hlocal w) (hdecode w))
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hblock (i : I) : conditionalObservationEntropy μ (fun x => raw x i) z ≤
      ∑ w, conditionalObservationEntropy μ (fun x => out w x i) z :=
    (conditionalObservationEntropy_le_of_factorsThrough μ hμ _ _ z (hcover i)).trans
      (conditionalObservationEntropy_pi_le_sum μ hμ (fun x w => out w x i) z)
  have hb := sum_le_sum (fun i (_ : i ∈ univ) => hblock i)
  rw [sum_comm] at hb
  dsimp only [conditionalTotalCorrelation]
  dsimp only [conditionalTotalCorrelation] at hsum
  nlinarith

end AdaptiveTransfer
