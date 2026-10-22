import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Finite entropy estimates

Entropy uses natural logarithms here; dividing by `Real.log 2` gives bits.
The subprobability form is needed for the disjoint virtual transcript fibers
in the adaptive separator proof. No information inequality is postulated.
-/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Gibbs' inequality also holds when the comparison weights have total
mass at most one. Zero source weights impose no support condition. -/
theorem entropy_le_crossEntropy_of_sum_le {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsum_le : ∑ i, q i ≤ ∑ i, p i)
    (hsupport : ∀ i, 0 < p i → 0 < q i) :
    entropy p ≤ -(∑ i, p i * Real.log (q i)) := by
  have hpoint : ∀ i, p i * Real.log (q i) - p i * Real.log (p i) ≤ q i - p i := by
    intro i
    by_cases hzero : p i = 0
    · simpa [hzero] using hq i
    · have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hzero)
      have hqi := hsupport i hpi
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqi hpi)
      have hmul := mul_le_mul_of_nonneg_left hlog (hp i)
      rw [Real.log_div hqi.ne' hpi.ne', mul_sub] at hmul
      have heq : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rwa [heq] at hmul
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.sum_sub_distrib] at hsum
  have h : (∑ i, p i * Real.log (q i)) ≤ ∑ i, p i * Real.log (p i) := by
    linarith
  simpa only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    using neg_le_neg h

theorem entropy_le_crossEntropy {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i ≤ 1)
    (hsupport : ∀ i, 0 < p i → 0 < q i) :
    entropy p ≤ -(∑ i, p i * Real.log (q i)) :=
  entropy_le_crossEntropy_of_sum_le p q hp hq (hp1 ▸ hq1) hsupport

theorem entropy_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hp i)
  calc
    p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    _ = 1 := hp1

/-- A finite alphabet bounds entropy, with no positivity assumption on each
individual probability. -/
theorem entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    entropy p ≤ Real.log (Fintype.card α) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : ∑ _ : α, (Fintype.card α : ℝ)⁻¹ = 1 := by
    simp [hc.ne']
  have h := entropy_le_crossEntropy p (fun _ => (Fintype.card α : ℝ)⁻¹)
    hp (fun _ => inv_nonneg.mpr hc.le) hp1 hs.le
    (fun _ _ => inv_pos.mpr hc)
  simpa only [← Finset.sum_mul, hp1, one_mul, Real.log_inv, neg_neg] using h

open Classical in
/-- Distribution of a deterministic finite observation. -/
noncomputable def pushforward {α β : Type*} [Fintype α]
    (p : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

theorem pushforward_nonneg {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (f : α → β) (b : β) :
    0 ≤ pushforward p f b := by
  classical
  apply Finset.sum_nonneg
  intro a _
  by_cases h : f a = b <;> simp [h, hp]

theorem le_pushforward {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (f : α → β) (a : α) :
    p a ≤ pushforward p f (f a) := by
  classical
  calc
    p a = (if f a = f a then p a else 0) := by simp
    _ ≤ ∑ a', if f a' = f a then p a' else 0 := by
      apply Finset.single_le_sum (f := fun a' => if f a' = f a then p a' else 0)
        _ (Finset.mem_univ a)
      intro a' _
      by_cases h : f a' = f a <;> simp [h, hp]

theorem sum_pushforward {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) :
    ∑ b, pushforward p f b = ∑ a, p a := by
  classical
  simp only [pushforward]
  rw [Finset.sum_comm]
  simp

theorem sum_pushforward_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → ℝ) :
    ∑ b, pushforward p f b * g b = ∑ a, p a * g (f a) := by
  classical
  simp only [pushforward, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem pushforward_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → γ) :
    pushforward (pushforward p f) g = pushforward p (g ∘ f) := by
  classical
  funext c
  change (∑ b, if g b = c then pushforward p f b else 0) =
    ∑ a, if g (f a) = c then p a else 0
  simpa only [mul_ite, mul_one, mul_zero] using
    sum_pushforward_mul p f (fun b => if g b = c then 1 else 0)

/-- Computing an observation cannot increase entropy. This statement also
holds for nonnormalized nonnegative weights. -/
theorem entropy_pushforward_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (f : α → β) :
    entropy (pushforward p f) ≤ entropy p := by
  have hpoint : ∀ a, p a * Real.log (p a) ≤ p a * Real.log (pushforward p f (f a)) := by
    intro a
    by_cases hz : p a = 0
    · simp [hz]
    · have ha : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log ha (le_pushforward p hp f a)) (hp a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  rw [← sum_pushforward_mul p f (fun b => Real.log (pushforward p f b))] at hsum
  simpa only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    using neg_le_neg hsum

theorem pushforward_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (a : α) :
    pushforward p Prod.fst a = ∑ b, p (a, b) := by
  classical
  simp only [pushforward, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

theorem pushforward_snd {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (b : β) :
    pushforward p Prod.snd b = ∑ a, p (a, b) := by
  classical
  simp [pushforward, Fintype.sum_prod_type]

/-- Subadditivity with its exact mass correction. This unnormalized form
can be applied directly on each conditioning fiber, including empty ones. -/
theorem entropy_subadditive {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ ab, 0 ≤ p ab) :
    entropy p + Real.negMulLog (∑ ab, p ab) ≤
      entropy (pushforward p Prod.fst) + entropy (pushforward p Prod.snd) := by
  classical
  let s := ∑ ab, p ab
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun ab _ => hp ab)
  by_cases hs : s = 0
  · have hz : ∀ ab, p ab = 0 := by
      intro ab
      have hle : p ab ≤ s :=
        Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ ab)
      exact le_antisymm (hs ▸ hle) (hp ab)
    simp [entropy, pushforward, hz]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    let a := pushforward p Prod.fst
    let b := pushforward p Prod.snd
    have ha : ∀ x, 0 ≤ a x := pushforward_nonneg p hp Prod.fst
    have hb : ∀ y, 0 ≤ b y := pushforward_nonneg p hp Prod.snd
    have hapos : ∀ xy, 0 < p xy → 0 < a xy.1 :=
      fun xy h => lt_of_lt_of_le h (le_pushforward p hp Prod.fst xy)
    have hbpos : ∀ xy, 0 < p xy → 0 < b xy.2 :=
      fun xy h => lt_of_lt_of_le h (le_pushforward p hp Prod.snd xy)
    have hasum : ∑ x, a x = s := sum_pushforward p Prod.fst
    have hbsum : ∑ y, b y = s := sum_pushforward p Prod.snd
    let q := fun xy : α × β => a xy.1 * b xy.2 / s
    have hqsum : ∑ xy, q xy = s := by
      change (∑ xy : α × β, a xy.1 * b xy.2 / s) = s
      rw [← Finset.sum_div, Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, hasum, hbsum]
      field_simp
    have hcross := entropy_le_crossEntropy_of_sum_le p q hp
      (fun xy => div_nonneg (mul_nonneg (ha xy.1) (hb xy.2)) hs0)
      hqsum.le (fun xy h => div_pos (mul_pos (hapos xy h) (hbpos xy h)) hspos)
    have hpoint : ∀ xy, p xy * Real.log (q xy) =
        p xy * Real.log (a xy.1) + p xy * Real.log (b xy.2) -
          p xy * Real.log s := by
      intro xy
      by_cases hz : p xy = 0
      · simp [hz]
      · have hpos : 0 < p xy := lt_of_le_of_ne (hp xy) (Ne.symm hz)
        dsimp only [q]
        rw [Real.log_div (mul_pos (hapos xy hpos) (hbpos xy hpos)).ne' hs,
          Real.log_mul (hapos xy hpos).ne' (hbpos xy hpos).ne']
        ring
    simp_rw [hpoint] at hcross
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← sum_pushforward_mul p Prod.fst (fun x => Real.log (a x)),
      ← sum_pushforward_mul p Prod.snd (fun y => Real.log (b y))] at hcross
    change entropy p + Real.negMulLog s ≤ entropy a + entropy b
    simp only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at *
    linarith

/-- Strong subadditivity follows by applying the preceding inequality on
each common-conditioning fiber. No independence of the input is used. -/
theorem entropy_strong_subadditive {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : γ × (α × β) → ℝ) (hp : ∀ cab, 0 ≤ p cab) :
    entropy p + entropy (fun c => ∑ ab, p (c, ab)) ≤
      entropy (fun ca : γ × α => ∑ b, p (ca.1, (ca.2, b))) +
      entropy (fun cb : γ × β => ∑ a, p (cb.1, (a, cb.2))) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun c _ => entropy_subadditive (fun ab => p (c, ab)) (fun ab => hp (c, ab)))
  simpa only [entropy, pushforward_fst, pushforward_snd,
    Finset.sum_add_distrib, Fintype.sum_prod_type] using h

end TransposeFollowup
