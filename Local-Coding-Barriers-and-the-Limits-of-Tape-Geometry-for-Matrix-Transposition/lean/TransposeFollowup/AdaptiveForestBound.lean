import TransposeFollowup.AdaptiveForestLeaf
import TransposeFollowup.AdaptiveBankTranscript

/-! The finite expected-length bound for actual adaptive forest query codes.
The refined fiber inequality and the charged pin overhead are both derived. -/

namespace TransposeFollowup.GapBankCode

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {d b sigma : ℕ} (C : GapBankCode d b sigma)

theorem forest_expected_length
    {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (X : Ω → FiniteMatrix d b) (hc : C.CorrectOn (Set.range X))
    (R M D : ℕ) (hR : 0 < R) (hM : 0 < M) (hd : 0 < d) (hD : 2 ≤ D)
    (hforest : ∀ x, (C.protocol.interactionGraph (C.transcript (X x))).IsAcyclic)
    (hpair : ∀ x, C.protocol.Along (fun S => S.card ≤ 2) (C.transcript (X x)))
    (G : List Bool → SimpleGraph (Fin d))
    (hlocal : ∀ x, C.LeafLocalTo (C.transcript (X x)) (G (C.transcript (X x))))
    (hdegree : ∀ x i, (G (C.transcript (X x))).degree i ≤ D)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : C.bank.StateBudget s) :
    (d*d*b : ℕ) -
      ((d*b*D^(2*R)*(d ⌈/⌉ M + 2*sigma) : ℕ) +
        ((D^R+1)*bucketPatternCount M (D^R) : ℕ)*s) -
      (bucketPatternCount M (D^R) : ℝ) *
        ((d*d*b : ℕ) - observationEntropy p X / Real.log 2) ≤
      (1 + 1 / (R : ℝ)) * ∑ x, p x * (C.transcript (X x)).length := by
  let q := AdaptiveForest.refined C.protocol R hR
  let : DecidableEq q.fullOutputs := Classical.decEq _
  let Y := fun x => C.bank.recode (X x)
  let f := q.outcome
  let Q := bucketPatternCount M (D^R)
  let overhead : ℝ := (d*b*D^(2*R)*(d ⌈/⌉ M + 2*sigma) : ℕ) + ((D^R+1)*Q : ℕ)*s
  have hQ : 1 ≤ (Q : ℝ) := by
    have hK : 0 < D^R := pow_pos (by omega) R
    have hn : Nonempty (BucketPattern M (D^R)) := ⟨⟨{⟨0,hM⟩},
      ⟨Finset.singleton_nonempty _, by simp; omega⟩⟩⟩
    have hi : 0 < Fintype.card (BucketPattern M (D^R)) := Fintype.card_pos
    rw [card_bucketPattern] at hi
    exact_mod_cast hi
  have he : observationEntropy p Y = observationEntropy p X := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    exact C.bank.recode.injective.eq_iff
  have hcard : Real.log (Fintype.card (MatrixBit d b → Bool) : ℝ) =
      (d*d*b : ℕ) * Real.log 2 := by
    rw [← Fintype.card_congr C.bank.recode, card_finiteMatrix]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hav := fullFiber_expected_cost p hp hp1 Y f
    (Subtype.val : q.fullOutputs → List Bool) Subtype.val_injective
    q.outcome_prefixFree overhead Q hQ
  have hleaf : ∀ a, 0 < helperMass p (f ∘ Y) a →
      observationEntropy (helperConditionalWeight p (f ∘ Y) a)
        (fun x : HelperFiber (f ∘ Y) a => Y x) ≤
      overhead * Real.log 2 + ((Q : ℝ) - 1) *
        (Real.log (fiberCard f a : ℝ) - observationEntropy (helperConditionalWeight p (f ∘ Y) a)
          (fun x : HelperFiber (f ∘ Y) a => Y x)) := by
    intro a ha
    have := helperFiber_nonempty_of_mass_pos p (f ∘ Y) a ha
    let z : HelperFiber (f ∘ Y) a := Classical.arbitrary _
    let pp := helperConditionalWeight p (f ∘ Y) a
    have hpp := helperConditionalWeight_nonneg p hp (f ∘ Y) a
    have hpp1 := sum_helperConditionalWeight p (f ∘ Y) a ha.ne'
    have hcf : C.CorrectOn (Set.range (fun x : HelperFiber (f ∘ Y) a => X x)) := by
      intro u hu j
      obtain ⟨x, rfl⟩ := hu
      exact hc (X x) ⟨x.val, rfl⟩ j
    have hm (x : HelperFiber (f ∘ Y) a) : q.run (C.bank.recode (X x)) = q.run (C.bank.recode (X z)) := by
      exact congrArg Subtype.val (x.property.trans z.property.symm)
    have hb := C.forest_leaf_entropy pp hpp hpp1 (fun x : HelperFiber (f ∘ Y) a => X x)
      hcf (X z) R M D hR hM hd hD hm (hforest z)
      (G (C.transcript (X z))) (hlocal z) (hdegree z) hs0 hs
    have hef : observationEntropy pp (fun x : HelperFiber (f ∘ Y) a => Y x) =
        observationEntropy pp (fun x : HelperFiber (f ∘ Y) a => X x) := by
      apply observationEntropy_eq_of_same_fibers pp hpp
      intro x y
      exact C.bank.recode.injective.eq_iff
    have hz : q.run (C.bank.recode (X z)) = a.val := congrArg Subtype.val z.property
    rw [hef, q.outcome_fiberCard a]
    change _ ≤ overhead * Real.log 2 + ((Q:ℝ)-1) *
      (Real.log ((q.fullFiber (q.run (C.bank.recode (X z)))).card : ℝ) - _) at hb
    rwa [hz] at hb
  have hbound := hav hleaf
  rw [hcard, he] at hbound
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hnorm :
      (d*d*b : ℕ) - overhead - (Q : ℝ)*((d*d*b : ℕ) - observationEntropy p X / Real.log 2) ≤
      ∑ x, p x * (q.run (Y x)).length := by
    convert hbound using 1 <;> first | rfl | field_simp
  have hscale (x : Ω) : ((q.run (Y x)).length : ℝ) ≤
      (1 + 1/(R:ℝ)) * (C.transcript (X x)).length := by
    have hn := AdaptiveForest.refined_length_mul_le C.protocol R hR (Y x) (hforest x) (hpair x)
    have hn' : (R:ℝ) * (q.run (Y x)).length ≤ ((R:ℝ)+1) * (C.transcript (X x)).length := by
      exact_mod_cast hn
    have hr : (0:ℝ) < R := by exact_mod_cast hR
    have hh := (le_div_iff₀ hr).mpr (show ((q.run (Y x)).length : ℝ) * R ≤
      ((R:ℝ)+1) * (C.transcript (X x)).length by nlinarith)
    convert hh using 1; field_simp
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) =>
    mul_le_mul_of_nonneg_left (hscale x) (hp x))
  have hrhs : (∑ x, p x * ((1 + 1/(R:ℝ)) * (C.transcript (X x)).length)) =
      (1 + 1/(R:ℝ)) * ∑ x, p x * (C.transcript (X x)).length := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  exact hnorm.trans (hrhs ▸ hsum)

end TransposeFollowup.GapBankCode
