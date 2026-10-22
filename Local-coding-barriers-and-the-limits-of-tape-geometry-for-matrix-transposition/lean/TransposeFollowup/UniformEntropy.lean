import TransposeFollowup.EntropyObservation

/-! Uniform finite families and finite support entropy bounds. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def uniformWeight (Ω : Type*) [Fintype Ω] : Ω → ℝ :=
  fun _ => (Fintype.card Ω : ℝ)⁻¹

theorem uniformWeight_nonneg (Ω : Type*) [Fintype Ω] :
    ∀ x, 0 ≤ uniformWeight Ω x := by intro x; unfold uniformWeight; positivity

theorem sum_uniformWeight (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    ∑ x, uniformWeight Ω x = 1 := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformWeight, hc]

theorem entropy_uniformWeight (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    entropy (uniformWeight Ω) = Real.log (Fintype.card Ω) := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [entropy, uniformWeight, Real.negMulLog, neg_mul, Real.log_inv,
    mul_neg, neg_neg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem observationEntropy_injective {Ω A : Type*}
    [Fintype Ω] [Fintype A] [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (hf : Function.Injective f) :
    observationEntropy p f = entropy p := by
  have : Nonempty A := Nonempty.map f inferInstance
  have h := observationEntropy_eq_of_same_fibers p hp f id
    (fun x y => ⟨fun heq => hf heq, fun heq => congrArg f heq⟩)
  simpa only [observationEntropy_id] using h

/-- The observation can be bounded by any finite set containing its values,
not necessarily the whole ambient alphabet. -/
theorem observationEntropy_le_log_support {Ω A : Type*}
    [Fintype Ω] [Fintype A] [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : Ω → A) (S : Finset A) (hS : ∀ x, f x ∈ S) :
    observationEntropy p f ≤ Real.log (S.card : ℝ) := by
  classical
  let g := fun x => (⟨f x, hS x⟩ : S)
  have : Nonempty S := ⟨g (Classical.arbitrary Ω)⟩
  have : Nonempty A := Nonempty.map f inferInstance
  have heq : observationEntropy p f = observationEntropy p g := by
    apply observationEntropy_eq_of_same_fibers p hp
    intro x y
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [heq]
  have h := entropy_le_log_card (pushforward p g) (pushforward_nonneg p hp g)
    (by rw [sum_pushforward, hp1])
  simpa only [observationEntropy, Fintype.card_coe] using h

end TransposeFollowup
