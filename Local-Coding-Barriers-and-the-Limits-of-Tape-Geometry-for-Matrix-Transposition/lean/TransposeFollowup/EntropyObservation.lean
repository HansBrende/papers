import TransposeFollowup.FiniteEntropy

/-! Finite deterministic observations used by the separator proof. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

noncomputable def observationEntropy {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : Ω → ℝ) (f : Ω → A) : ℝ := entropy (pushforward p f)

theorem pushforward_id {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) :
    pushforward p id = p := by
  classical
  funext a
  simp [pushforward]

theorem observationEntropy_id {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) :
    observationEntropy p id = entropy p := by
  rw [observationEntropy, pushforward_id]

theorem observationEntropy_comp_le {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (g : A → B) :
    observationEntropy p (g ∘ f) ≤ observationEntropy p f := by
  unfold observationEntropy
  rw [← pushforward_comp]
  exact entropy_pushforward_le _ (pushforward_nonneg p hp f) g

/-- If one observation determines another, its entropy is at least as large.
This is the interface through which individual decoding is used. -/
theorem observationEntropy_le_of_factorsThrough {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Nonempty B]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (g : Ω → B)
    (h : g.FactorsThrough f) :
    observationEntropy p g ≤ observationEntropy p f := by
  obtain ⟨e, rfl⟩ := (Function.factorsThrough_iff g).mp h
  exact observationEntropy_comp_le p hp f e

theorem observationEntropy_eq_of_same_fibers {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (g : Ω → B)
    (h : ∀ x y, f x = f y ↔ g x = g y) :
    observationEntropy p f = observationEntropy p g := by
  apply le_antisymm
  · exact observationEntropy_le_of_factorsThrough p hp g f (fun x y => (h x y).mpr)
  · exact observationEntropy_le_of_factorsThrough p hp f g (fun x y => (h x y).mp)

theorem observationEntropy_const {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : Ω → ℝ) (a : A) :
    observationEntropy p (fun _ => a) = Real.negMulLog (∑ x, p x) := by
  classical
  unfold observationEntropy entropy pushforward
  have heq : ∀ b, (∑ x, if a = b then p x else 0) =
      if a = b then ∑ x, p x else 0 := by
    intro b
    by_cases h : a = b <;> simp [h]
  simp_rw [heq]
  simp only [apply_ite, Real.negMulLog_zero]
  simp

theorem observationEntropy_pair_of_factorsThrough {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (g : Ω → B)
    (h : g.FactorsThrough f) :
    observationEntropy p (fun x => (g x, f x)) = observationEntropy p f := by
  apply observationEntropy_eq_of_same_fibers p hp
  intro x y
  exact ⟨fun heq => congrArg Prod.snd heq, fun heq => Prod.ext (h heq) heq⟩

theorem pushforward_pair_left {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : C × (A × B) → ℝ) (c : C) (a : A) :
    pushforward p (fun x => (x.1, x.2.1)) (c, a) = ∑ b, p (c, (a, b)) := by
  classical
  simp only [pushforward, Fintype.sum_prod_type, Prod.mk.injEq]
  calc
    _ = ∑ c', if c' = c then ∑ b, p (c', (a, b)) else 0 := by
      apply Finset.sum_congr rfl
      intro c' _
      by_cases hc : c' = c
      · simp only [hc, true_and, ite_true]
        rw [Finset.sum_comm]
        simp
      · simp [hc]
    _ = _ := by simp

theorem pushforward_pair_right {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : C × (A × B) → ℝ) (c : C) (b : B) :
    pushforward p (fun x => (x.1, x.2.2)) (c, b) = ∑ a, p (c, (a, b)) := by
  classical
  simp only [pushforward, Fintype.sum_prod_type, Prod.mk.injEq]
  calc
    _ = ∑ c', if c' = c then ∑ a, p (c', (a, b)) else 0 := by
      apply Finset.sum_congr rfl
      intro c' _
      by_cases hc : c' = c <;> simp [hc]
    _ = _ := by simp

/-- Conditional subadditivity for three arbitrary finite observations. -/
theorem observationEntropy_strong_subadditive {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    observationEntropy p (fun x => (h x, (f x, g x))) + observationEntropy p h ≤
      observationEntropy p (fun x => (h x, f x)) +
      observationEntropy p (fun x => (h x, g x)) := by
  let q := pushforward p (fun x => (h x, (f x, g x)))
  have hq := pushforward_nonneg p hp (fun x => (h x, (f x, g x)))
  have hs := entropy_strong_subadditive q hq
  have hc : (fun c => ∑ ab, q (c, ab)) = pushforward q Prod.fst := by
    funext c
    exact (pushforward_fst q c).symm
  have hca : (fun ca : C × A => ∑ b, q (ca.1, (ca.2, b))) =
      pushforward q (fun x => (x.1, x.2.1)) := by
    funext ca
    exact (pushforward_pair_left q ca.1 ca.2).symm
  have hcb : (fun cb : C × B => ∑ a, q (cb.1, (a, cb.2))) =
      pushforward q (fun x => (x.1, x.2.2)) := by
    funext cb
    exact (pushforward_pair_right q cb.1 cb.2).symm
  rw [hc, hca, hcb] at hs
  simpa only [q, pushforward_comp, Function.comp_def, observationEntropy] using hs

end TransposeFollowup
