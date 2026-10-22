import TransposeFollowup.UniformEntropy

/-! Fiber counting and conditional Gibbs estimates for adaptive aggregation. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

open Classical in
noncomputable def fiberCard {Ω A : Type*} [Fintype Ω] (f : Ω → A) (a : A) : ℕ :=
  (Finset.univ.filter (fun x => f x = a)).card

theorem pushforward_uniformWeight {Ω A : Type*} [Fintype Ω]
    (f : Ω → A) (a : A) :
    pushforward (uniformWeight Ω) f a = (fiberCard f a : ℝ) / Fintype.card Ω := by
  classical
  unfold pushforward uniformWeight fiberCard
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Gibbs inequality conditioned on a deterministic helper. The comparison
weights need only sum to at most one separately for each helper value. -/
theorem entropy_le_conditional_crossEntropy {A H : Type*}
    [Fintype A] [Fintype H]
    (p q : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (z : A → H)
    (hq1 : ∀ h, pushforward q z h ≤ 1)
    (hsupport : ∀ a, 0 < p a → 0 < q a) :
    entropy p ≤ observationEntropy p z - ∑ a, p a * Real.log (q a) := by
  let ph := pushforward p z
  have hph : ∀ h, 0 ≤ ph h := pushforward_nonneg p hp z
  let r := fun a => ph (z a) * q a
  have hr1 : ∑ a, r a ≤ ∑ a, p a := by
    calc
      _ = ∑ h, pushforward q z h * ph h := by
        rw [sum_pushforward_mul]
        apply Finset.sum_congr rfl
        intro a _
        exact mul_comm _ _
      _ ≤ ∑ h, ph h := by
        apply Finset.sum_le_sum
        intro h _
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hq1 h) (hph h)
      _ = ∑ a, p a := sum_pushforward p z
  have hphpos : ∀ a, 0 < p a → 0 < ph (z a) :=
    fun a ha => lt_of_lt_of_le ha (le_pushforward p hp z a)
  have h := entropy_le_crossEntropy_of_sum_le p r hp
    (fun a => mul_nonneg (hph (z a)) (hq a)) hr1
    (fun a ha => mul_pos (hphpos a ha) (hsupport a ha))
  have hpoint : ∀ a, p a * Real.log (r a) =
      p a * Real.log (ph (z a)) + p a * Real.log (q a) := by
    intro a
    by_cases hz : p a = 0
    · simp [hz]
    · have ha : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
      dsimp only [r]
      rw [Real.log_mul (hphpos a ha).ne' (hsupport a ha).ne', mul_add]
  simp_rw [hpoint] at h
  rw [Finset.sum_add_distrib, ← sum_pushforward_mul p z (fun h => Real.log (ph h))] at h
  change entropy p ≤ entropy ph - _
  simpa only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib,
    neg_add_rev, sub_eq_add_neg, add_comm] using h

/-- Conditional support-size bound for arbitrary nonnegative weights. Fibers
may have different sizes, and zero-probability inputs impose no restrictions. -/
theorem entropy_le_observation_add_mean_log_fiberCard {Ω A : Type*}
    [Fintype Ω] [Fintype A] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (f : Ω → A) :
    entropy p ≤ observationEntropy p f +
      ∑ a, pushforward p f a * Real.log (fiberCard f a : ℝ) := by
  classical
  have hpos (x : Ω) : 0 < (fiberCard f (f x) : ℝ) := by
    apply Nat.cast_pos.mpr
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  have hbudget (a : A) :
      pushforward (fun x : Ω => (fiberCard f (f x) : ℝ)⁻¹) f a ≤ 1 := by
    unfold pushforward
    rw [← Finset.sum_filter]
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x => f x = a), (fiberCard f a : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = (fiberCard f a : ℝ) * (fiberCard f a : ℝ)⁻¹ := by simp [fiberCard]
      _ ≤ 1 := by
        by_cases hz : fiberCard f a = 0
        · simp [hz]
        · rw [mul_inv_cancel₀ (by exact_mod_cast hz : (fiberCard f a : ℝ) ≠ 0)]
  have h := entropy_le_conditional_crossEntropy p
    (fun x => (fiberCard f (f x) : ℝ)⁻¹) hp
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) f hbudget
    (fun x _ => inv_pos.mpr (hpos x))
  rw [sum_pushforward_mul]
  simpa only [Real.log_inv, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add] using h

/-- A deterministic observation loses at most log C entropy when every fiber
contains at most C inputs. This also covers unnormalized nonnegative weights. -/
theorem entropy_le_observation_add_log_fiber_bound {Ω A : Type*}
    [Fintype Ω] [Fintype A] (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : Ω → A) (C : ℝ) (hC : 0 < C)
    (hcap : ∀ a, (fiberCard f a : ℝ) ≤ C) :
    entropy p ≤ observationEntropy p f + (∑ x, p x) * Real.log C := by
  classical
  have hbudget (a : A) : pushforward (fun _ : Ω => C⁻¹) f a ≤ 1 := by
    unfold pushforward
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (fiberCard f a : ℝ) * C⁻¹ ≤ 1
    simpa only [div_eq_mul_inv, one_mul] using
      (div_le_iff₀ hC).mpr (by simpa only [one_mul] using hcap a)
  have h := entropy_le_conditional_crossEntropy p (fun _ : Ω => C⁻¹)
    hp (fun _ => inv_nonneg.mpr hC.le) f hbudget (fun _ _ => inv_pos.mpr hC)
  simpa only [Real.log_inv, mul_neg, Finset.sum_neg_distrib,
    ← Finset.sum_mul, sub_neg_eq_add] using h

end TransposeFollowup
