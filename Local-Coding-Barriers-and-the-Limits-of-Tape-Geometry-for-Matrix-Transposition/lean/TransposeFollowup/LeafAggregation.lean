import TransposeFollowup.EntropyFibers

/-! Entropy aggregation of the proved leaf inequalities. This is an
intermediate theorem: its two budget hypotheses must be proved from the
actual protocol's disjoint fibers and charged prefix code. -/

namespace TransposeFollowup

open scoped BigOperators
set_option autoImplicit false

/-- Abstract finite aggregation in natural-log units. `charge` will be the
transcript length plus the separator assignment width; `loss` is the exact
internal component count. Helper information is charged twice. -/
theorem aggregate_leaf_bounds_of_distribution {Ω L H : Type*}
    [Fintype Ω] [Fintype L] [Fintype H]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (leaf : Ω → L) (helper : L → H)
    (P : ℕ) (volume charge loss : L → ℕ)
    (hvolpos : ∀ l, 0 < fiberCard leaf l → 0 < volume l)
    (hleaf : ∀ l, 0 < fiberCard leaf l →
      2 * Real.log (fiberCard leaf l : ℝ) ≤
        Real.log (volume l : ℝ) + (loss l : ℝ) * Real.log 2)
    (hvolbudget : ∀ h,
      pushforward (fun l => (volume l : ℝ) / (2 : ℝ) ^ P) helper h ≤ 1)
    (hcodebudget : ∀ h,
      pushforward (fun l => (1 / 2 : ℝ) ^ charge l) helper h ≤ 1) :
    2 * entropy w ≤
      (P : ℝ) * Real.log 2 +
      2 * observationEntropy w (helper ∘ leaf) +
      (∑ l, pushforward w leaf l * ((charge l + loss l : ℕ) : ℝ)) *
        Real.log 2 := by
  classical
  let p := pushforward w leaf
  have hp : ∀ l, 0 ≤ p l := pushforward_nonneg _ hw leaf
  have hp1 : ∑ l, p l = 1 := (sum_pushforward _ leaf).trans hw1
  have hfpos : ∀ l, 0 < p l → 0 < fiberCard leaf l := by
    intro l hl
    by_contra hn
    have hz : Finset.univ.filter (fun x => leaf x = l) = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
    have hzero : p l = 0 := by
      change pushforward w leaf l = 0
      unfold pushforward
      rw [← Finset.sum_filter, hz, Finset.sum_empty]
    exact (ne_of_gt hl) hzero
  have hvpos : ∀ l, 0 < p l → 0 < (volume l : ℝ) := by
    intro l hl
    exact_mod_cast hvolpos l (hfpos l hl)
  have hvol := entropy_le_conditional_crossEntropy p
    (fun l => (volume l : ℝ) / (2 : ℝ) ^ P) hp
    (fun _ => by positivity) helper hvolbudget
    (fun l hl => div_pos (hvpos l hl) (by positivity))
  have hvpoint : ∀ l, p l * Real.log ((volume l : ℝ) / (2 : ℝ) ^ P) =
      p l * Real.log (volume l : ℝ) - p l * ((P : ℝ) * Real.log 2) := by
    intro l
    by_cases hz : p l = 0
    · simp [hz]
    · have hl := lt_of_le_of_ne (hp l) (Ne.symm hz)
      rw [Real.log_div (hvpos l hl).ne' (by positivity), Real.log_pow, mul_sub]
  simp_rw [hvpoint] at hvol
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul] at hvol
  have hcode := entropy_le_conditional_crossEntropy p
    (fun l => (1 / 2 : ℝ) ^ charge l) hp
    (fun _ => by positivity) helper hcodebudget (fun _ _ => by positivity)
  have hcpoint : ∀ l, p l * Real.log ((1 / 2 : ℝ) ^ charge l) =
      -(p l * (charge l : ℝ)) * Real.log 2 := by
    intro l
    rw [Real.log_pow, one_div, Real.log_inv]
    ring
  simp_rw [hcpoint] at hcode
  rw [← Finset.sum_mul, Finset.sum_neg_distrib] at hcode
  have hpoint : ∀ l, p l * (2 * Real.log (fiberCard leaf l : ℝ)) ≤
      p l * (Real.log (volume l : ℝ) + (loss l : ℝ) * Real.log 2) := by
    intro l
    by_cases hz : p l = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (hleaf l (hfpos l (lt_of_le_of_ne (hp l) (Ne.symm hz)))) (hp l)
  have hleafsum : 2 * (∑ l, p l * Real.log (fiberCard leaf l : ℝ)) ≤
      (∑ l, p l * Real.log (volume l : ℝ)) +
        (∑ l, p l * (loss l : ℝ)) * Real.log 2 := by
    calc
      _ = ∑ l, p l * (2 * Real.log (fiberCard leaf l : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ ≤ ∑ l, p l * (Real.log (volume l : ℝ) + (loss l : ℝ) * Real.log 2) :=
        Finset.sum_le_sum (fun l _ => hpoint l)
      _ = _ := by
        simp_rw [mul_add, ← mul_assoc]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hmean := entropy_le_observation_add_mean_log_fiberCard w hw leaf
  change entropy w ≤ entropy p + ∑ l, p l * Real.log (fiberCard leaf l : ℝ) at hmean
  have hhelper : observationEntropy w (helper ∘ leaf) =
      observationEntropy p helper := by
    unfold observationEntropy
    rw [← pushforward_comp]
  rw [hhelper]
  change 2 * entropy w ≤ (P : ℝ) * Real.log 2 +
    2 * observationEntropy p helper +
      (∑ l, p l * ((charge l + loss l : ℕ) : ℝ)) * Real.log 2
  simp_rw [Nat.cast_add, mul_add]
  rw [Finset.sum_add_distrib]
  nlinarith

end TransposeFollowup
