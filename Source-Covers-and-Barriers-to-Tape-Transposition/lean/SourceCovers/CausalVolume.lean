import SourceCovers.CausalRouting

/-! The whole-group volume bound from disjoint collector intervals. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine Finset
open scoped BigOperators Classical
noncomputable section

variable {d b h n : ℕ} {Edge : Type*} [Fintype Edge] (G : Network d b h n Edge)
variable [∀ a : Fin h, Nonempty (G.GroupBit a)]

/-- All collector links, across all groups, occupy distinct memory slots. -/
theorem collectorSpineIndex_joint_injective : Function.Injective
    (fun x : (a : Fin h) × (G.collector a).Link => G.collectorSpineIndex x.1 x.2) := by
  rintro ⟨a, v⟩ ⟨a', v'⟩ he
  have hv : v.val = v'.val := Fin.ext (congrArg (fun x : Fin (n - 1) => x.val) he)
  have ha : a = a' := by
    by_contra ha
    rcases lt_or_gt_of_ne ha with ha | ha
    · have hl := G.lastOutput_le_firstOutput ha
      have hf := v'.property.1
      rw [← hv] at hf
      exact (not_lt_of_ge (hl.trans hf)) v.property.2
    · have hl := G.lastOutput_le_firstOutput ha
      have hf := v.property.1
      rw [hv] at hf
      exact (not_lt_of_ge (hl.trans hf)) v'.property.2
  subst a'
  cases Subtype.ext hv
  rfl

theorem sum_interval_lengths_le :
    ∑ a, ((G.lastOutput a).val - (G.firstOutput a).val) ≤ n - 1 := by
  have hc := Nat.card_le_card_of_injective _ G.collectorSpineIndex_joint_injective
  rw [Nat.card_sigma] at hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, CausalFields.Collector.card_link,
    collector] using hc

/-- Any upper bound on group width gives the stated total-volume estimate.
There is no positivity requirement on that width bound or on the node count. -/
theorem intervalVolume_le (g : ℕ) (hg : ∀ a, Fintype.card (G.GroupColumn a) ≤ g) :
    G.intervalVolume ≤ (∑ e, G.capacity e) + 2 * (g * d * b : ℕ) * (n - 1 : ℕ) := by
  have hcard (a : Fin h) : (Fintype.card (G.GroupBit a) : ℝ) ≤ (g * d * b : ℕ) := by
    have hc : Fintype.card (G.GroupBit a) ≤ g * d * b := by
      rw [G.card_groupBit]
      calc
        _ ≤ d * g * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_left d (hg a))
        _ = _ := by ring
    exact_mod_cast hc
  have hl : (∑ a, (((G.lastOutput a).val - (G.firstOutput a).val : ℕ) : ℝ)) ≤
      (n - 1 : ℕ) := by exact_mod_cast G.sum_interval_lengths_le
  unfold intervalVolume
  rw [mul_assoc]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ ∑ a, (g * d * b : ℕ) * (((G.lastOutput a).val - (G.firstOutput a).val : ℕ) : ℝ) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hcard a) (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)

end
end SourceCovers.CausalGroups.Network
