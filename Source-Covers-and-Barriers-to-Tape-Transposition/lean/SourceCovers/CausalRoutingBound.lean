import SourceCovers.CausalDistance
import SourceCovers.CausalVolume

/-! Theorem Q: actual partial routing, its entropy and metric bounds, and
the resulting helper/deficit inequality. The original interval budget is
derived from the sharper prefix budget. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine TransposeFollowup Finset
open scoped BigOperators Classical
noncomputable section

universe u v
variable {d b h n : ℕ} {Edge : Type u} [Fintype Edge] (G : Network d b h n Edge)
variable [∀ a : Fin h, Nonempty (G.GroupBit a)]
variable {Helper : Type v} (C : Set (Input d b)) (Z : Input d b → Helper)

/-- The complete routing statement with exact prefix charges. The law may
have zero weights on the declared domain; on its exact support the mass
is precisely the paper's `R_sup`. -/
theorem causal_group_routing_sharp (htyp : G.CausalGroupTyping C Z)
    (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∃ R : FiniteWeightedFamily.{u, v} G.BitRoute,
      G.IsPartialRouting R ∧ R.mass = G.supportRoutingMass C Z p ∧
      (∀ e, G.routingLoad R e ≤ G.augmentedCapacity e) ∧
      G.conditionalGroupEntropy C Z p ≤ R.mass ∧
      (∀ g : ℕ, (∀ a, Fintype.card (G.GroupColumn a) ≤ g) →
        G.intervalVolume ≤ (∑ e, G.capacity e) + 2 * (g * d * b : ℕ) * (n - 1 : ℕ)) ∧
      ∀ ℓ : ℕ, 0 < ℓ →
        R.mass ≤ (G.shortBits ℓ).card + (∑ e, G.augmentedCapacity e) / ℓ ∧
        (d * d * b : ℕ) + G.groupTotalCorrelation C Z p - (G.shortBits ℓ).card -
            (∑ e, G.augmentedCapacity e) / ℓ ≤
          (d * d * b : ℕ) - entropy p / Real.log 2 +
            observationEntropy p (helperValue C Z) / Real.log 2 := by
  obtain ⟨R, hR, hm, hK⟩ := G.exists_averaged_routing C Z htyp p hp hp1
  have he : G.conditionalGroupEntropy C Z p ≤ R.mass :=
    (G.conditionalGroupEntropy_le_supportRoutingMass C Z p hp).trans_eq hm.symm
  refine ⟨R, hR, hm, hK, he, G.intervalVolume_le, ?_⟩
  intro ℓ hℓ
  have hb := G.routingMass_le_short_add_capacity hR G.augmentedCapacity hK ℓ hℓ
  refine ⟨hb, ?_⟩
  have hh := G.deficit_add_helper_ge_of_groupEntropy_le C Z p (d * d * b : ℕ)
    _ (he.trans hb)
  linarith

/-- Theorem Q as stated, obtained directly from the sharper theorem. Group
nonemptiness is supplied by `groupBit_nonempty` when the entry width is positive. -/
theorem causal_group_routing (htyp : G.CausalGroupTyping C Z)
    (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∃ R : FiniteWeightedFamily.{u, v} G.BitRoute,
      G.IsPartialRouting R ∧ R.mass = G.supportRoutingMass C Z p ∧
      (∀ e, G.routingLoad R e ≤ G.intervalCapacity e) ∧
      G.conditionalGroupEntropy C Z p ≤ R.mass ∧
      (∀ g : ℕ, (∀ a, Fintype.card (G.GroupColumn a) ≤ g) →
        G.intervalVolume ≤ (∑ e, G.capacity e) + 2 * (g * d * b : ℕ) * (n - 1 : ℕ)) ∧
      ∀ ℓ : ℕ, 0 < ℓ →
        R.mass ≤ (G.shortBits ℓ).card + G.intervalVolume / ℓ ∧
        (d * d * b : ℕ) + G.groupTotalCorrelation C Z p - (G.shortBits ℓ).card -
            G.intervalVolume / ℓ ≤
          (d * d * b : ℕ) - entropy p / Real.log 2 +
            observationEntropy p (helperValue C Z) / Real.log 2 := by
  obtain ⟨R, hR, hm, hK, he, hV, hbound⟩ := G.causal_group_routing_sharp C Z htyp p hp hp1
  refine ⟨R, hR, hm, fun e => (hK e).trans (G.augmentedCapacity_le_interval e), he, hV, ?_⟩
  intro ℓ hℓ
  obtain ⟨hb, hh⟩ := hbound ℓ hℓ
  have hv := div_le_div_of_nonneg_right G.sum_augmentedCapacity_le_intervalVolume
    (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
  exact ⟨hb.trans (add_le_add le_rfl hv), by linarith⟩

end
end SourceCovers.CausalGroups.Network
