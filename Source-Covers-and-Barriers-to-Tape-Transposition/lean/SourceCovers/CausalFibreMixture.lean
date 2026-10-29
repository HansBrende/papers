import SourceCovers.CausalRouting
import TransposeFollowup.ConditionalEntropyFibers

/-! Mixtures over the actual attained helper values. The helper codomain
need not be finite. Existing finite-weight lemmas supply its probabilities. -/

namespace SourceCovers.CausalGroups.Network

open LeanMachine TransposeFollowup Finset
open scoped BigOperators Classical
noncomputable section

universe u v
variable {d b h n : ℕ} {Edge : Type u} [Fintype Edge] (G : Network d b h n Edge)
variable {Helper : Type v} (C : Set (Input d b)) (Z : Input d b → Helper)

abbrev AttainedHelper := Set.range (fun x : C => Z x.val)

def helperValue (x : C) : AttainedHelper C Z := ⟨Z x.val, ⟨x, rfl⟩⟩

theorem attained_mem_image (z : AttainedHelper C Z) : z.val ∈ Z '' C := by
  obtain ⟨x, hx⟩ := z.property
  exact ⟨x.val, x.property, hx⟩

theorem attained_fibre_nonempty (z : AttainedHelper C Z) : Nonempty (fibre C Z z.val) := by
  obtain ⟨x, hx⟩ := z.property
  exact ⟨⟨x.val, x.property, hx⟩⟩

/-- The entropy library's sample fibre is exactly the original-input fibre. -/
def attainedFibreEquiv (z : AttainedHelper C Z) :
    HelperFiber (helperValue C Z) z ≃ fibre C Z z.val where
  toFun x := ⟨x.val.val, x.val.property, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, Subtype.ext x.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def attainedWeight (p : C → ℝ) (z : AttainedHelper C Z) : ℝ :=
  helperMass p (helperValue C Z) z

theorem attainedWeight_nonneg (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) (z : AttainedHelper C Z) :
    0 ≤ attainedWeight C Z p z := helperMass_nonneg p hp (helperValue C Z) z

theorem sum_attainedWeight (p : C → ℝ) :
    ∑ z : AttainedHelper C Z, attainedWeight C Z p z = ∑ x, p x :=
  sum_helperMass p (helperValue C Z)

/-- If `C` is the law's exact support, every indexed helper value has
positive mass. No condition is imposed on helper values outside that image. -/
theorem attainedWeight_pos (p : C → ℝ) (hp : ∀ x, 0 < p x) (z : AttainedHelper C Z) :
    0 < attainedWeight C Z p z := by
  obtain ⟨x, hx⟩ := z.property
  have he : helperValue C Z x = z := Subtype.ext hx
  have hl := le_pushforward p (fun x => (hp x).le) (helperValue C Z) x
  rw [he] at hl
  exact (hp x).trans_le hl

theorem attainedConditionalWeight_pos (p : C → ℝ) (hp : ∀ x, 0 < p x)
    (z : AttainedHelper C Z) (x : HelperFiber (helperValue C Z) z) :
    0 < helperConditionalWeight p (helperValue C Z) z x :=
  div_pos (hp x.val) (attainedWeight_pos C Z p hp z)

/-- Positivity of the conditional projection law is exactly membership in
the original fibre's projected support. This identifies the support used
by the route construction with the probabilistic support in Theorem Q. -/
theorem conditionalProjection_support (p : C → ℝ) (hp : ∀ x, 0 < p x)
    (z : AttainedHelper C Z) (a : Fin h) (y : G.GroupBit a → Bool) :
    0 < pushforward (helperConditionalWeight p (helperValue C Z) z)
      (fun x : HelperFiber (helperValue C Z) z => G.projection a x.val.val) y ↔
        y ∈ Set.range (fun x : fibre C Z z.val => G.projection a x.val) := by
  constructor
  · intro hpos
    by_contra hn
    have hz : pushforward (helperConditionalWeight p (helperValue C Z) z)
        (fun x : HelperFiber (helperValue C Z) z => G.projection a x.val.val) y = 0 := by
      apply sum_eq_zero
      intro x _
      exact ite_eq_right (fun hx => hn ⟨attainedFibreEquiv C Z z x, hx⟩)
    rw [hz] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨x, rfl⟩
    let x' := (attainedFibreEquiv C Z z).symm x
    have hl := le_pushforward (helperConditionalWeight p (helperValue C Z) z)
      (helperConditionalWeight_nonneg p (fun x => (hp x).le) (helperValue C Z) z)
      (fun x : HelperFiber (helperValue C Z) z => G.projection a x.val.val) x'
    exact (attainedConditionalWeight_pos C Z p hp z x').trans_le hl

/-- Weighted logarithmic projection support on the declared code domain.
For weights strictly positive on `C`, this is exactly the paper's `R_sup`.
Nonnegative weights are also allowed in the more general routing theorem. -/
def supportRoutingMass (p : C → ℝ) : ℝ :=
  ∑ z : AttainedHelper C Z, attainedWeight C Z p z * G.supportSum (fibre C Z z.val)

variable [∀ a : Fin h, Nonempty (G.GroupBit a)]

/-- Combine all groups and average their actual routes over helper values.
The domain may include zero-weight inputs; taking strictly positive weights
on `C` makes every conditional domain its exact probabilistic support. -/
theorem exists_averaged_routing (htyp : G.CausalGroupTyping C Z)
    (p : C → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∃ R : FiniteWeightedFamily.{u, v} G.BitRoute,
      G.IsPartialRouting R ∧ R.mass = G.supportRoutingMass C Z p ∧
      ∀ e, G.routingLoad R e ≤ G.augmentedCapacity e := by
  have hf (z : AttainedHelper C Z) :
      ∃ R : FiniteWeightedFamily.{u, 0} G.BitRoute,
        G.IsPartialRouting R ∧ R.mass = G.supportSum (fibre C Z z.val) ∧
        ∀ e, G.routingLoad R e ≤ G.augmentedCapacity e := by
    let := attained_fibre_nonempty C Z z
    exact (Classical.choice (htyp z.val (attained_mem_image C Z z))).exists_fibre_routing
  choose R hR hm hl using hf
  have hpw := attainedWeight_nonneg C Z p hp
  have hpw1 : ∑ z, attainedWeight C Z p z = 1 := (sum_attainedWeight C Z p).trans hp1
  refine ⟨FiniteWeightedFamily.mix (attainedWeight C Z p) R,
    G.mix_isPartialRouting _ hpw hpw1 R hR, ?_, ?_⟩
  · change (FiniteWeightedFamily.mix (attainedWeight C Z p) R).sum (fun _ => 1) = _
    rw [FiniteWeightedFamily.sum_mix]
    change (∑ z, attainedWeight C Z p z * (R z).mass) = _
    simp only [hm, supportRoutingMass]
  · intro e
    exact FiniteWeightedFamily.sum_mix_le _ hpw hpw1 R _ _ (fun z => hl z e)

end
end SourceCovers.CausalGroups.Network
