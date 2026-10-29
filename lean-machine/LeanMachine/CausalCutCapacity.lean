import LeanMachine.CausalFields
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Cardinality and bit-capacity bounds for causal cut observations.
The counted set is the joint raw projection of an arbitrary support. -/

namespace LeanMachine.CausalFields

open Finset
open scoped BigOperators Classical
noncomputable section

/-- Functional recovery bounds the whole image, not just its marginals. -/
theorem card_range_le_of_factorsThrough {Ω A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : Ω → A) (g : Ω → B) (h : Function.FactorsThrough g f) :
    Fintype.card (Set.range g) ≤ Fintype.card A := by
  obtain ⟨decode, hd⟩ := (Function.factorsThrough_iff _).mp h
  rw [hd]
  calc
    _ ≤ Fintype.card (Set.range decode) := Fintype.card_le_of_injective
      (Set.inclusion (Set.range_comp_subset_range f decode)) (Set.inclusion_injective _)
    _ ≤ _ := Fintype.card_range_le decode

namespace Evaluation

variable {Node Edge Bit Input Symbol : Type*} [Fintype Edge] [Fintype Bit]
variable {G : Layout Node Edge Bit} {Field : Edge → Type*} [∀ e, Fintype (Field e)]
variable {C : Set Input} {raw : Input → Bit → Symbol} (E : Evaluation G Field C raw)

include E in
theorem card_raw_range_le [Fintype Symbol] [Nonempty Symbol]
    (U : Set Node) (B : Set Bit)
    (hvisible : ∀ v ∈ U, G.visible v ⊆ B) (houtput : ∀ i, G.output i ∈ U) :
    Fintype.card (Set.range (fun x : C => raw x.val)) ≤
      (∏ e : {e // G.target e ∈ U ∧ G.source e ∉ U}, Fintype.card (Field e.val)) *
        Fintype.card Symbol ^ Fintype.card B := by
  simpa only [Fintype.card_prod, Fintype.card_pi, prod_const, card_univ] using
    card_range_le_of_factorsThrough (E.cutObservation U B) (fun x : C => raw x.val)
      (E.raw_factorsThrough_cut U B hvisible houtput)

/-- Joint support in bits is at most the visible raw-bit count plus the
allocated capacities of all entering edges. No product-support premise. -/
theorem log_support_le_cut [Nonempty C] {raw : Input → Bit → Bool}
    (E : Evaluation G Field C raw) (cost : Edge → ℝ)
    (hcost : ∀ e, (Fintype.card (Field e) : ℝ) ≤ (2 : ℝ) ^ cost e)
    (U : Set Node) (B : Set Bit)
    (hvisible : ∀ v ∈ U, G.visible v ⊆ B) (houtput : ∀ i, G.output i ∈ U) :
    Real.logb 2 (Fintype.card (Set.range (fun x : C => raw x.val))) ≤
      Fintype.card B + ∑ e : {e // G.target e ∈ U ∧ G.source e ∉ U}, cost e.val := by
  have hp : (0 : ℝ) < Fintype.card (Set.range (fun x : C => raw x.val)) := by
    exact_mod_cast Fintype.card_pos
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).mpr
  have hn := E.card_raw_range_le U B hvisible houtput
  have hnR := (Nat.cast_le (α := ℝ)).mpr hn
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, Fintype.card_bool, Nat.cast_ofNat] at hnR
  calc
    _ ≤ (∏ e : {e // G.target e ∈ U ∧ G.source e ∉ U}, (Fintype.card (Field e.val) : ℝ)) *
        2 ^ Fintype.card B := hnR
    _ ≤ (∏ e : {e // G.target e ∈ U ∧ G.source e ∉ U}, (2 : ℝ) ^ cost e.val) *
        2 ^ Fintype.card B := mul_le_mul_of_nonneg_right
          (prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun e _ => hcost e.val)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_comm]

end Evaluation
end
end LeanMachine.CausalFields
