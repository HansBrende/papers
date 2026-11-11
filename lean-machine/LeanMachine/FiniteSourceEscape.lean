import LeanMachine.ContextPruning
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-! Normalized counting on a finite source. An exponentially smaller bad
set leaves at least half of the original uniform source; no change of law
or choice of a largest fibre is involved. -/

namespace LeanMachine.FiniteSourceEscape

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

noncomputable def weight (_x : Ω) : ℝ := 1 / Fintype.card Ω

theorem weight_pos [Nonempty Ω] (x : Ω) : 0 < weight x := by
  unfold weight
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem mass_eq_card (E : Finset Ω) :
    ContextPruning.mass weight E = (E.card : ℝ) / Fintype.card Ω := by
  simp [ContextPruning.mass, weight, div_eq_mul_inv]

theorem weight_sum [Nonempty Ω] : (∑ x : Ω, weight x) = 1 := by
  change ContextPruning.mass weight univ = 1
  rw [mass_eq_card, card_univ, div_self]
  exact_mod_cast Fintype.card_ne_zero

theorem half_mass_complement [Nonempty Ω] (E : Finset Ω)
    (hsmall : 2 * (E.card : ℝ) ≤ Fintype.card Ω) :
    1 / 2 ≤ ContextPruning.mass weight Eᶜ := by
  classical
  rw [mass_eq_card]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hsum : (E.card : ℝ) + Eᶜ.card = Fintype.card Ω := by
    exact_mod_cast card_add_card_compl E
  apply (le_div_iff₀ hpos).mpr
  linarith

/-- The source and bad-set exponents differ by at least one bit. -/
theorem twice_bad_le_card (E : Finset Ω) {P η κ : ℝ}
    (hgap : κ + 1 ≤ η * P / 2)
    (hsource : (2 : ℝ) ^ ((1 - η / 2) * P) ≤ Fintype.card Ω)
    (hbad : (E.card : ℝ) ≤ (2 : ℝ) ^ (κ + (1 - η) * P)) :
    2 * (E.card : ℝ) ≤ Fintype.card Ω := by
  calc
    2 * (E.card : ℝ) ≤ 2 * (2 : ℝ) ^ (κ + (1 - η) * P) := by gcongr
    _ = (2 : ℝ) ^ (1 + (κ + (1 - η) * P)) := by
      conv_rhs => rw [Real.rpow_add (by norm_num), Real.rpow_one]
    _ ≤ (2 : ℝ) ^ ((1 - η / 2) * P) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ Fintype.card Ω := hsource

theorem half_mass_complement_of_exponents [Nonempty Ω] (E : Finset Ω) {P η κ : ℝ}
    (hgap : κ + 1 ≤ η * P / 2)
    (hsource : (2 : ℝ) ^ ((1 - η / 2) * P) ≤ Fintype.card Ω)
    (hbad : (E.card : ℝ) ≤ (2 : ℝ) ^ (κ + (1 - η) * P)) :
    1 / 2 ≤ ContextPruning.mass weight Eᶜ :=
  half_mass_complement E (twice_bad_le_card E hgap hsource hbad)

/-- The original source inputs with at most one exception at every reached
time, including the terminal configuration. -/
noncomputable def thin {H : Type*} (stop : Ω → ℕ) (outside : Ω → ℕ → Finset H) : Finset Ω :=
  univ.filter (fun x => ∀ t ≤ stop x, (outside x t).card ≤ 1)

theorem complement_thin_pair {H : Type*} (stop : Ω → ℕ) (outside : Ω → ℕ → Finset H)
    {x : Ω} (hx : x ∈ (thin stop outside)ᶜ) :
    ∃ t ≤ stop x, ∃ J : Finset H, J.card = 2 ∧ J ⊆ outside x t := by
  classical
  have hn : ¬ ∀ t ≤ stop x, (outside x t).card ≤ 1 := by
    simpa only [mem_compl, thin, mem_filter, mem_univ, true_and] using hx
  push Not at hn
  obtain ⟨t, ht, hcard⟩ := hn
  obtain ⟨J, hJ, hsize⟩ := exists_subset_card_eq (by omega : 2 ≤ (outside x t).card)
  exact ⟨t, ht, J, hsize, hJ⟩

/-- Exact passage from the small native thin-source set to simultaneous
escape of two coordinates under the original uniform source law. -/
theorem half_mass_pair_escape [Nonempty Ω] {H : Type*}
    (stop : Ω → ℕ) (outside : Ω → ℕ → Finset H) {P η κ : ℝ}
    (hgap : κ + 1 ≤ η * P / 2)
    (hsource : (2 : ℝ) ^ ((1 - η / 2) * P) ≤ Fintype.card Ω)
    (hbad : ((thin stop outside).card : ℝ) ≤ (2 : ℝ) ^ (κ + (1 - η) * P)) :
    ∃ B : Finset Ω, 1 / 2 ≤ ContextPruning.mass weight B ∧
      ∀ x ∈ B, ∃ t ≤ stop x, ∃ J : Finset H, J.card = 2 ∧ J ⊆ outside x t :=
  ⟨(thin stop outside)ᶜ, half_mass_complement_of_exponents _ hgap hsource hbad,
    fun _ hx => complement_thin_pair stop outside hx⟩

end LeanMachine.FiniteSourceEscape
