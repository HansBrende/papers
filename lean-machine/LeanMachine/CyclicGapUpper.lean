import LeanMachine.CyclicSelection
import LeanMachine.GapErosion
import Mathlib.Algebra.Order.Floor.Div

set_option autoImplicit false

/-! Upper bounds on circular gaps from explicit successor witnesses.
No identification of the sorted enumeration is needed. -/

namespace LeanMachine.CyclicSelection

open Finset
open scoped BigOperators
noncomputable section

theorem gap_le_of_next {L D : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hSL : S ⊆ range L)
    (hnext : ∀ a ∈ S, ∃ b ∈ S, 0 < forward L a b ∧ forward L a b ≤ D)
    {i : ℕ} (hi : i < S.card) : gap L S hS i ≤ D := by
  obtain ⟨b, hb, hpos, hle⟩ := hnext _ (point_mem (L := L) hS hi)
  rcases anchor_offset_zero_or_gap_le hS hSL hi hb with hz | hg
  · omega
  · exact hg.trans hle

theorem pointArea_le_of_gap_le {L D : ℕ} {S : Finset ℕ} (hL : 0 < L)
    (hS : S.Nonempty) (hSL : S ⊆ range L)
    (hgap : ∀ i < S.card, gap L S hS i ≤ D) :
    GapErosion.pointArea (range S.card) (gap L S hS) L ≤ (D : ℝ) / (2 * L) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum : ∑ i ∈ range S.card, (gap L S hS i : ℝ) = L := by
    exact_mod_cast sum_gap hS hSL
  have hb : (∑ i ∈ range S.card, (gap L S hS i : ℝ) ^ 2) ≤ D * (L : ℝ) := by
    calc
      _ ≤ ∑ i ∈ range S.card, D * (gap L S hS i : ℝ) := by
        apply sum_le_sum
        intro i hi
        have he : (gap L S hS i : ℝ) ≤ D := by exact_mod_cast hgap i (mem_range.mp hi)
        have hp : (0 : ℝ) ≤ gap L S hS i := Nat.cast_nonneg _
        nlinarith
      _ = _ := by rw [← mul_sum, hsum]
  unfold GapErosion.pointArea
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)).mpr
  convert hb using 1
  field_simp

end
end LeanMachine.CyclicSelection

namespace LeanMachine

/-- Each increment in a floor grid is at most the ceiling of its mesh. -/
theorem floor_step_le_ceilDiv (L Q j : ℕ) (hQ : 0 < Q) :
    (j + 1) * L / Q ≤ j * L / Q + L ⌈/⌉ Q := by
  have hm := Nat.mod_lt (j * L) hQ
  have he := Nat.mod_add_div (j * L) Q
  have hc : L ≤ Q * (L ⌈/⌉ Q) := le_smul_ceilDiv hQ
  apply Nat.lt_succ_iff.mp
  apply (Nat.div_lt_iff_lt_mul hQ).mpr
  nlinarith

theorem ceilDiv_cast_le_div_add_one (L Q : ℕ) (hQ : 0 < Q) :
    ((L ⌈/⌉ Q : ℕ) : ℝ) ≤ (L : ℝ) / Q + 1 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hn : (L ⌈/⌉ Q) * Q ≤ L + Q :=
    (Nat.div_mul_le_self (L + Q - 1) Q).trans (Nat.sub_le _ _)
  have hr : ((L ⌈/⌉ Q : ℕ) : ℝ) * Q ≤ (L : ℝ) + Q := by exact_mod_cast hn
  calc
    _ ≤ ((L : ℝ) + Q) / Q := (le_div_iff₀ hQR).mpr hr
    _ = _ := by rw [add_div, div_self hQR.ne']

end LeanMachine
