import AdaptiveTransfer.NativeImportInformation

/-! Cardinality estimates applied to the actual native replay classes.
The saving premise is geometric; injectivity is already proved from their
native executions. -/

namespace AdaptiveTransfer
open Transpose Finset NativeRelations LeanMachine
open scoped BigOperators

namespace NativeReplayClass
variable {M : TM} {P : ℕ} {π : Fin P → Fin P} (g : NativeReplayClass M P π)

theorem bits_card_bound (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    g.inputs.card ≤ 2 ^ (P - g.omitted.card + g.ordinaryBits q a) *
      ∑ j ∈ range (g.tags + 1), ((M.k - 1) * g.limit).choose j * (M.g + 1) ^ j := by
  classical
  calc
    g.inputs.card ≤ (Fintype.card g.Exterior * Fintype.card g.Ordinary) * Fintype.card g.Imports := by
      simpa only [Fintype.card_coe, Fintype.card_prod] using
        Fintype.card_le_of_injective _ g.records_injective
    _ ≤ (2 ^ (P - g.omitted.card) * 2 ^ g.ordinaryBits q a) *
        ∑ j ∈ range (g.tags + 1), ((M.k - 1) * g.limit).choose j * (M.g + 1) ^ j := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul g.exterior_card.le (g.ordinary_card_le q a hq ha)
      · exact replayImports_card_le M g.limit g.free g.tags
    _ = _ := by rw [pow_add]

/-- A geometric saving after the actual initial-slab bill bounds a whole
native class. The harmless larger slot set `k*limit` is derived here. -/
theorem saving_card_bound (q a N : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a)
    (hN : (runStarts g.times).card ≤ N) (saving : ℝ)
    (hsaving : saving ≤ (g.omitted.card : ℝ) -
      (a : ℝ) * (if g.start = 0 then 0 else (g.cells.card : ℝ))) :
    (g.inputs.card : ℝ) ≤
      (2 : ℝ) ^ ((P : ℝ) - saving + (N : ℝ) * q +
        (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * g.radius + 1)) *
      ((∑ j ∈ range (min (M.k * g.limit) g.tags + 1),
        (M.k * g.limit).choose j * (M.g + 1) ^ j : ℕ) : ℝ) := by
  have hc : g.omitted.card ≤ P := by
    simpa only [Fintype.card_fin] using card_le_univ g.omitted
  have hbits : ((P - g.omitted.card + g.ordinaryBits q a : ℕ) : ℝ) ≤
      (P : ℝ) - saving + (N : ℝ) * q +
        (a : ℝ) * (M.k - 1 : ℕ) * N * (2 * g.radius + 1) := by
    have hr : ((runStarts g.times).card : ℝ) ≤ N := by exact_mod_cast hN
    have hq' := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg q)
    have ha' := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ (a : ℝ) * (M.k - 1 : ℕ) * (2 * g.radius + 1) by positivity)
    simp only [ordinaryBits, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hc]
    push_cast
    split_ifs at hsaving ⊢ <;> nlinarith
  have hsparse :
      (∑ j ∈ range (g.tags + 1), ((M.k - 1) * g.limit).choose j * (M.g + 1) ^ j) ≤
      ∑ j ∈ range (min (M.k * g.limit) g.tags + 1),
        (M.k * g.limit).choose j * (M.g + 1) ^ j := by
    rw [← sparseMenu_truncate]
    exact sum_le_sum fun j _ => Nat.mul_le_mul_right _
      (Nat.choose_le_choose j (Nat.mul_le_mul_right _ (Nat.sub_le M.k 1)))
  have hh := g.bits_card_bound q a hq ha
  have hh' : (g.inputs.card : ℝ) ≤
      (2 : ℝ) ^ ((P - g.omitted.card + g.ordinaryBits q a : ℕ) : ℝ) *
      ((∑ j ∈ range (g.tags + 1), ((M.k - 1) * g.limit).choose j * (M.g + 1) ^ j : ℕ) : ℝ) := by
    exact_mod_cast hh
  exact hh'.trans (mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits)
    (by exact_mod_cast hsparse) (by positivity) (by positivity))

end NativeReplayClass
end AdaptiveTransfer
