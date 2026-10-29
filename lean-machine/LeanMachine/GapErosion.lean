import Mathlib.Tactic

/-! Finite area loss when an integer gap is eroded at both ends. -/

namespace LeanMachine.GapErosion

open Finset
open scoped BigOperators

noncomputable section

def remaining (g r : ℕ) : ℕ := g - 1 - 2 * r

theorem loss_le (g r : ℕ) :
    (g : ℝ) ^ 2 - (remaining g r : ℝ) * (remaining g r + 1) ≤
      (4 * r + 1) * g := by
  by_cases h : 1 + 2 * r ≤ g
  · have he : g = remaining g r + 1 + 2 * r := by unfold remaining; omega
    have heR : (g : ℝ) = remaining g r + 1 + 2 * r := by exact_mod_cast he
    nlinarith [sq_nonneg (r : ℝ)]
  · have hz : remaining g r = 0 := by unfold remaining; omega
    have hg : (g : ℝ) ≤ 4 * r + 1 := by exact_mod_cast (by omega : g ≤ 4 * r + 1)
    rw [hz]
    norm_num only [Nat.cast_zero, zero_mul, sub_zero]
    nlinarith [show 0 ≤ (g : ℝ) by positivity]

def pointArea {α : Type*} (I : Finset α) (gap : α → ℕ) (L : ℕ) : ℝ :=
  (∑ a ∈ I, (gap a : ℝ) ^ 2) / (2 * (L : ℝ) ^ 2)

def erodedArea {α : Type*} (I : Finset α) (gap : α → ℕ) (L r : ℕ) : ℝ :=
  (∑ a ∈ I, (remaining (gap a) r : ℝ) * (remaining (gap a) r + 1)) /
    (2 * (L : ℝ) ^ 2)

/-- The loss has no dependence on the number of gaps. -/
theorem area_loss {α : Type*} (I : Finset α) (gap : α → ℕ) {L : ℕ}
    (hL : 0 < L) (hsum : ∑ a ∈ I, gap a = L) (r : ℕ) :
    pointArea I gap L - (2 * r + 1 / 2 : ℝ) / L ≤ erodedArea I gap L r := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsumR : ∑ a ∈ I, (gap a : ℝ) = L := by exact_mod_cast hsum
  have h := sum_le_sum (fun a (_ : a ∈ I) => loss_le (gap a) r)
  rw [sum_sub_distrib, ← mul_sum, hsumR] at h
  unfold pointArea erodedArea
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)).mpr
  field_simp
  nlinarith

/-- Total constant selection weight of all nonempty eroded runs. -/
theorem weight_sum_le_half {α : Type*} (I : Finset α) (gap : α → ℕ) {L : ℕ}
    (hL : 0 < L) (hsum : ∑ a ∈ I, gap a = L) (r : ℕ) :
    (∑ a ∈ I, if remaining (gap a) r = 0 then (0 : ℝ) else
      (remaining (gap a) r + 1) / (2 * L)) ≤ 1 / 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    _ ≤ ∑ a ∈ I, (gap a : ℝ) / (2 * L) := by
      apply sum_le_sum
      intro a _
      split_ifs with hz
      · positivity
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (show remaining (gap a) r + 1 ≤ gap a by unfold remaining at *; omega)
    _ = 1 / 2 := by
      rw [← sum_div]
      have : ∑ a ∈ I, (gap a : ℝ) = L := by exact_mod_cast hsum
      rw [this]
      field_simp

end
end LeanMachine.GapErosion
