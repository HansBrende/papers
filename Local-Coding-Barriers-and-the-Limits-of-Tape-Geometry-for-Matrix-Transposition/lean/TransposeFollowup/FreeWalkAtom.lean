import TransposeFollowup.FreeWalkPotential

/-! Exponential bounds for the exact symmetric free-walk atom recurrence. -/
namespace TransposeFollowup.FreeWalk
open Classical FreeGroup
set_option autoImplicit false

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable def atom : ℕ → FreeGroup α → ℝ
  | 0, x => if x = 1 then 1 else 0
  | n + 1, x => (2 * Fintype.card α : ℝ)⁻¹ *
      ∑ a : α × Bool, atom n ((mk [a])⁻¹ * x)

theorem atom_nonneg (n : ℕ) (x : FreeGroup α) : 0 ≤ atom n x := by
  induction n generalizing x with
  | zero => unfold atom; split_ifs <;> norm_num
  | succ n ih => exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => ih _))

theorem averaged_weight_le {k : ℝ} (hk : 1 ≤ k)
    (hcard : k ^ 2 ≤ 2 * Fintype.card α) (x : FreeGroup α) :
    (2 * Fintype.card α : ℝ)⁻¹ * ∑ a : α × Bool, weight (1 / k) ((mk [a])⁻¹ * x) ≤
      (2 / k) * weight (1 / k) x := by
  have hk0 : 0 < k := by linarith
  have hd : 0 < (2 * Fintype.card α : ℝ) := by nlinarith
  have hd0 : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (by nlinarith)
  have hb := sum_neighbor_weight_le (show 0 < 1 / k by positivity) x
  push_cast at hb
  have hc : (2 * Fintype.card α : ℝ)⁻¹ *
      ((2 * Fintype.card α : ℝ) * (1 / k) + (1 / k)⁻¹) ≤ 2 / k := by
    have hdiv : k ≤ (2 * Fintype.card α : ℝ) / k :=
      (le_div_iff₀ hk0).mpr (by nlinarith)
    calc
      _ = ((2 * Fintype.card α : ℝ) / k + k) / (2 * Fintype.card α : ℝ) := by
        simp only [one_div, inv_inv]
        ring
      _ ≤ ((2 * Fintype.card α : ℝ) / k + (2 * Fintype.card α : ℝ) / k) /
          (2 * Fintype.card α : ℝ) := by gcongr
      _ = _ := by field_simp; ring
  calc
    _ ≤ (2 * Fintype.card α : ℝ)⁻¹ *
        (((2 * Fintype.card α : ℝ) * (1 / k) + (1 / k)⁻¹) * weight (1 / k) x) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((2 * Fintype.card α : ℝ)⁻¹ *
        ((2 * Fintype.card α : ℝ) * (1 / k) + (1 / k)⁻¹)) * weight (1 / k) x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (weight_nonneg (by positivity) x)

theorem atom_le_weighted {k : ℝ} (hk : 1 ≤ k)
    (hcard : k ^ 2 ≤ 2 * Fintype.card α) (n : ℕ) (x : FreeGroup α) :
    atom n x ≤ (2 / k) ^ n * weight (1 / k) x := by
  have hk0 : 0 < k := by linarith
  induction n generalizing x with
  | zero =>
    by_cases hx : x = 1
    · simp [atom, hx, weight_one]
    · simpa only [atom, ite_eq_right hx, pow_zero, one_mul] using
        weight_nonneg (show 0 ≤ 1 / k by positivity) x
  | succ n ih =>
    calc
      _ ≤ (2 * Fintype.card α : ℝ)⁻¹ *
          ∑ a : α × Bool, (2 / k) ^ n * weight (1 / k) ((mk [a])⁻¹ * x) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ih _)) (by positivity)
      _ = (2 / k) ^ n * ((2 * Fintype.card α : ℝ)⁻¹ *
          ∑ a : α × Bool, weight (1 / k) ((mk [a])⁻¹ * x)) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (2 / k) ^ n * ((2 / k) * weight (1 / k) x) :=
        mul_le_mul_of_nonneg_left (averaged_weight_le hk hcard x) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem atom_le {k : ℝ} (hk : 1 ≤ k)
    (hcard : k ^ 2 ≤ 2 * Fintype.card α) (n : ℕ) (x : FreeGroup α) :
    atom n x ≤ (2 / k) ^ n := by
  have hk0 : 0 < k := by linarith
  have hq : 1 / k ≤ 1 := (div_le_one hk0).mpr hk
  exact (atom_le_weighted hk hcard n x).trans
    (mul_le_of_le_one_right (by positivity) (weight_le_one (by positivity) hq x))

end TransposeFollowup.FreeWalk
