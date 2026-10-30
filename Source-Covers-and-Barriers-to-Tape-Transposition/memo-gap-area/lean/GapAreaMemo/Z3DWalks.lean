import GapAreaMemo.Z3DHeads
import Mathlib.Analysis.PSeries

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: walks, raw path, outputs and runtime

Four work heads: the bank heads X and Y (staircases), the older exception E
and the newer exception G (scheduled excursions). The raw path sweeps the raw
range `[0, L-1]` at slope `1/s` from time `1`, with `s = ⌊(endC - 1)/L⌋`, so it
reaches the top during bank C and stays there. Outputs are the `L` times
after `OA`.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag

variable (P : Index)

def nX : ℕ := 3 * P.NX
def nY : ℕ := 3 * P.NY

def walkX : ℕ → ℤ := Staircase.walk (fun j => (P.segX j).walk) (fun j => (P.segX j).h) P.startX P.nX
def walkY : ℕ → ℤ := Staircase.walk (fun j => (P.segY j).walk) (fun j => (P.segY j).h) P.startY P.nY

noncomputable def heads : Fin 4 → ℕ → ℤ := fun i =>
  if i.val = 0 then P.walkX
  else if i.val = 1 then P.walkY
  else if i.val = 2 then SourceCovers.NativeExcursion.walk P.eSchedule
  else SourceCovers.NativeExcursion.walk P.gSchedule

theorem heads_isWalk (i : Fin 4) : BoundedNesting.IsWalk (P.heads i) := by
  unfold heads
  split_ifs
  · exact Staircase.isWalk_walk P.validX _
  · exact Staircase.isWalk_walk P.validY _
  · exact SourceCovers.NativeExcursion.isWalk _
  · exact SourceCovers.NativeExcursion.isWalk _

/-- The raw slope. -/
def slope : ℕ := (P.endC - 1) / P.L

theorem L_pos : 0 < P.L := pow_pos (by norm_num) _

theorem endC_ge : 2 * P.L + 1 ≤ P.endC := by
  have h1 := P.U_le_endC (j := 1) P.K_pos
  have h2 : P.U 1 = 1 + fC 1 * P.cc 1 + P.cc 1 := rfl
  have h3 : fC 1 = 1 := by unfold fC; simp
  have h4 : P.cc 1 = 2 * P.L := by unfold cc; rw [← P.a_one]; ring
  omega

theorem slope_pos : 1 ≤ P.slope := by
  unfold slope
  rw [Nat.le_div_iff_mul_le P.L_pos]
  have := P.endC_ge
  omega

/-- The raw path. -/
def raw (t : ℕ) : ℕ := min ((t - 1) / P.slope) (P.L - 1)

theorem raw_lt (t : ℕ) : P.raw t < P.L := by
  unfold raw; have := P.L_pos; omega

theorem raw_step (t : ℕ) : P.raw (t + 1) ≤ P.raw t + 1 ∧ P.raw t ≤ P.raw (t + 1) := by
  unfold raw
  have hs := P.slope_pos
  have h1 : (t + 1 - 1) / P.slope ≤ (t - 1) / P.slope + 1 := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · rw [show t + 1 - 1 = (t - 1) + 1 by omega]
      have h3 : ((t - 1) + 1) / P.slope ≤ ((t - 1) + P.slope) / P.slope :=
        Nat.div_le_div_right (by omega)
      rw [Nat.add_div_right _ (by omega)] at h3
      exact h3
  have h2 : (t - 1) / P.slope ≤ (t + 1 - 1) / P.slope := Nat.div_le_div_right (by omega)
  constructor <;> omega

/-- The output times. -/
def out (z : ℕ) : ℕ := P.OA + 1 + z

theorem out_strictMono : StrictMono P.out := fun i j h => by unfold out; omega

theorem out_lt {z : ℕ} (hz : z < P.L) : P.out z < P.T := by unfold out T; omega

/-! ### Size sums -/

theorem a_mul_sq_le {k : ℕ} (_hk : 1 ≤ k) (hK : k ≤ P.K) : P.a k * (k * k) ≤ P.L := by
  have hlt : k < 2 ^ (lev k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hsq : k * k ≤ 4 ^ (lev k + 1) := by
    have h1 := Nat.mul_lt_mul'' hlt hlt
    have h4 : 2 ^ (lev k + 1) * 2 ^ (lev k + 1) = 4 ^ (lev k + 1) := by
      rw [← mul_pow]; norm_num
    rw [h4] at h1
    exact h1.le
  have he := P.exponent_ok hK
  calc P.a k * (k * k) ≤ P.a k * 4 ^ (lev k + 1) := Nat.mul_le_mul_left _ hsq
    _ = P.L := by
      unfold a L
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega

theorem a_le_div {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ P.K) : (P.a k : ℝ) ≤ P.L * ((k : ℝ) ^ 2)⁻¹ := by
  have h := P.a_mul_sq_le hk hK
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hk0]
  exact_mod_cast (show P.a k * k ^ 2 ≤ P.L by rw [pow_two]; exact h)

/-- Bank heights above an index sum to at most `2 L / (k + 1)`. -/
theorem sumA_le (k : ℕ) : (P.sumA k : ℝ) ≤ 2 * P.L / (k + 1) := by
  unfold sumA
  push_cast
  calc (∑ i ∈ Ioc k P.K, (P.a i : ℝ)) ≤ ∑ i ∈ Ioo k (P.K + 1), P.L * ((i : ℝ) ^ 2)⁻¹ := by
        rw [show Ioo k (P.K + 1) = Ioc k P.K by ext i; simp only [mem_Ioo, mem_Ioc]; omega]
        exact sum_le_sum fun i hi => P.a_le_div (by simp only [mem_Ioc] at hi; omega)
          (by simp only [mem_Ioc] at hi; omega)
    _ = P.L * ∑ i ∈ Ioo k (P.K + 1), ((i : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ P.L * (2 / (k + 1)) := mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le k (P.K + 1))
        (by positivity)
    _ = 2 * P.L / (k + 1) := by ring

theorem hg_le : (P.hg : ℝ) ≤ 4 * P.L := by
  unfold hg; push_cast; have := P.sumA_le 0; simp at this; linarith

end SourceCovers.Z3D.Index
