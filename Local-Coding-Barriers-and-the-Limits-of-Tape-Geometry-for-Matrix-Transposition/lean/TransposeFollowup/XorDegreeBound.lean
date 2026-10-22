import TransposeFollowup.XorComponentCount
import TransposeFollowup.GraphNearCount
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! An explicit fixed-degree consequence of the recoded-XOR bound. The error
is at most 6 log(max(2,Delta)) P/log n for every n>=2 and every entry width.
This proves the stated one-sided P-O_Delta(P/log n) bound uniformly in b. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

theorem half_log_power_budget (D n : ℕ) (hD : 2 ≤ D) (hn : 0 < n) :
    (Nat.log D n / 2 + 1) * D ^ (Nat.log D n / 2) ≤ n := by
  let k := Nat.log D n / 2
  have hk : k + 1 ≤ D ^ k :=
    (Nat.succ_le_of_lt (show k < 2 ^ k from Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hD k)
  have hexp : 2 * k ≤ Nat.log D n := by dsimp [k]; omega
  calc
    _ ≤ D ^ k * D ^ k := Nat.mul_le_mul_right _ hk
    _ = D ^ (2 * k) := by rw [← pow_add]; congr 1; omega
    _ ≤ D ^ Nat.log D n := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ n := Nat.pow_log_le_self D (Nat.ne_of_gt hn)

theorem log_le_twice_half_log (D n : ℕ) (hD : 2 ≤ D) (hn : 0 < n) :
    Real.log (n : ℝ) ≤ 2 * ((Nat.log D n / 2 : ℕ) + 2 : ℝ) * Real.log (D : ℝ) := by
  have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < D) n
  have hlog := (Real.log_lt_log (by exact_mod_cast hn : 0 < (n : ℝ))
    (by exact_mod_cast hnat : (n : ℝ) < (D : ℝ) ^ (Nat.log D n + 1))).le
  rw [Real.log_pow] at hlog
  have hindex : ((Nat.log D n + 1 : ℕ) : ℝ) ≤ 2 * ((Nat.log D n / 2 : ℕ) + 2 : ℝ) := by
    exact_mod_cast (show Nat.log D n + 1 ≤ 2 * (Nat.log D n / 2 + 2) by omega)
  exact hlog.trans (mul_le_mul_of_nonneg_right hindex (Real.log_natCast_nonneg D))

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

theorem degree_broadcast_bound_scaled (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 0 < n) :
    (Nat.log D n / 2 + 2) * (n * n * b) ≤
      (Nat.log D n / 2 + 2) * B + 3 * (n * n * b) := by
  let k := Nat.log D n / 2
  have hnear : (nearBits (b := b) G (k + 1)).card ≤ b * n * (2 * D ^ k) :=
    card_nearBits_le_of_balls G (k + 1) (2 * D ^ k)
      (nearVertices_card_le_power G D hD hdegree k)
  have hbudget := half_log_power_budget D n hD hn
  change (k + 1) * D ^ k ≤ n at hbudget
  have hterm : (k + 1) * (nearBits (b := b) G (k + 1)).card ≤ 2 * (n * n * b) := by
    calc
      _ ≤ (k + 1) * (b * n * (2 * D ^ k)) := Nat.mul_le_mul_left _ hnear
      _ = (2 * b * n) * ((k + 1) * D ^ k) := by ring
      _ ≤ (2 * b * n) * n := Nat.mul_le_mul_left _ hbudget
      _ = _ := by ring
  have hs := C.broadcast_lower_bound_scaled hc G hG (k + 1)
  change (k + 2) * (n * n * b) ≤ (k + 2) * B + 3 * (n * n * b)
  nlinarith

/-- Explicit fixed-degree theorem. In contrast with a qualitative big-O
statement, this gives a uniform constant and holds for every n>=2 and b>=0. -/
theorem degree_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (D : ℝ) * (n * n * b : ℕ) / Real.log (n : ℝ) := by
  let k := Nat.log D n / 2
  let P : ℝ := (n * n * b : ℕ)
  have hs : ((k : ℝ) + 2) * P ≤ ((k : ℝ) + 2) * B + 3 * P := by
    dsimp [k, P]
    exact_mod_cast C.degree_broadcast_bound_scaled hc G hG D hD hdegree (by omega)
  have hk : 0 < (k : ℝ) + 2 := by positivity
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog := log_le_twice_half_log D n hD (by omega)
  change Real.log (n : ℝ) ≤ 2 * ((k : ℝ) + 2) * Real.log (D : ℝ) at hlog
  have hratio : (3 : ℝ) / ((k : ℝ) + 2) ≤ 6 * Real.log (D : ℝ) / Real.log (n : ℝ) := by
    apply (div_le_div_iff₀ hk hln).mpr
    nlinarith
  have hgap : P - B ≤ 3 * P / ((k : ℝ) + 2) := by
    apply (le_div_iff₀ hk).mpr
    nlinarith
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hbound : P - B ≤ 6 * Real.log (D : ℝ) * P / Real.log (n : ℝ) := by
    calc
      _ ≤ 3 * P / ((k : ℝ) + 2) := hgap
      _ = P * (3 / ((k : ℝ) + 2)) := by ring
      _ ≤ P * (6 * Real.log (D : ℝ) / Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hP
      _ = _ := by ring
  change (B : ℝ) ≥ P - _
  linarith

theorem fixed_degree_broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : C.LocalTo G) (Delta : ℕ)
    (hdegree : ∀ i, G.degree i ≤ Delta) (hn : 2 ≤ n) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      6 * Real.log (max 2 Delta : ℕ) * (n * n * b : ℕ) / Real.log (n : ℝ) :=
  C.degree_broadcast_lower_bound hc G hG (max 2 Delta) (le_max_left _ _)
    (fun i => (hdegree i).trans (le_max_right _ _)) hn

end RecodedXorCode
end TransposeFollowup
