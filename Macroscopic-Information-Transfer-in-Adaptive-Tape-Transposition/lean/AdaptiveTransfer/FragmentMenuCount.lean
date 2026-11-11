import AdaptiveTransfer.FragmentGeometry
import Mathlib.Data.Nat.Choose.Sum

/-! The complete finite adaptive cut menu, including the actual cut set and
its full native step payloads. Grouping literal bounded cut sets by size gives
exactly the manuscript's sum of global geometry menus. -/

namespace AdaptiveTransfer
open Transpose MergeDepth Finset
open scoped BigOperators

def boundedCuts (T r : ℕ) : Finset (Finset ℕ) := (range T).powerset.filter fun B => B.card ≤ r

abbrev TotalFragmentRecord (M : TM) (P T r : ℕ) :=
  Σ B : boundedCuts T r, FragmentRecord M P T B.val

theorem globalGeometrySize_factor (k P T s : ℕ) :
    globalGeometryMenuSize k P T s = T.choose s * fragmentGeometrySize k P T s := by
  unfold globalGeometryMenuSize fragmentGeometrySize
  ring

theorem totalFragmentRecord_card (M : TM) (P T r : ℕ) :
    Fintype.card (TotalFragmentRecord M P T r) =
      ∑ s ∈ range (min r T + 1), globalGeometryMenuSize M.k P T s * Fintype.card (Value M) ^ s := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [fragmentRecord_card]
  rw [sum_coe_sort (boundedCuts T r)
    (fun B : Finset ℕ => fragmentGeometrySize M.k P T B.card * Fintype.card (Value M) ^ B.card)]
  unfold boundedCuts
  rw [sum_filter]
  rw [sum_powerset_apply_card (fun s => if s ≤ r then
    fragmentGeometrySize M.k P T s * Fintype.card (Value M) ^ s else 0)]
  simp only [card_range, nsmul_eq_mul, mul_ite, mul_zero]
  rw [← sum_filter]
  have hf : (range (T + 1)).filter (fun s => s ≤ r) = range (min r T + 1) := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [hf]
  apply sum_congr rfl
  intro s _hs
  rw [globalGeometrySize_factor]
  simp only [Nat.cast_id]
  ring

theorem totalFragmentRecord_card_le (M : TM) (P T r q a : ℕ)
    (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    Fintype.card (TotalFragmentRecord M P T r) ≤
      ∑ s ∈ range (min r T + 1), globalGeometryMenuSize M.k P T s * 2 ^ ((q + M.k * a + 2) * s) := by
  rw [totalFragmentRecord_card]
  apply sum_le_sum
  intro s _hs
  apply Nat.mul_le_mul_left
  rw [pow_mul]
  exact Nat.pow_le_pow_left (payload_card_le M q a hq ha) s

end AdaptiveTransfer
