import AdaptiveTransfer.LocalGeometry
import AdaptiveTransfer.FragmentMenuCount
import Mathlib.Data.Nat.Choose.Sum

/-! The complete finite localized cut menu, including the actual cut set and
its full native step payloads. Grouping literal bounded cut sets by size gives
exactly the manuscript's sum of localized geometry menus. -/

namespace AdaptiveTransfer
open Transpose MergeDepth Finset
open scoped BigOperators

abbrev TotalLocalFragmentRecord (M : TM) (P T N r : ℕ) :=
  Σ B : boundedCuts T r, LocalFragmentRecord M P T N B.val

theorem localGeometrySize_factor (k P T N s : ℕ) :
    localGeometryMenuSize k P T N s = T.choose s * localFragmentGeometrySize k P T N s := by
  unfold localGeometryMenuSize localFragmentGeometrySize
  ring

theorem totalLocalFragmentRecord_card (M : TM) (P T N r : ℕ) :
    Fintype.card (TotalLocalFragmentRecord M P T N r) =
      ∑ s ∈ range (min r T + 1), localGeometryMenuSize M.k P T N s * Fintype.card (Value M) ^ s := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [localFragmentRecord_card]
  rw [sum_coe_sort (boundedCuts T r)
    (fun B : Finset ℕ => localFragmentGeometrySize M.k P T N B.card * Fintype.card (Value M) ^ B.card)]
  unfold boundedCuts
  rw [sum_filter]
  rw [sum_powerset_apply_card (fun s => if s ≤ r then
    localFragmentGeometrySize M.k P T N s * Fintype.card (Value M) ^ s else 0)]
  simp only [card_range, nsmul_eq_mul, mul_ite, mul_zero]
  rw [← sum_filter]
  have hf : (range (T + 1)).filter (fun s => s ≤ r) = range (min r T + 1) := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [hf]
  apply sum_congr rfl
  intro s _hs
  rw [localGeometrySize_factor]
  simp only [Nat.cast_id]
  ring

theorem totalLocalFragmentRecord_card_le (M : TM) (P T N r q a : ℕ)
    (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    Fintype.card (TotalLocalFragmentRecord M P T N r) ≤
      ∑ s ∈ range (min r T + 1), localGeometryMenuSize M.k P T N s * 2 ^ ((q + M.k * a + 2) * s) := by
  rw [totalLocalFragmentRecord_card]
  apply sum_le_sum
  intro s _hs
  apply Nat.mul_le_mul_left
  rw [pow_mul]
  exact Nat.pow_le_pow_left (payload_card_le M q a hq ha) s

end AdaptiveTransfer
