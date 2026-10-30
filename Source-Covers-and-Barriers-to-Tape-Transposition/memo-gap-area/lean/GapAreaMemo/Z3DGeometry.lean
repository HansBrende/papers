import GapAreaMemo.Z3DColoring
import GapAreaMemo.GapArea

set_option autoImplicit false

/-!
# The dyadic sharpness geometry as an admissible geometry

The geometry carries the trivial computation on a single input with a
one-point record alphabet; the source-cover certificate's credit (the frozen
point area of the exact source bank) depends only on the geometry. The
runtime is at most `128 L`, the core has a two-coloring, all families a
three-coloring, there are two exceptions and no outside families.
-/

namespace SourceCovers.Z3D.Index

open Finset Zigzag Transpose.Tape Transpose.Tape.Impl

variable (P : Index)

theorem fC_le_four (k : ℕ) : fC k ≤ 4 := by
  unfold fC; split_ifs with h
  · omega
  · rcases ratio_cases (k := k - 1) (by omega) with h' | h'
    · rw [h']; omega
    · rw [h']

theorem U_le (j : ℕ) : P.U j ≤ 1 + 5 * ∑ i ∈ Ioc 0 j, P.cc i := by
  induction j with
  | zero => simp [U]
  | succ j ih =>
    show P.U j + fC (j + 1) * P.cc (j + 1) + P.cc (j + 1) ≤ _
    rw [show Ioc 0 (j + 1) = insert (j + 1) (Ioc 0 j) by
      ext i; simp only [mem_Ioc, mem_insert]; omega, sum_insert (by simp)]
    have := Nat.mul_le_mul_right (P.cc (j + 1)) (fC_le_four (j + 1))
    omega

theorem sum_cc : ∑ i ∈ Ioc 0 P.K, P.cc i = 8 * P.sumA 0 := by
  unfold cc sumA; rw [mul_sum]

theorem a_le_a_one (k : ℕ) : P.a k ≤ P.a 1 := by
  unfold a
  apply Nat.pow_le_pow_right (by norm_num)
  unfold lev; simp only [Nat.log_one_right]; omega

theorem runtime_le : (P.T : ℝ) ≤ 128 * (P.d * P.d * P.b : ℕ) := by
  rw [← P.L_eq]
  have hL : (1 : ℝ) ≤ P.L := by exact_mod_cast P.L_pos
  have hs := P.sumA_le 0
  simp only [Nat.cast_zero, zero_add, div_one] at hs
  have hU := P.U_le P.K
  rw [P.sum_cc] at hU
  have hccK : P.cc P.K ≤ 2 * P.L := by
    have := P.a_le_a_one P.K; have := P.a_one; unfold cc; omega
  have hT : P.T = P.U P.K + P.cc P.K + P.cc P.K + P.hg + P.L + P.hg + 3 + P.hg + P.L + 2 := by
    unfold T
    rw [P.OA_eq]
    unfold σA
    rw [P.sumA_K, P.OB_eq, P.σB_K]
    unfold cc
    ring
  have hg := P.hg_le
  have hU' : (P.U P.K : ℝ) ≤ 1 + 40 * P.sumA 0 := by exact_mod_cast (by omega : P.U P.K ≤ 1 + 40 * P.sumA 0)
  have hcc' : (P.cc P.K : ℝ) ≤ 2 * P.L := by exact_mod_cast hccK
  rw [hT]
  push_cast
  linarith

theorem b_pos : 0 < P.b := pow_pos (by norm_num) _
theorem d_pos : 0 < P.d := pow_pos (by norm_num) _

/-- The single input of the trivial computation. -/
def input0 : Fin (P.d * P.d * P.b) → Bool := fun _ => false

/-- **The sharpness geometry** of index `P`, for any record capacity `β ≥ 0`. -/
noncomputable def geometry (β : ℝ) (hβ : 0 ≤ β) : AdmissibleGeometry 128 β 3 2 where
  d := P.d
  b := P.b
  hd := P.d_pos
  hb := P.b_pos
  T := P.T
  k := 4
  xs := P.heads
  work_walk := P.heads_isWalk
  x := P.raw
  raw_range := fun s _ => by rw [← P.L_eq]; exact P.raw_lt s
  raw_step := fun e _ => by
    have h := P.raw_step e
    rw [Real.dist_eq, abs_le]
    constructor
    · have : (P.raw (e + 1) : ℝ) ≤ P.raw e + 1 := by exact_mod_cast h.1
      linarith
    · have : (P.raw e : ℝ) ≤ P.raw (e + 1) := by exact_mod_cast h.2
      linarith
  t := P.out
  append_strict := P.out_strictMono.strictMonoOn _
  append_lt := fun z hz => P.out_lt (by rw [P.L_eq]; exact hz)
  C := {P.input0}
  correct_nonempty := singleton_nonempty _
  Record := Unit
  recordFintype := inferInstance
  record := fun _ _ => ()
  output := fun _ _ => false
  capacity := by simp [hβ]
  locally_determined := fun _ _ _ _ _ _ _ _ => rfl
  correct := fun z hz _ => by
    rw [mem_singleton] at hz; subst hz; rfl
  core := P.core
  core_coloring := P.core_coloring
  full_coloring := P.full_coloring
  exceptions := P.exceptions
  exceptions_card := P.exceptions_card
  exceptions_disjoint := P.core_disjoint
  a0 := 0
  outside_small := P.outside_none
  runtime := by have := P.runtime_le; push_cast at this; exact this

end SourceCovers.Z3D.Index
