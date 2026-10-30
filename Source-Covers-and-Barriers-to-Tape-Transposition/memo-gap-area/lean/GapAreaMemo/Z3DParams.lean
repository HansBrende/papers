import GapAreaMemo.BankShapes
import GapAreaMemo.Covering

set_option autoImplicit false

/-!
# The dyadic sharpness geometry: parameters

The dimension is `d = 2^m` with `m = 2^ν`, the entry width is `b = m`, and
`L = d² b = 2^n` with `n = 2m + ν`. Zigzag indices `k = 1, …, K`,
`K = 2^(ν+1) - 1`, lie in dyadic blocks `lev k = ⌊log₂ k⌋ ≤ ν`. A zigzag of
banks A and B has height `a k = L / 4^(lev k + 1)`, one of bank C has height
`cc k = 8 a k`. Consecutive heights differ by a factor `1` inside a block and
`4` at a block boundary.
-/

namespace SourceCovers.Z3D

open Finset

/-- The index of a geometry of the sequence. -/
structure Index where
  ν : ℕ
  hν : 3 ≤ ν

namespace Index

variable (P : Index)

def m : ℕ := 2 ^ P.ν
def d : ℕ := 2 ^ P.m
def b : ℕ := P.m
def n : ℕ := 2 * P.m + P.ν
def L : ℕ := 2 ^ P.n
def K : ℕ := 2 ^ (P.ν + 1) - 1

def lev (k : ℕ) : ℕ := Nat.log 2 k

def a (k : ℕ) : ℕ := 2 ^ (P.n - 2 * lev k - 2)
def cc (k : ℕ) : ℕ := 8 * P.a k

theorem m_ge : P.ν + 5 ≤ P.m := by
  have h := P.hν
  unfold m
  have : ∀ j, 3 ≤ j → j + 5 ≤ 2 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih => rw [pow_succ]; omega
  exact this _ h

theorem L_eq : P.L = P.d * P.d * P.b := by
  unfold L n d b m
  rw [pow_add, two_mul, pow_add]

theorem lev_le {k : ℕ} (hk : k ≤ P.K) : lev k ≤ P.ν := by
  unfold lev
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have : k < 2 ^ (P.ν + 1) := by unfold K at hk; have := Nat.one_le_two_pow (n := P.ν + 1); omega
    have := Nat.log_lt_of_lt_pow (by omega) this
    omega

theorem exponent_ok {k : ℕ} (hk : k ≤ P.K) : 2 * lev k + 2 + (P.ν + 1) ≤ P.n := by
  have h1 := P.lev_le hk
  have h2 := P.m_ge
  unfold n
  omega

theorem a_pos (k : ℕ) : 0 < P.a k := pow_pos (by norm_num) _

theorem cc_pos (k : ℕ) : 0 < P.cc k := by unfold cc; have := P.a_pos k; omega

theorem lev_succ_le {k : ℕ} (hk : 1 ≤ k) : lev (k + 1) ≤ lev k + 1 := by
  unfold lev
  have h1 : k + 1 < 2 ^ (Nat.log 2 k + 2) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) k
    rw [pow_succ] at this ⊢
    rw [pow_succ]
    omega
  have := Nat.log_lt_of_lt_pow (by omega) h1
  omega

theorem lev_mono {i j : ℕ} (hij : i ≤ j) : lev i ≤ lev j := Nat.log_mono_right hij

/-- The ratio of consecutive heights: `1` inside a block, `4` at a block boundary. -/
def ratio (k : ℕ) : ℕ := 4 ^ (lev (k + 1) - lev k)

theorem ratio_cases {k : ℕ} (hk : 1 ≤ k) : ratio k = 1 ∨ ratio k = 4 := by
  unfold ratio
  have h1 := lev_succ_le hk
  have h2 := lev_mono (show k ≤ k + 1 by omega)
  rcases Nat.lt_or_ge (lev (k + 1)) (lev k + 1) with h | h
  · left; rw [show lev (k + 1) - lev k = 0 by omega]; simp
  · right; rw [show lev (k + 1) - lev k = 1 by omega]; simp

theorem ratio_pos (k : ℕ) : 0 < ratio k := pow_pos (by norm_num) _

theorem a_succ {k : ℕ} (hk : 1 ≤ k) (hK : k + 1 ≤ P.K) :
    P.a k = ratio k * P.a (k + 1) := by
  have he := P.exponent_ok hK
  have h1 := lev_succ_le hk
  have h2 := lev_mono (show k ≤ k + 1 by omega)
  unfold a ratio
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem cc_succ {k : ℕ} (hk : 1 ≤ k) (hK : k + 1 ≤ P.K) :
    P.cc k = ratio k * P.cc (k + 1) := by
  unfold cc; rw [P.a_succ hk hK]; ring

theorem a_le_four_mul {k : ℕ} (hk : 1 ≤ k) (hK : k + 1 ≤ P.K) : P.a k ≤ 4 * P.a (k + 1) := by
  rw [P.a_succ hk hK]
  rcases ratio_cases hk with h | h
  · rw [h]; omega
  · rw [h]

theorem a_one : 4 * P.a 1 = P.L := by
  unfold a L lev
  simp only [Nat.log_one_right, mul_zero, Nat.sub_zero]
  have : 2 ≤ P.n := by have := P.m_ge; unfold n; omega
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

theorem K_pos : 1 ≤ P.K := by
  unfold K
  have : 2 ≤ 2 ^ (P.ν + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (P.ν + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem K_odd : P.K % 2 = 1 := by
  unfold K
  have : 2 ^ (P.ν + 1) % 2 = 0 := by rw [pow_succ]; simp
  have hpos : 1 ≤ 2 ^ (P.ν + 1) := Nat.one_le_two_pow
  omega

end Index
end SourceCovers.Z3D
