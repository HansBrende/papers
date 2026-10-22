import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Bounds for the canonical numerator and denominator of exact rationals.
These establish operand sizes, independently of any machine cost model. -/

namespace TransposeFollowup

set_option autoImplicit false

def rationalHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

theorem rationalHeight_pos (q : ℚ) : 0 < rationalHeight q :=
  q.den_pos.trans_le (le_max_right _ _)

theorem rationalHeight_le {q : ℚ} {H : ℕ} : rationalHeight q ≤ H ↔
    q.num.natAbs ≤ H ∧ q.den ≤ H := max_le_iff

theorem rationalHeight_divInt_le (a b : ℤ) (H : ℕ)
    (hH : 1 ≤ H) (ha : a.natAbs ≤ H) (hb : b.natAbs ≤ H) :
    rationalHeight (Rat.divInt a b) ≤ H := by
  by_cases hzero : b = 0
  · subst b
    simpa [rationalHeight] using hH
  · obtain ⟨c, hcnum, hcden⟩ := Rat.num_den_mk hzero
      (rfl : Rat.divInt a b = Rat.divInt a b)
    have hc : c ≠ 0 := by intro h; simp [h] at hcden; exact hzero hcden
    have hcpos : 1 ≤ c.natAbs := by
      have := Int.natAbs_pos.mpr hc
      omega
    have hn := congrArg Int.natAbs hcnum
    have hd := congrArg Int.natAbs hcden
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn hd
    apply rationalHeight_le.mpr
    constructor <;> nlinarith

theorem rationalHeight_add_le (q r : ℚ) :
    rationalHeight (q + r) ≤ 2 * rationalHeight q * rationalHeight r := by
  have hq := (rationalHeight_le (q := q) (H := rationalHeight q)).mp le_rfl
  have hr := (rationalHeight_le (q := r) (H := rationalHeight r)).mp le_rfl
  have hqp := rationalHeight_pos q
  have hrp := rationalHeight_pos r
  rw [Rat.add_num_den]
  apply rationalHeight_divInt_le
  · nlinarith
  · have h := Int.natAbs_add_le (q.num * r.den) (q.den * r.num)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
    nlinarith [Nat.mul_le_mul hq.1 hr.2, Nat.mul_le_mul hq.2 hr.1]
  · simp only [Int.natAbs_mul, Int.natAbs_natCast]
    nlinarith [Nat.mul_le_mul hq.2 hr.2]

theorem rationalHeight_mul_le (q r : ℚ) :
    rationalHeight (q * r) ≤ rationalHeight q * rationalHeight r := by
  have hq := (rationalHeight_le (q := q) (H := rationalHeight q)).mp le_rfl
  have hr := (rationalHeight_le (q := r) (H := rationalHeight r)).mp le_rfl
  have he : q * r = Rat.divInt (q.num * r.num) ((q.den : ℤ) * r.den) := by
    rw [← Rat.divInt_mul_divInt, Rat.num_divInt_den, Rat.num_divInt_den]
  rw [he]
  apply rationalHeight_divInt_le
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos (rationalHeight_pos q) (rationalHeight_pos r)))
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

theorem rationalHeight_inv (q : ℚ) : rationalHeight q⁻¹ = rationalHeight q := by
  by_cases hq : q.num = 0
  · have hz : q = 0 := Rat.zero_of_num_zero hq
    simp [hz]
  · simp [rationalHeight, Rat.num_inv, Rat.den_inv, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero hq, hq, max_comm]

theorem rationalHeight_div_le (q r : ℚ) :
    rationalHeight (q / r) ≤ rationalHeight q * rationalHeight r := by
  simpa only [div_eq_mul_inv, rationalHeight_inv] using rationalHeight_mul_le q r⁻¹

theorem rationalHeight_min_le (q r : ℚ) :
    rationalHeight (min q r) ≤ max (rationalHeight q) (rationalHeight r) := by
  rcases le_total q r with h | h
  · rw [min_eq_left h]
    exact le_max_left _ _
  · rw [min_eq_right h]
    exact le_max_right _ _

theorem rationalHeight_max_le (q r : ℚ) :
    rationalHeight (max q r) ≤ max (rationalHeight q) (rationalHeight r) := by
  rcases le_total q r with h | h
  · rw [max_eq_right h]
    exact le_max_right _ _
  · rw [max_eq_left h]
    exact le_max_left _ _

theorem rationalHeight_nat_ratio {a n : ℕ} (ha : a ≤ n) (hn : 0 < n) :
    rationalHeight ((a : ℚ) / n) ≤ n := by
  have h := rationalHeight_divInt_le (a : ℤ) (n : ℤ) n hn ha le_rfl
  simpa only [Rat.divInt_eq_div, Int.cast_natCast] using h

theorem rationalHeight_natCast (n : ℕ) : rationalHeight (n : ℚ) = max n 1 := by
  simp [rationalHeight]

theorem rat_le_rationalHeight (q : ℚ) : q ≤ (rationalHeight q : ℚ) := by
  have hn : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by
    calc
      _ ≤ ((q.num.natAbs : ℤ) : ℚ) := Int.cast_le.mpr Int.le_natAbs
      _ = _ := Int.cast_natCast _
  have hh : (q.num.natAbs : ℚ) ≤ rationalHeight q := by exact_mod_cast (le_max_left q.num.natAbs q.den)
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hp : (0 : ℚ) ≤ rationalHeight q := Nat.cast_nonneg _
  conv_lhs => rw [← Rat.num_div_den q]
  rw [div_le_iff₀ (by exact_mod_cast q.den_pos)]
  nlinarith

theorem natFloor_le_rationalHeight (q : ℚ) : ⌊q⌋₊ ≤ rationalHeight q := by
  have h := Nat.floor_mono (rat_le_rationalHeight q)
  simpa only [Nat.floor_natCast] using h

theorem natSize_le_poly {m C n d : ℕ} (h : m ≤ C * (n + 1) ^ d) :
    m.size ≤ C.size + d * (n + 1).size + 1 := by
  have hp : C * (n + 1) ^ d ≤ 2 ^ (C.size + d * (n + 1).size) := by
    calc
      _ ≤ 2 ^ C.size * (2 ^ (n + 1).size) ^ d :=
        Nat.mul_le_mul (Nat.lt_size_self C).le (Nat.pow_le_pow_left (Nat.lt_size_self (n + 1)).le d)
      _ = _ := by rw [← pow_mul, mul_comm (n + 1).size d, pow_add]
  simpa only [Nat.size_pow] using Nat.size_le_size (h.trans hp)

theorem rationalHeight_bits_le {q : ℚ} {C n d : ℕ}
    (h : rationalHeight q ≤ C * (n + 1) ^ d) :
    q.num.natAbs.size ≤ C.size + d * (n + 1).size + 1 ∧
      q.den.size ≤ C.size + d * (n + 1).size + 1 := by
  have hq := rationalHeight_le.mp h
  exact ⟨natSize_le_poly hq.1, natSize_le_poly hq.2⟩

end TransposeFollowup
