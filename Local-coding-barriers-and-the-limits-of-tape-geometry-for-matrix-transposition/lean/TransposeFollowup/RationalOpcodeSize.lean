import TransposeFollowup.RationalNeighbors
import TransposeFollowup.RationalHeight

/-! Size bounds for rational overlap and neighbor generation. Fixed rational
coefficients give polynomial magnitudes and logarithmic binary operand sizes.
This does not yet supply a native arithmetic implementation or a time bound. -/

namespace TransposeFollowup

set_option autoImplicit false

theorem rationalHeight_linearForm {a b x : ℚ} {C H : ℕ}
    (ha : rationalHeight a ≤ C) (hb : rationalHeight b ≤ C)
    (hx : rationalHeight x ≤ H) :
    rationalHeight (a * x + b) ≤ 2 * C ^ 2 * H := by
  have hm := (rationalHeight_mul_le a x).trans (Nat.mul_le_mul ha hx)
  calc
    _ ≤ 2 * rationalHeight (a * x) * rationalHeight b := rationalHeight_add_le _ _
    _ ≤ 2 * (C * H) * C := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) hb
    _ = _ := by ring

namespace RationalMobius

variable (F : RationalMobius)

def arithmeticConstant : ℕ := 1 + rationalHeight F.a + rationalHeight F.b +
  rationalHeight F.c + rationalHeight F.d + rationalHeight F.lo + rationalHeight F.hi

theorem arithmeticConstant_pos : 0 < F.arithmeticConstant := by
  dsimp [arithmeticConstant]
  omega

theorem coefficient_heights : rationalHeight F.a ≤ F.arithmeticConstant ∧
    rationalHeight F.b ≤ F.arithmeticConstant ∧ rationalHeight F.c ≤ F.arithmeticConstant ∧
    rationalHeight F.d ≤ F.arithmeticConstant ∧ rationalHeight F.lo ≤ F.arithmeticConstant ∧
    rationalHeight F.hi ≤ F.arithmeticConstant := by
  dsimp [arithmeticConstant]
  omega

theorem evalQ_height_le {x : ℚ} {H : ℕ} (hx : rationalHeight x ≤ H) :
    rationalHeight (F.evalQ x) ≤ 4 * F.arithmeticConstant ^ 4 * H ^ 2 := by
  obtain ⟨ha, hb, hc, hd, _, _⟩ := F.coefficient_heights
  have hn := rationalHeight_linearForm ha hb hx
  have hden := rationalHeight_linearForm hc hd hx
  calc
    _ ≤ rationalHeight (F.a * x + F.b) * rationalHeight (F.c * x + F.d) :=
      rationalHeight_div_le _ _
    _ ≤ (2 * F.arithmeticConstant ^ 2 * H) * (2 * F.arithmeticConstant ^ 2 * H) :=
      Nat.mul_le_mul hn hden
    _ = _ := by ring

theorem sourceLeft_height_le {n : ℕ} (i : Fin n) :
    rationalHeight (F.sourceLeft i) ≤ F.arithmeticConstant * (n + 1) := by
  have hn : 0 < n := by have := i.isLt; omega
  have hg := rationalHeight_nat_ratio i.isLt.le hn
  have hlo := F.coefficient_heights.2.2.2.2.1
  apply (rationalHeight_max_le _ _).trans
  apply max_le
  · exact hlo.trans (Nat.le_mul_of_pos_right _ (by omega))
  · exact hg.trans (by have := Nat.le_mul_of_pos_left (n + 1) F.arithmeticConstant_pos; omega)

theorem sourceRight_height_le {n : ℕ} (i : Fin n) :
    rationalHeight (F.sourceRight i) ≤ F.arithmeticConstant * (n + 1) := by
  have hn : 0 < n := by have := i.isLt; omega
  have hg : rationalHeight (((i.val : ℚ) + 1) / n) ≤ n := by
    simpa only [Nat.cast_succ] using
      rationalHeight_nat_ratio (Nat.succ_le_of_lt i.isLt) hn
  have hhi := F.coefficient_heights.2.2.2.2.2
  apply (rationalHeight_min_le _ _).trans
  apply max_le
  · exact hhi.trans (Nat.le_mul_of_pos_right _ (by omega))
  · exact hg.trans (by have := Nat.le_mul_of_pos_left (n + 1) F.arithmeticConstant_pos; omega)

theorem evalQ_sourceLeft_height_le {n : ℕ} (i : Fin n) :
    rationalHeight (F.evalQ (F.sourceLeft i)) ≤ 4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 2 := by
  convert F.evalQ_height_le (F.sourceLeft_height_le i) using 1
  ring

theorem evalQ_sourceRight_height_le {n : ℕ} (i : Fin n) :
    rationalHeight (F.evalQ (F.sourceRight i)) ≤ 4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 2 := by
  convert F.evalQ_height_le (F.sourceRight_height_le i) using 1
  ring

theorem neighborStart_argument_height_le {n : ℕ} (i : Fin n) :
    rationalHeight ((n : ℚ) * F.evalQ (F.sourceLeft i)) ≤
      4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 3 := by
  have hn : rationalHeight (n : ℚ) ≤ n + 1 := by rw [rationalHeight_natCast]; omega
  calc
    _ ≤ rationalHeight (n : ℚ) * rationalHeight (F.evalQ (F.sourceLeft i)) :=
      rationalHeight_mul_le _ _
    _ ≤ (n + 1) * (4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 2) :=
      Nat.mul_le_mul hn (F.evalQ_sourceLeft_height_le i)
    _ = _ := by ring

theorem neighborStart_le {n : ℕ} (i : Fin n) :
    F.neighborStart i ≤ 4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 3 :=
  (natFloor_le_rationalHeight _).trans (F.neighborStart_argument_height_le i)

theorem neighborEndpoint_le {n : ℕ} (i : Fin n) :
    F.neighborStart i + F.distortion + 1 ≤
      (4 * F.arithmeticConstant ^ 6 + F.distortion + 1) * (n + 1) ^ 3 := by
  have hs := F.neighborStart_le i
  have hn := Nat.one_le_pow 3 (n + 1) (by omega)
  nlinarith

theorem neighborEndpoint_bits_le {n : ℕ} (i : Fin n) :
    (F.neighborStart i + F.distortion + 1).size ≤
      (4 * F.arithmeticConstant ^ 6 + F.distortion + 1).size + 3 * (n + 1).size + 1 :=
  natSize_le_poly (F.neighborEndpoint_le i)

theorem overlapComparison_height_le {n : ℕ} (i j : Fin n) :
    rationalHeight (max (F.evalQ (F.sourceLeft i)) ((j.val : ℚ) / n)) ≤
        4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 2 ∧
    rationalHeight (min (F.evalQ (F.sourceRight i)) (((j.val : ℚ) + 1) / n)) ≤
        4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 2 := by
  have hn : 0 < n := by have := i.isLt; omega
  have hgL := rationalHeight_nat_ratio j.isLt.le hn
  have hgR : rationalHeight (((j.val : ℚ) + 1) / n) ≤ n := by
    simpa only [Nat.cast_succ] using rationalHeight_nat_ratio (Nat.succ_le_of_lt j.isLt) hn
  have hpoly : n ≤ 4 * F.arithmeticConstant ^ 6 * (n + 1) ^ 2 := by
    have h1 := Nat.le_self_pow (by decide : 2 ≠ 0) (n + 1)
    have h2 := Nat.le_mul_of_pos_left ((n + 1) ^ 2)
      (show 0 < 4 * F.arithmeticConstant ^ 6 by have := F.arithmeticConstant_pos; positivity)
    omega
  exact ⟨(rationalHeight_max_le _ _).trans
      (max_le (F.evalQ_sourceLeft_height_le i) (hgL.trans hpoly)),
    (rationalHeight_min_le _ _).trans
      (max_le (F.evalQ_sourceRight_height_le i) (hgR.trans hpoly))⟩

theorem evalQ_sourceLeft_bits_le {n : ℕ} (i : Fin n) :
    (F.evalQ (F.sourceLeft i)).num.natAbs.size ≤
      (4 * F.arithmeticConstant ^ 6).size + 2 * (n + 1).size + 1 ∧
    (F.evalQ (F.sourceLeft i)).den.size ≤
      (4 * F.arithmeticConstant ^ 6).size + 2 * (n + 1).size + 1 :=
  rationalHeight_bits_le (F.evalQ_sourceLeft_height_le i)

theorem evalQ_sourceRight_bits_le {n : ℕ} (i : Fin n) :
    (F.evalQ (F.sourceRight i)).num.natAbs.size ≤
      (4 * F.arithmeticConstant ^ 6).size + 2 * (n + 1).size + 1 ∧
    (F.evalQ (F.sourceRight i)).den.size ≤
      (4 * F.arithmeticConstant ^ 6).size + 2 * (n + 1).size + 1 :=
  rationalHeight_bits_le (F.evalQ_sourceRight_height_le i)

end RationalMobius
end TransposeFollowup
