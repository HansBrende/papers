import TransposeFollowup.IntegerMobius

/-! Compute clipped source endpoints by integer comparisons. The pairs are
unreduced fractions with positive denominators; their values are exactly the
endpoints of the already verified rational overlap test. -/

namespace TransposeFollowup
namespace RationalMobius

set_option autoImplicit false
variable (F : RationalMobius)

def leftPair {n : ℕ} (i : Fin n) : ℤ × ℤ :=
  if F.lo.num * (n : ℤ) ≤ (i.val : ℤ) * F.lo.den then (i.val, n) else (F.lo.num, F.lo.den)

def rightPair {n : ℕ} (i : Fin n) : ℤ × ℤ :=
  if ((i.val : ℤ) + 1) * F.hi.den ≤ F.hi.num * (n : ℤ)
    then ((i.val : ℤ) + 1, n) else (F.hi.num, F.hi.den)

theorem left_compare {n : ℕ} (i : Fin n) :
    F.lo ≤ (i.val : ℚ) / n ↔ F.lo.num * (n : ℤ) ≤ (i.val : ℤ) * F.lo.den := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  conv_lhs => lhs; rw [← F.lo.num_div_den]
  rw [div_le_div_iff₀ (by exact_mod_cast F.lo.den_pos) hn]
  norm_cast

theorem right_compare {n : ℕ} (i : Fin n) :
    ((i.val : ℚ) + 1) / n ≤ F.hi ↔
      ((i.val : ℤ) + 1) * F.hi.den ≤ F.hi.num * (n : ℤ) := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  conv_lhs => rhs; rw [← F.hi.num_div_den]
  rw [div_le_div_iff₀ hn (by exact_mod_cast F.hi.den_pos)]
  norm_cast

theorem leftPair_den_pos {n : ℕ} (i : Fin n) : 0 < (F.leftPair i).2 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  unfold leftPair
  split_ifs
  · exact hn
  · change (0 : ℤ) < F.lo.den
    exact_mod_cast F.lo.den_pos

theorem rightPair_den_pos {n : ℕ} (i : Fin n) : 0 < (F.rightPair i).2 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast (show 0 < n by have := i.isLt; omega)
  unfold rightPair
  split_ifs
  · exact hn
  · change (0 : ℤ) < F.hi.den
    exact_mod_cast F.hi.den_pos

theorem leftPair_value {n : ℕ} (i : Fin n) :
    ((F.leftPair i).1 : ℚ) / (F.leftPair i).2 = F.sourceLeft i := by
  unfold leftPair
  split_ifs with h
  · simpa only [Int.cast_natCast, sourceLeft] using (max_eq_right ((F.left_compare i).mpr h)).symm
  · have hh : (i.val : ℚ) / n ≤ F.lo := (lt_of_not_ge (fun h' => h ((F.left_compare i).mp h'))).le
    simpa only [Int.cast_natCast, Rat.num_div_den, sourceLeft] using (max_eq_left hh).symm

theorem rightPair_value {n : ℕ} (i : Fin n) :
    ((F.rightPair i).1 : ℚ) / (F.rightPair i).2 = F.sourceRight i := by
  unfold rightPair
  split_ifs with h
  · have hh := (F.right_compare i).mpr h
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one, sourceRight] using (min_eq_right hh).symm
  · have hh : F.hi ≤ ((i.val : ℚ) + 1) / n := (lt_of_not_ge (fun h' => h ((F.right_compare i).mp h'))).le
    simpa only [Int.cast_natCast, Rat.num_div_den, sourceRight] using (min_eq_left hh).symm

theorem leftPair_bounds {n : ℕ} (i : Fin n) :
    (F.leftPair i).1.natAbs ≤ F.arithmeticConstant * (n + 1) ∧
    (F.leftPair i).2.natAbs ≤ F.arithmeticConstant * (n + 1) := by
  have hc := F.coefficient_heights.2.2.2.2.1
  have hh := rationalHeight_le.mp hc
  have hC := Nat.le_mul_of_pos_right F.arithmeticConstant (show 0 < n + 1 by omega)
  have hn := Nat.le_mul_of_pos_left (n + 1) F.arithmeticConstant_pos
  have hi := i.isLt
  unfold leftPair
  split_ifs <;> simp only [Int.natAbs_natCast] <;> omega

theorem rightPair_bounds {n : ℕ} (i : Fin n) :
    (F.rightPair i).1.natAbs ≤ F.arithmeticConstant * (n + 1) ∧
    (F.rightPair i).2.natAbs ≤ F.arithmeticConstant * (n + 1) := by
  have hc := F.coefficient_heights.2.2.2.2.2
  have hh := rationalHeight_le.mp hc
  have hC := Nat.le_mul_of_pos_right F.arithmeticConstant (show 0 < n + 1 by omega)
  have hn := Nat.le_mul_of_pos_left (n + 1) F.arithmeticConstant_pos
  have hi := i.isLt
  have hs : ((i.val : ℤ) + 1).natAbs = i.val + 1 := by omega
  unfold rightPair
  split_ifs <;> simp only [hs, Int.natAbs_natCast] <;> omega

def imagePair (x : ℤ × ℤ) : ℤ × ℤ :=
  (F.integerNumerator x.1 x.2, F.integerDenominator x.1 x.2)

theorem leftImagePair_value {n : ℕ} (i : Fin n) :
    ((F.imagePair (F.leftPair i)).1 : ℚ) / (F.imagePair (F.leftPair i)).2 =
      F.evalQ (F.sourceLeft i) := by
  rw [← F.leftPair_value i]
  exact (F.evalQ_fraction_eq _ _ (F.leftPair_den_pos i).ne').symm

theorem rightImagePair_value {n : ℕ} (i : Fin n) :
    ((F.imagePair (F.rightPair i)).1 : ℚ) / (F.imagePair (F.rightPair i)).2 =
      F.evalQ (F.sourceRight i) := by
  rw [← F.rightPair_value i]
  exact (F.evalQ_fraction_eq _ _ (F.rightPair_den_pos i).ne').symm

end RationalMobius
end TransposeFollowup
