import TransposeFollowup.IntegerOverlap

/-! Uniform binary size bounds for the unreduced integer overlap predicate.
All constants depend only on the fixed rational map, never on the grid size. -/

namespace TransposeFollowup
namespace RationalMobius

set_option autoImplicit false
variable (F : RationalMobius)

def integerMagnitude : ℕ := 1 + F.integralA.natAbs + F.integralB.natAbs +
  F.integralC.natAbs + F.integralD.natAbs

def integerOperandConstant : ℕ := F.integerMagnitude * F.arithmeticConstant

theorem integerMagnitude_pos : 0 < F.integerMagnitude := by dsimp [integerMagnitude]; omega

theorem integerOperandConstant_pos : 0 < F.integerOperandConstant :=
  Nat.mul_pos F.integerMagnitude_pos F.arithmeticConstant_pos

theorem arithmeticConstant_le_integerOperandConstant :
    F.arithmeticConstant ≤ F.integerOperandConstant :=
  Nat.le_mul_of_pos_left _ F.integerMagnitude_pos

theorem imagePair_bounds {x : ℤ × ℤ} {H : ℕ}
    (hx : x.1.natAbs ≤ H ∧ x.2.natAbs ≤ H) :
    (F.imagePair x).1.natAbs ≤ F.integerMagnitude * H ∧
    (F.imagePair x).2.natAbs ≤ F.integerMagnitude * H := by
  have hn : F.integralA.natAbs + F.integralB.natAbs ≤ F.integerMagnitude := by
    dsimp [integerMagnitude]; omega
  have hd : F.integralC.natAbs + F.integralD.natAbs ≤ F.integerMagnitude := by
    dsimp [integerMagnitude]; omega
  exact ⟨(F.integerNumerator_bound hx.1 hx.2).trans (Nat.mul_le_mul_right H hn),
    (F.integerDenominator_bound hx.1 hx.2).trans (Nat.mul_le_mul_right H hd)⟩

theorem endpointPairs_bounds {n : ℕ} (i : Fin n) :
    (F.leftPair i).1.natAbs ≤ F.integerOperandConstant * (n + 1) ∧
    (F.leftPair i).2.natAbs ≤ F.integerOperandConstant * (n + 1) ∧
    (F.rightPair i).1.natAbs ≤ F.integerOperandConstant * (n + 1) ∧
    (F.rightPair i).2.natAbs ≤ F.integerOperandConstant * (n + 1) := by
  have hl := F.leftPair_bounds i
  have hr := F.rightPair_bounds i
  have h := Nat.mul_le_mul_right (n + 1) F.arithmeticConstant_le_integerOperandConstant
  exact ⟨hl.1.trans h, hl.2.trans h, hr.1.trans h, hr.2.trans h⟩

theorem endpointImagePairs_bounds {n : ℕ} (i : Fin n) :
    (F.imagePair (F.leftPair i)).1.natAbs ≤ F.integerOperandConstant * (n + 1) ∧
    (F.imagePair (F.leftPair i)).2.natAbs ≤ F.integerOperandConstant * (n + 1) ∧
    (F.imagePair (F.rightPair i)).1.natAbs ≤ F.integerOperandConstant * (n + 1) ∧
    (F.imagePair (F.rightPair i)).2.natAbs ≤ F.integerOperandConstant * (n + 1) := by
  have hl := F.imagePair_bounds (F.leftPair_bounds i)
  have hr := F.imagePair_bounds (F.rightPair_bounds i)
  simpa only [integerOperandConstant, Nat.mul_assoc] using ⟨hl.1, hl.2, hr.1, hr.2⟩

theorem evalQ_sourceLeft_height_linear {n : ℕ} (i : Fin n) :
    rationalHeight (F.evalQ (F.sourceLeft i)) ≤ F.integerOperandConstant * (n + 1) := by
  have h := F.endpointImagePairs_bounds i
  have hp : 1 ≤ F.integerOperandConstant * (n + 1) := by
    have := Nat.mul_pos F.integerOperandConstant_pos (show 0 < n + 1 by omega)
    omega
  have hb := rationalHeight_divInt_le _ _ _ hp h.1 h.2.1
  simpa only [Rat.divInt_eq_div, F.leftImagePair_value i] using hb

theorem evalQ_sourceRight_height_linear {n : ℕ} (i : Fin n) :
    rationalHeight (F.evalQ (F.sourceRight i)) ≤ F.integerOperandConstant * (n + 1) := by
  have h := F.endpointImagePairs_bounds i
  have hp : 1 ≤ F.integerOperandConstant * (n + 1) := by
    have := Nat.mul_pos F.integerOperandConstant_pos (show 0 < n + 1 by omega)
    omega
  have hb := rationalHeight_divInt_le _ _ _ hp h.2.2.1 h.2.2.2
  simpa only [Rat.divInt_eq_div, F.rightImagePair_value i] using hb

theorem integerProduct_bits_le {n : ℕ} {a b : ℤ}
    (ha : a.natAbs ≤ F.integerOperandConstant * (n + 1))
    (hb : b.natAbs ≤ F.integerOperandConstant * (n + 1)) :
    (a * b).natAbs.size ≤ (F.integerOperandConstant ^ 2).size + 2 * (n + 1).size + 1 := by
  apply natSize_le_poly
  rw [Int.natAbs_mul]
  calc
    _ ≤ (F.integerOperandConstant * (n + 1)) * (F.integerOperandConstant * (n + 1)) := Nat.mul_le_mul ha hb
    _ = _ := by ring

theorem integerOverlap_cross_bits {n : ℕ} (i j : Fin n) :
    ∀ z ∈ [(F.leftPair i).1 * (F.rightPair i).2, (F.rightPair i).1 * (F.leftPair i).2,
      (F.imagePair (F.leftPair i)).1 * (n : ℤ),
      ((j.val : ℤ) + 1) * (F.imagePair (F.leftPair i)).2,
      (j.val : ℤ) * (F.imagePair (F.rightPair i)).2,
      (F.imagePair (F.rightPair i)).1 * (n : ℤ)],
    z.natAbs.size ≤ (F.integerOperandConstant ^ 2).size + 2 * (n + 1).size + 1 := by
  have h := F.endpointPairs_bounds i
  have hi := F.endpointImagePairs_bounds i
  have hn := Nat.le_mul_of_pos_left (n + 1) F.integerOperandConstant_pos
  have hj := j.isLt
  have hN : (n : ℤ).natAbs ≤ F.integerOperandConstant * (n + 1) := by simp only [Int.natAbs_natCast]; omega
  have hJ : (j.val : ℤ).natAbs ≤ F.integerOperandConstant * (n + 1) := by simp only [Int.natAbs_natCast]; omega
  have hJ1 : ((j.val : ℤ) + 1).natAbs ≤ F.integerOperandConstant * (n + 1) := by omega
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · exact F.integerProduct_bits_le h.1 h.2.2.2
  · exact F.integerProduct_bits_le h.2.2.1 h.2.1
  · exact F.integerProduct_bits_le hi.1 hN
  · exact F.integerProduct_bits_le hJ1 hi.2.1
  · exact F.integerProduct_bits_le hJ hi.2.2.2
  · exact F.integerProduct_bits_le hi.2.2.1 hN

end RationalMobius
end TransposeFollowup
