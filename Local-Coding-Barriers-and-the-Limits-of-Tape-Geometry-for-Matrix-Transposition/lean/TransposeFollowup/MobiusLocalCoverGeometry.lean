import TransposeFollowup.MobiusUnimodular
import TransposeFollowup.RationalRecenteredFamily
import TransposeFollowup.MobiusWalkEntrySupport
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! Explicit Frobenius-radius control for quotients of a bounded set
inside one translated smoothing ball. -/
namespace TransposeFollowup.RealMobius
open Classical Set
open scoped Pointwise
set_option autoImplicit false

theorem mobius_quotient_ball_of_entry_difference {g h : Group} {Q r : ℝ}
    (hQ : 0 < Q) (hh : h ∈ matrixEntryBox Q)
    (hd : ∀ i j : Fin 2, |g i j - h i j| < r) :
    g * h⁻¹ ∈ mobiusIdentityBall (4 * r * Q) := by
  let d := max (max |g 0 0 - h 0 0| |g 0 1 - h 0 1|)
    (max |g 1 0 - h 1 0| |g 1 1 - h 1 1|)
  have hle (i j : Fin 2) : |g i j - h i j| ≤ d := by
    fin_cases i <;> fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hdlt : d < r := max_lt (max_lt (hd 0 0) (hd 0 1)) (max_lt (hd 1 0) (hd 1 1))
  have hi (i j : Fin 2) : |g⁻¹ i j - h⁻¹ i j| ≤ d := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases i <;> fin_cases j
    · exact hle 1 1
    · change |-g 0 1 - -h 0 1| ≤ d
      simpa only [neg_sub_neg, abs_sub_comm] using hle 0 1
    · change |-g 1 0 - -h 1 0| ≤ d
      simpa only [neg_sub_neg, abs_sub_comm] using hle 1 0
    · exact hle 0 0
  have hm := RationalFreePair.real_inv_mul_mem_identityBall
    (a := h⁻¹) (b := g⁻¹) (N := Q) (by intro i j; simpa only [inv_inv] using hh i j) hi
    (show 4 * Q * d < 4 * r * Q by
      simpa only [mul_right_comm 4 Q r] using
        mul_lt_mul_of_pos_left hdlt (by positivity : 0 < 4 * Q))
  rw [← mobiusIdentityBall_inv (4 * r * Q)]
  apply Set.mem_inv.mpr
  simpa only [mul_inv_rev, inv_inv] using hm

theorem local_piece_quotients_in_identityBall {U : Set Group} {z : Group} {Q η : ℝ}
    (hQ : 0 < Q) (hη : 0 < η) (hηone : η ≤ 1) (hU : U ⊆ matrixEntryBox Q)
    (hn : (U ∩ z • mobiusIdentityBall η).Nonempty) :
    (U ∩ z • mobiusIdentityBall η) * (U ∩ z • mobiusIdentityBall η)⁻¹ ⊆
      mobiusIdentityBall (64 * Q ^ 2 * η) := by
  obtain ⟨t, htU, htS⟩ := hn
  obtain ⟨s, hs, he⟩ := Set.mem_smul_set.mp htS
  change z * s = t at he
  have hz : z ∈ matrixEntryBox (4 * Q) := by
    have hb := matrixEntryBox_mul (hU htU)
      (matrixEntryBox_inv (mobiusIdentityBall_subset_entryBox_two hη hηone hs))
    rw [← he, mul_inv_cancel_right] at hb
    simpa only [show 2 * Q * 2 = 4 * Q by ring] using hb
  have herr {b : Group} (hb : b ∈ mobiusIdentityBall η) (i j : Fin 2) :
      |b i j - (1 : Group) i j| < η := by
    obtain ⟨h00, h01, h10, h11⟩ := mobiusIdentityBall_entry_bounds hη hb
    fin_cases i <;> fin_cases j <;> simpa using (by assumption)
  have hdiff {a b : Group} (ha : a ∈ z • mobiusIdentityBall η)
      (hb : b ∈ z • mobiusIdentityBall η) (i j : Fin 2) : |a i j - b i j| < 16 * Q * η := by
    obtain ⟨a', ha', rfl⟩ := Set.mem_smul_set.mp ha
    obtain ⟨b', hb', rfl⟩ := Set.mem_smul_set.mp hb
    have hd (u v : Fin 2) : |a' u v - b' u v| < 2 * η := by
      calc
        _ ≤ |a' u v - (1 : Group) u v| + |b' u v - (1 : Group) u v| := by
          simpa only [abs_sub_comm ((1 : Group) u v) (b' u v)] using
            abs_sub_le (a' u v) ((1 : Group) u v) (b' u v)
        _ < η + η := add_lt_add (herr ha' u v) (herr hb' u v)
        _ = _ := by ring
    have heq : (z * a') i j - (z * b') i j =
        z i 0 * (a' 0 j - b' 0 j) + z i 1 * (a' 1 j - b' 1 j) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    change |(z * a') i j - (z * b') i j| < _
    calc
      _ ≤ |z i 0| * |a' 0 j - b' 0 j| + |z i 1| * |a' 1 j - b' 1 j| := by
        rw [heq]
        simpa only [abs_mul] using abs_add_le
          (z i 0 * (a' 0 j - b' 0 j)) (z i 1 * (a' 1 j - b' 1 j))
      _ ≤ (4 * Q) * |a' 0 j - b' 0 j| + (4 * Q) * |a' 1 j - b' 1 j| := add_le_add
        (mul_le_mul_of_nonneg_right (hz i 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hz i 1) (abs_nonneg _))
      _ < (4 * Q) * (2 * η) + (4 * Q) * (2 * η) := add_lt_add
        (mul_lt_mul_of_pos_left (hd 0 j) (by positivity))
        (mul_lt_mul_of_pos_left (hd 1 j) (by positivity))
      _ = _ := by ring
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
  have hb' : b⁻¹ ∈ U ∩ z • mobiusIdentityBall η := Set.mem_inv.mp hb
  have hq := mobius_quotient_ball_of_entry_difference hQ (hU hb'.1) (hdiff ha.2 hb'.2)
  simpa only [inv_inv, show 4 * (16 * Q * η) * Q = 64 * Q ^ 2 * η by ring] using hq

end TransposeFollowup.RealMobius
