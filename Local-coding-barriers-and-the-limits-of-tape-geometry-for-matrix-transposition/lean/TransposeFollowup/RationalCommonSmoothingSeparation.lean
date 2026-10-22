import TransposeFollowup.RationalWalkIsolation
import TransposeFollowup.FrobeniusClosedRefinement

/-! Freezing one common right-smoothing element cancels the large left
translation in every pairwise comparison. Rational separation therefore
survives without an additive smoothing-scale error. -/
namespace TransposeFollowup.RationalFreePair
open Classical Set RealMobius
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false

theorem frobenius_entry_le_dist (a b : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |a i j - b i j| ≤ dist a b := by
  have hj : (a i j - b i j) ^ 2 ≤ ∑ j : Fin 2, (a i j - b i j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a i j - b i j)) (Finset.mem_univ j)
  have hi : (∑ j : Fin 2, (a i j - b i j) ^ 2) ≤ ∑ i : Fin 2, ∑ j : Fin 2, (a i j - b i j) ^ 2 :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (a i j - b i j))) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mp
  simpa only [sq_abs, frobenius_dist_sq] using hj.trans hi

theorem frobenius_norm_le_of_entryBox {g : RealMobius.Group} {B : ℝ}
    (hg : g ∈ matrixEntryBox B) : ‖(g : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 2 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0 0)
  rw [← dist_zero_right]
  apply (frobenius_dist_le_iff (by positivity)).mpr
  have hs (i j : Fin 2) : g i j ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hg i j)
  simp only [Matrix.zero_apply, sub_zero, Fin.sum_univ_two]
  nlinarith [hs 0 0, hs 0 1, hs 1 0, hs 1 1]

theorem common_smoothing_separated {D : ℕ} (hD : 0 < D)
    {a b u w : RealMobius.Group} (ha : a ∈ denominatorCarrier D)
    (hb : b ∈ denominatorCarrier D) (hne : a ≠ b)
    (hu : u ∈ matrixEntryBox 2)
    (hy : w⁻¹ * a * u ∈ matrixEntryBox 2) :
    1 / (64 * (D : ℝ) ^ 2) ≤
      dist ((w⁻¹ * a * u : RealMobius.Group) : Matrix (Fin 2) (Fin 2) ℝ)
        ((w⁻¹ * b * u : RealMobius.Group) : Matrix (Fin 2) (Fin 2) ℝ) := by
  let y := w⁻¹ * a * u
  let z := w⁻¹ * b * u
  let ι := fun g : RealMobius.Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
  have hne' : a⁻¹ * b ≠ 1 := by
    intro he
    apply hne
    have hh := congrArg (fun q => a * q) he
    simpa using hh.symm
  obtain ⟨i, j, hsep⟩ := denominatorCarrier_separated (Nat.mul_pos hD hD)
    (denominatorCarrier_mul (denominatorCarrier_inv ha) hb) (denominatorCarrier_one (D * D)) hne'
  have he : a⁻¹ * b = u * (y⁻¹ * z) * u⁻¹ := by dsimp only [y, z]; group
  have hid : ι (a⁻¹ * b) - 1 = ((ι u * ι y⁻¹) * (ι z - ι y)) * ι u⁻¹ := by
    rw [he]
    dsimp only [ι]
    simp only [mul_sub, sub_mul, mul_assoc,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one]
  have huN : ‖ι u‖ ≤ 4 := by simpa only [ι, show (2 : ℝ) * 2 = 4 by norm_num] using frobenius_norm_le_of_entryBox hu
  have huiN : ‖ι u⁻¹‖ ≤ 4 := by simpa only [ι, show (2 : ℝ) * 2 = 4 by norm_num] using frobenius_norm_le_of_entryBox (matrixEntryBox_inv hu)
  have hyiN : ‖ι y⁻¹‖ ≤ 4 := by simpa only [ι, y, show (2 : ℝ) * 2 = 4 by norm_num] using frobenius_norm_le_of_entryBox (matrixEntryBox_inv hy)
  have hnorm : ‖ι (a⁻¹ * b) - 1‖ ≤ 64 * dist (ι y) (ι z) := by
    rw [hid]
    calc
      _ ≤ (‖ι u‖ * ‖ι y⁻¹‖) * ‖ι z - ι y‖ * ‖ι u⁻¹‖ := by
        exact (Matrix.frobenius_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right ((Matrix.frobenius_norm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ (4 * 4) * ‖ι z - ι y‖ * 4 := by gcongr
      _ = _ := by rw [← dist_eq_norm, dist_comm]; ring
  have heN : |(a⁻¹ * b) i j - (1 : RealMobius.Group) i j| ≤ ‖ι (a⁻¹ * b) - 1‖ := by
    simpa only [dist_eq_norm, ι, Matrix.SpecialLinearGroup.coe_one] using frobenius_entry_le_dist (ι (a⁻¹ * b)) 1 i j
  have hd : 0 < (D : ℝ) ^ 2 := by positivity
  have hsep' : 1 / (D : ℝ) ^ 2 ≤ 64 * dist (ι y) (ι z) := by
    simpa only [Nat.cast_mul, show (D : ℝ) * D = (D : ℝ) ^ 2 by ring] using hsep.trans (heN.trans hnorm)
  change 1 / (64 * (D : ℝ) ^ 2) ≤ dist (ι y) (ι z)
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := (div_le_iff₀ hd).mp hsep'
  nlinarith only [hh]

end TransposeFollowup.RationalFreePair
