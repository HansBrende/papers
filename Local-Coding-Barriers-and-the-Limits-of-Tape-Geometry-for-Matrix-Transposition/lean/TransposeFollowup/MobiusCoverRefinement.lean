import TransposeFollowup.CoordinateCoverRefinement
import TransposeFollowup.MobiusWalkEntrySupport
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! Offset-bin refinement of translated identity balls into ordinary
Frobenius balls, with representatives inside the target set. -/
namespace TransposeFollowup.RealMobius
open Classical Set
open scoped ENNReal Pointwise
set_option autoImplicit false

theorem mobius_mul_ball_entry_error {f s : Group} {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r)
    (hf : f ∈ matrixEntryBox Q) (hs : s ∈ mobiusIdentityBall r) (i j : Fin 2) :
    |(f * s) i j - f i j| < 2 * Q * r := by
  have herr (u v : Fin 2) : |s u v - (1 : Group) u v| < r := by
    obtain ⟨h00, h01, h10, h11⟩ := mobiusIdentityBall_entry_bounds hr hs
    fin_cases u <;> fin_cases v <;> simpa using (by assumption)
  have hid : f i 0 * (1 : Group) 0 j + f i 1 * (1 : Group) 1 j = f i j := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun g : Group => g i j) (mul_one f)
  have he : (f * s) i j - f i j =
      f i 0 * (s 0 j - (1 : Group) 0 j) + f i 1 * (s 1 j - (1 : Group) 1 j) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← hid]
    ring
  calc
    _ ≤ |f i 0| * |s 0 j - (1 : Group) 0 j| + |f i 1| * |s 1 j - (1 : Group) 1 j| := by
      rw [he]
      simpa only [abs_mul] using abs_add_le
        (f i 0 * (s 0 j - (1 : Group) 0 j)) (f i 1 * (s 1 j - (1 : Group) 1 j))
    _ ≤ Q * |s 0 j - (1 : Group) 0 j| + Q * |s 1 j - (1 : Group) 1 j| := add_le_add
      (mul_le_mul_of_nonneg_right (hf i 0) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (hf i 1) (abs_nonneg _))
    _ < Q * r + Q * r := add_lt_add
      (mul_lt_mul_of_pos_left (herr 0 j) hQ) (mul_lt_mul_of_pos_left (herr 1 j) hQ)
    _ = _ := by ring

theorem exists_frobenius_refinement {A : Set Group} (F : Finset Group) {Q r η : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) (hη : 0 < η) (hF : (F : Set Group) ⊆ matrixEntryBox Q)
    (hcover : A ⊆ (F : Set Group) * mobiusIdentityBall r) :
    ∃ E : Finset Group, (E : Set Group) ⊆ A ∧
      (E.card : ℝ≥0∞) ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal ((16 * Q * r / η + 1) ^ 4) ∧
      ∀ g ∈ A, ∃ e ∈ E, (∀ i j, |g i j - e i j| < η / 4) ∧
        (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2 := by
  have hpatch : ∀ g ∈ A, ∃ f ∈ F, ∀ i j, |g i j - f i j| ≤ 2 * Q * r := by
    intro g hg
    obtain ⟨f, hf, s, hs, rfl⟩ := Set.mem_mul.mp (hcover hg)
    exact ⟨f, hf, fun i j => (mobius_mul_ball_entry_error hQ hr (hF hf) hs i j).le⟩
  obtain ⟨E, hE, hcard, hclose⟩ := BoundedCoordinatePacking.exists_coordinate_refinement
    (fun g : Group => fun i j => g i j) F (by positivity : 0 < η / 4) hpatch
  have hb : (BoundedCoordinatePacking.binCount (2 * Q * r) (η / 4) : ℝ) ≤ 16 * Q * r / η + 1 := by
    calc
      _ ≤ 2 * (2 * Q * r) / (η / 4) + 1 := BoundedCoordinatePacking.binCount_le (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hreal : (E.card : ℝ) ≤ (F.card : ℝ) * (16 * Q * r / η + 1) ^ 4 := by
    calc
      (E.card : ℝ) ≤ (F.card : ℝ) * (BoundedCoordinatePacking.binCount (2 * Q * r) (η / 4) : ℝ) ^ 4 := by
        exact_mod_cast hcard
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hb 4) (Nat.cast_nonneg _)
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg F.card), ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal hreal
  · intro g hg
    obtain ⟨e, he, hge⟩ := hclose g hg
    refine ⟨e, he, hge, ?_⟩
    have hs (i j : Fin 2) : (g i j - e i j) ^ 2 < (η / 4) ^ 2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr (hge i j)
    simp only [Fin.sum_univ_two]
    nlinarith [hs 0 0, hs 0 1, hs 1 0, hs 1 1, sq_nonneg η]

end TransposeFollowup.RealMobius
