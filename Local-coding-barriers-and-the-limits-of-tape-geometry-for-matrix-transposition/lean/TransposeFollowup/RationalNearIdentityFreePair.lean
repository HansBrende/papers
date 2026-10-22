import TransposeFollowup.RationalFreePair
import TransposeFollowup.MobiusHaarKernel

/-! Explicit rational free pairs arbitrarily close to the real identity.
The integer parameter is chosen once for the seed pair. This does not yet
construct the growing near-identity family required for walk flattening. -/
namespace TransposeFollowup.RationalFreePair
open Classical Set
set_option autoImplicit false

def baseDenominator (n : ℕ) : ℕ := 3 * (n + 1)

def parameter (n : ℕ) : ℚ := (baseDenominator n + 1) / baseDenominator n

theorem baseDenominator_pos (n : ℕ) : 0 < baseDenominator n := by
  unfold baseDenominator
  omega

theorem parameter_pos (n : ℕ) : 0 < parameter n := by
  unfold parameter
  have h : (0 : ℚ) < baseDenominator n := by exact_mod_cast baseDenominator_pos n
  positivity

theorem parameter_padic_large (n : ℕ) : 1 < padicNorm 3 (parameter n) := by
  have hnum : padicNorm 3 ((baseDenominator n : ℚ) + 1) = 1 := by
    have h : padicNorm 3 ((baseDenominator n + 1 : ℕ) : ℚ) = 1 := by
      apply (padicNorm.nat_eq_one_iff _).mpr
      unfold baseDenominator
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hden : padicNorm 3 (baseDenominator n : ℚ) < 1 :=
    (padicNorm.nat_lt_one_iff _).mpr ⟨n + 1, rfl⟩
  have hpos : 0 < padicNorm 3 (baseDenominator n : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (by
      exact_mod_cast (baseDenominator_pos n).ne')))
  rw [parameter, padicNorm.div, hnum, one_div]
  exact (one_lt_inv₀ hpos).mpr hden

def seed (n : ℕ) : Bool → Group := generators (parameter n) (parameter_pos n).ne'

theorem seed_free (n : ℕ) : Function.Injective (FreeGroup.lift (seed n)) :=
  generators_free (parameter_pos n).ne' (parameter_padic_large n)

theorem conjugate_diagonal_matrix (a : ℚ) (ha : a ≠ 0) :
    (conjugator * diagonal a ha * conjugator⁻¹).1 =
      !![2 * a - a⁻¹, -a + a⁻¹; 2 * a - 2 * a⁻¹, -a + 2 * a⁻¹] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  change (!![1, 1; 1, 2] * !![a, 0; 0, a⁻¹]) * !![2, -1; -1, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem generators_entry_error {a : ℚ} (ha : a ≠ 0) (ha1 : 1 ≤ a)
    (k : Bool) (i j : Fin 2) :
    |(generators a ha k) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤ 4 * (a - 1) := by
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha1
  have hi0 : 0 < a⁻¹ := inv_pos.mpr hapos
  have hi1 : a⁻¹ ≤ 1 := (inv_le_one₀ hapos).mpr ha1
  have hilow : 2 - a ≤ a⁻¹ := by
    rw [← one_div, le_div_iff₀ hapos]
    nlinarith [sq_nonneg (a - 1)]
  cases k with
  | false =>
    change |(diagonal a ha).1 i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤ _
    fin_cases i <;> fin_cases j <;> norm_num [diagonal]
    all_goals first | exact ha1 | (apply abs_le.mpr; constructor <;> linarith)
  | true =>
    change |(conjugator * diagonal a ha * conjugator⁻¹).1 i j -
      (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤ _
    rw [conjugate_diagonal_matrix]
    fin_cases i <;> fin_cases j <;> norm_num
    all_goals first | exact ha1 | (apply abs_le.mpr; constructor <;> linarith)

theorem parameter_error (n : ℕ) : parameter n - 1 = 1 / (baseDenominator n : ℚ) := by
  have hn : (baseDenominator n : ℚ) ≠ 0 := by exact_mod_cast (baseDenominator_pos n).ne'
  unfold parameter
  field_simp
  ring

theorem seed_entry_error (n : ℕ) (k : Bool) (i j : Fin 2) :
    |(seed n k) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| ≤
      4 / (baseDenominator n : ℚ) := by
  have hn : (0 : ℚ) < baseDenominator n := by exact_mod_cast baseDenominator_pos n
  have hp : 1 ≤ parameter n := by
    have : 0 < 1 / (baseDenominator n : ℚ) := by positivity
    linarith [parameter_error n]
  simpa only [seed, parameter_error, mul_one_div] using
    generators_entry_error (parameter_pos n).ne' hp k i j

noncomputable def realEmbedding : Group →* RealMobius.Group :=
  Matrix.SpecialLinearGroup.map (Rat.castHom ℝ)

theorem realEmbedding_entry (g : Group) (i j : Fin 2) :
    realEmbedding g i j = (g i j : ℝ) := rfl

theorem realEmbedding_injective : Function.Injective realEmbedding := by
  intro g h he
  apply Subtype.ext
  ext i j
  have hv := congrArg (fun g : RealMobius.Group => g i j) he
  change (g i j : ℝ) = (h i j : ℝ) at hv
  exact_mod_cast hv

noncomputable def realSeed (n : ℕ) : Bool → RealMobius.Group := fun k => realEmbedding (seed n k)

theorem realSeed_free (n : ℕ) : Function.Injective (FreeGroup.lift (realSeed n)) := by
  have he : FreeGroup.lift (realSeed n) = realEmbedding.comp (FreeGroup.lift (seed n)) := by
    ext k
    simp [realSeed]
  rw [he]
  exact realEmbedding_injective.comp (seed_free n)

theorem realSeed_entry_error (n : ℕ) (k : Bool) (i j : Fin 2) :
    |(realSeed n k) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤
      4 / (baseDenominator n : ℝ) := by
  have he : (|(seed n k) i j - (1 : Matrix (Fin 2) (Fin 2) ℚ) i j| : ℝ) ≤
      ((4 / (baseDenominator n : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast seed_entry_error n k i j
  push_cast at he
  change |((seed n k) i j : ℝ) - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ _
  fin_cases i <;> fin_cases j <;> norm_num at he ⊢ <;> exact he

theorem realSeed_distance_sq_le (n : ℕ) (k : Bool) :
    RealMobius.mobiusIdentityDistanceSq (realSeed n k) ≤
      (8 / (baseDenominator n : ℝ)) ^ 2 := by
  have hn : (0 : ℝ) < baseDenominator n := by exact_mod_cast baseDenominator_pos n
  have hb := fun i j => sq_le_sq₀ (abs_nonneg _) (by positivity)
    |>.mpr (realSeed_entry_error n k i j)
  have h00 := hb 0 0
  have h01 := hb 0 1
  have h10 := hb 1 0
  have h11 := hb 1 1
  norm_num only [Matrix.one_apply, Fin.isValue, ite_true, ite_false,
    zero_ne_one, one_ne_zero, sq_abs, sub_zero] at h00 h01 h10 h11
  unfold RealMobius.mobiusIdentityDistanceSq
  rw [show 8 / (baseDenominator n : ℝ) = 2 * (4 / (baseDenominator n : ℝ)) by ring]
  nlinarith

theorem exists_realSeed_near_identity {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, Function.Injective (FreeGroup.lift (realSeed n)) ∧
      ∀ k, realSeed n k ∈ RealMobius.mobiusIdentityBall η := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < η / 8 by positivity)
  refine ⟨n, realSeed_free n, ?_⟩
  intro k
  have hbase : (0 : ℝ) < baseDenominator n := by exact_mod_cast baseDenominator_pos n
  have hrad : 8 / (baseDenominator n : ℝ) < η := by
    have hn' : (0 : ℝ) < n + 1 := by positivity
    have hq : (n : ℝ) + 1 ≤ baseDenominator n := by
      simp only [baseDenominator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      nlinarith
    have he := one_div_le_one_div_of_le hn' hq
    rw [show 8 / (baseDenominator n : ℝ) = 8 * (1 / (baseDenominator n : ℝ)) by ring]
    linarith
  exact (realSeed_distance_sq_le n k).trans_lt (sq_lt_sq₀ (by positivity) hη.le |>.mpr hrad)

end TransposeFollowup.RationalFreePair
