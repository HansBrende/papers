import TransposeFollowup.PositiveWordSquares
import TransposeFollowup.RationalSeedWords

/-! An explicit exponentially large rational free family with controlled
word length, denominators and matrix entries. Near-identity selection by
packing is a subsequent step. -/
namespace TransposeFollowup.RationalFreePair
open Classical FreeWordFamily
set_option autoImplicit false

def squareFamily (n : ℕ) {L : ℕ} (f : Fin L → Bool) : Group :=
  FreeGroup.lift (seed n) (positiveSquare f)

theorem squareFamily_eq_word (n : ℕ) {L : ℕ} (f : Fin L → Bool) :
    squareFamily n f = ((squareWord f).map (signedSeed n)).prod := by
  rw [squareFamily, positiveSquare_eq_mk, ← seed_word_eq_lift]

theorem squareFamily_free (n : ℕ) {L : ℕ} (hL : 0 < L) :
    Function.Injective (FreeGroup.lift (@squareFamily n L)) := by
  have he : FreeGroup.lift (@squareFamily n L) =
      (FreeGroup.lift (seed n)).comp (FreeGroup.lift (@positiveSquare L)) := by
    ext f
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, squareFamily]
  rw [he]
  exact (seed_free n).comp (positiveSquares_free hL)

theorem squareFamily_injective (n : ℕ) {L : ℕ} (hL : 0 < L) :
    Function.Injective (@squareFamily n L) :=
  (seed_free n).comp (positiveSquare_injective hL)

theorem squareFamily_card (n : ℕ) {L : ℕ} (hL : 0 < L) :
    (Finset.univ.image (@squareFamily n L)).card = 2 ^ L := by
  rw [Finset.card_image_of_injective _ (squareFamily_injective n hL)]
  simp

theorem squareFamily_hasDenominator (n : ℕ) {L : ℕ} (f : Fin L → Bool) :
    HasDenominator (seedDenominator n ^ (2 * L)) (squareFamily n f) := by
  rw [squareFamily_eq_word]
  simpa only [squareWord_length] using seed_word_hasDenominator n (squareWord f)

theorem squareFamily_entry_bound (n : ℕ) {L : ℕ} (f : Fin L → Bool) (i j : Fin 2) :
    |squareFamily n f i j| ≤ (1 + 8 / (baseDenominator n : ℚ)) ^ (2 * L) := by
  rw [squareFamily_eq_word]
  simpa only [squareWord_length] using seed_word_entry_bound n (squareWord f) i j

theorem inverse_entry_bound {g : Group} {B : ℚ}
    (hg : ∀ i j, |g i j| ≤ B) : ∀ i j, |g⁻¹ i j| ≤ B := by
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h00 := hg 0 0
  have h01 := hg 0 1
  have h10 := hg 1 0
  have h11 := hg 1 1
  fin_cases i <;> fin_cases j <;> norm_num <;> assumption

theorem squareFamily_inverse_entry_bound (n : ℕ) {L : ℕ} (f : Fin L → Bool) (i j : Fin 2) :
    |(squareFamily n f)⁻¹ i j| ≤ (1 + 8 / (baseDenominator n : ℚ)) ^ (2 * L) :=
  inverse_entry_bound (squareFamily_entry_bound n f) i j

theorem squareFamily_separated (n : ℕ) {L : ℕ} (hL : 0 < L)
    {f g : Fin L → Bool} (hne : f ≠ g) :
    ∃ i j : Fin 2, 1 / ((seedDenominator n : ℚ) ^ (2 * L)) ≤
      |squareFamily n f i j - squareFamily n g i j| := by
  simpa only [Nat.cast_pow] using (squareFamily_hasDenominator n f).separated
    (pow_pos (seedDenominator_pos n) _) (squareFamily_hasDenominator n g)
      (fun h => hne (squareFamily_injective n hL h))

noncomputable def realSquareFamily (n : ℕ) {L : ℕ} (f : Fin L → Bool) : RealMobius.Group :=
  realEmbedding (squareFamily n f)

theorem realSquareFamily_free (n : ℕ) {L : ℕ} (hL : 0 < L) :
    Function.Injective (FreeGroup.lift (@realSquareFamily n L)) := by
  have he : FreeGroup.lift (@realSquareFamily n L) =
      realEmbedding.comp (FreeGroup.lift (@squareFamily n L)) := by
    ext f
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, realSquareFamily]
  rw [he]
  exact realEmbedding_injective.comp (squareFamily_free n hL)

theorem realSquareFamily_injective (n : ℕ) {L : ℕ} (hL : 0 < L) :
    Function.Injective (@realSquareFamily n L) :=
  realEmbedding_injective.comp (squareFamily_injective n hL)

theorem realSquareFamily_card (n : ℕ) {L : ℕ} (hL : 0 < L) :
    (Finset.univ.image (@realSquareFamily n L)).card = 2 ^ L := by
  rw [Finset.card_image_of_injective _ (realSquareFamily_injective n hL)]
  simp

theorem realSquareFamily_entry_bound (n : ℕ) {L : ℕ} (f : Fin L → Bool) (i j : Fin 2) :
    |realSquareFamily n f i j| ≤ (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (squareFamily_entry_bound n f i j)
  push_cast at h
  exact h

theorem realSquareFamily_inverse_entry_bound (n : ℕ) {L : ℕ} (f : Fin L → Bool) (i j : Fin 2) :
    |(realSquareFamily n f)⁻¹ i j| ≤ (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (squareFamily_inverse_entry_bound n f i j)
  push_cast at h
  change |(realEmbedding (squareFamily n f))⁻¹ i j| ≤ _
  rw [← map_inv]
  exact h

theorem realSquareFamily_separated (n : ℕ) {L : ℕ} (hL : 0 < L)
    {f g : Fin L → Bool} (hne : f ≠ g) :
    ∃ i j : Fin 2, 1 / ((seedDenominator n : ℝ) ^ (2 * L)) ≤
      |realSquareFamily n f i j - realSquareFamily n g i j| := by
  obtain ⟨i, j, he⟩ := squareFamily_separated n hL hne
  refine ⟨i, j, ?_⟩
  have h := (Rat.cast_le (K := ℝ)).mpr he
  push_cast at h
  exact h

end TransposeFollowup.RationalFreePair
