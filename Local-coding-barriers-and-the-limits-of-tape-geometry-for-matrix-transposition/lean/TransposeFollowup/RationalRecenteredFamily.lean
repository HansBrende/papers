import TransposeFollowup.FreeBasisRebase
import TransposeFollowup.RationalSquareFamily

/-! Freeness, arithmetic and explicit real nearness after left-dividing
a selected short-word family by one of its members. -/
namespace TransposeFollowup.RationalFreePair
open Classical
set_option autoImplicit false

theorem squareFamily_translated_subfamily_free (n : ℕ) {L : ℕ} (hL : 0 < L)
    (o : Fin L → Bool) {κ : Type*} (j : κ → (Fin L → Bool))
    (hj : Function.Injective j) (hjo : ∀ k, j k ≠ o) :
    Function.Injective (FreeGroup.lift (fun k => (squareFamily n o)⁻¹ * squareFamily n (j k))) :=
  FreeBasisRebase.translated_subfamily_free (squareFamily n) (squareFamily_free n hL) o j hj hjo

theorem realSquareFamily_translated_subfamily_free (n : ℕ) {L : ℕ} (hL : 0 < L)
    (o : Fin L → Bool) {κ : Type*} (j : κ → (Fin L → Bool))
    (hj : Function.Injective j) (hjo : ∀ k, j k ≠ o) :
    Function.Injective (FreeGroup.lift
      (fun k => (realSquareFamily n o)⁻¹ * realSquareFamily n (j k))) :=
  FreeBasisRebase.translated_subfamily_free (realSquareFamily n)
    (realSquareFamily_free n hL) o j hj hjo

theorem translated_squareFamily_hasDenominator (n : ℕ) {L : ℕ} (o f : Fin L → Bool) :
    HasDenominator (seedDenominator n ^ (4 * L)) ((squareFamily n o)⁻¹ * squareFamily n f) := by
  have h := (squareFamily_hasDenominator n o).inv.mul (squareFamily_hasDenominator n f)
  simpa only [← pow_add, show 2 * L + 2 * L = 4 * L by omega] using h

theorem translated_squareFamily_realEmbedding (n : ℕ) {L : ℕ} (o f : Fin L → Bool) :
    realEmbedding ((squareFamily n o)⁻¹ * squareFamily n f) =
      (realSquareFamily n o)⁻¹ * realSquareFamily n f := by
  simp only [map_mul, map_inv, realSquareFamily]

theorem real_inv_mul_entry_error {a b : RealMobius.Group} {N δ : ℝ}
    (ha : ∀ i j, |a⁻¹ i j| ≤ N) (hab : ∀ i j, |b i j - a i j| ≤ δ) :
    ∀ i j, |(a⁻¹ * b) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 2 * N * δ := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (ha 0 0)
  intro i j
  have hi : a⁻¹ i 0 * a 0 j + a⁻¹ i 1 * a 1 j =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    have h := congrArg (fun g : RealMobius.Group => g i j) (inv_mul_cancel a)
    change ((a⁻¹).1 * a.1) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j at h
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using h
  have he : (a⁻¹ * b) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
      a⁻¹ i 0 * (b 0 j - a 0 j) + a⁻¹ i 1 * (b 1 j - a 1 j) := by
    change ((a⁻¹).1 * b.1) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, ← hi]
    ring
  rw [he]
  calc
    _ ≤ |a⁻¹ i 0 * (b 0 j - a 0 j)| + |a⁻¹ i 1 * (b 1 j - a 1 j)| := abs_add_le _ _
    _ = |a⁻¹ i 0| * |b 0 j - a 0 j| + |a⁻¹ i 1| * |b 1 j - a 1 j| := by
      rw [abs_mul, abs_mul]
    _ ≤ N * δ + N * δ := add_le_add
      (mul_le_mul (ha i 0) (hab 0 j) (abs_nonneg _) hN)
      (mul_le_mul (ha i 1) (hab 1 j) (abs_nonneg _) hN)
    _ = _ := by ring

theorem real_inv_mul_distance_sq_le {a b : RealMobius.Group} {N δ : ℝ}
    (ha : ∀ i j, |a⁻¹ i j| ≤ N) (hab : ∀ i j, |b i j - a i j| ≤ δ) :
    RealMobius.mobiusIdentityDistanceSq (a⁻¹ * b) ≤ (4 * N * δ) ^ 2 := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (ha 0 0)
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hab 0 0)
  have hb := fun i j => (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
    (real_inv_mul_entry_error ha hab i j)
  have h00 := hb 0 0
  have h01 := hb 0 1
  have h10 := hb 1 0
  have h11 := hb 1 1
  norm_num only [Matrix.one_apply, Fin.isValue, ite_true, ite_false,
    zero_ne_one, one_ne_zero, sq_abs, sub_zero] at h00 h01 h10 h11
  unfold RealMobius.mobiusIdentityDistanceSq
  nlinarith

theorem real_inv_mul_mem_identityBall {a b : RealMobius.Group} {N δ η : ℝ}
    (ha : ∀ i j, |a⁻¹ i j| ≤ N) (hab : ∀ i j, |b i j - a i j| ≤ δ)
    (hrad : 4 * N * δ < η) : a⁻¹ * b ∈ RealMobius.mobiusIdentityBall η := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (ha 0 0)
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hab 0 0)
  have hz : 0 ≤ 4 * N * δ := by positivity
  exact (real_inv_mul_distance_sq_le ha hab).trans_lt
    ((sq_lt_sq₀ hz (hz.trans hrad.le)).mpr hrad)

theorem realSquareFamily_near_pair_translate (n : ℕ) {L : ℕ} (o f : Fin L → Bool)
    {η : ℝ} (hη : 0 < η)
    (hclose : ∀ i j, |realSquareFamily n f i j - realSquareFamily n o i j| ≤
      η / (8 * (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L))) :
    (realSquareFamily n o)⁻¹ * realSquareFamily n f ∈ RealMobius.mobiusIdentityBall η := by
  have hN : 0 < (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L) := by positivity
  apply real_inv_mul_mem_identityBall (realSquareFamily_inverse_entry_bound n o) hclose
  have he : 4 * (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L) *
      (η / (8 * (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L))) = η / 2 := by
    field_simp
    norm_num
  rw [he]
  linarith

end TransposeFollowup.RationalFreePair
