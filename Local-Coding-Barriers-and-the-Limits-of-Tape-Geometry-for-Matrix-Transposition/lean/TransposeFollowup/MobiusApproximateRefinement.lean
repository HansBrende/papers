import TransposeFollowup.MobiusCoverRefinement
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! Ordinary-scale covers of an approximate group and its sixth power.
All refinement losses are polynomials in the bounded-entry parameter. -/
namespace TransposeFollowup.RealMobius
open Classical Set
open scoped ENNReal Pointwise
set_option autoImplicit false

theorem matrixEntryBox_set_pow {U : Set Group} {Q : ℝ} (hU : U ⊆ matrixEntryBox Q) (n : ℕ) :
    U ^ n ⊆ matrixEntryBox ((2 * Q) ^ n) := by
  induction n with
  | zero =>
    intro g hg
    have hg1 : g = 1 := by simpa only [pow_zero, Set.mem_one] using hg
    subst g
    simpa only [pow_zero] using one_mem_matrixEntryBox
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
    have hm := matrixEntryBox_mul (ih ha) (hU hb)
    simpa only [pow_succ, show 2 * (2 * Q) ^ n * Q = (2 * Q) ^ n * (2 * Q) by ring] using hm

theorem exists_frobenius_covers_of_approximate_cover {U : Set Group} (Y F : Finset Group)
    {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 < η) (hU : U ⊆ matrixEntryBox Q)
    (hY : (Y : Set Group) ⊆ U ^ 2) (hF : (F : Set Group) ⊆ U)
    (hdouble : U ^ 2 ⊆ (Y : Set Group) * U)
    (hcover : U ⊆ (F : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η)) :
    ∃ E E₆ : Finset Group,
      (E : Set Group) ⊆ U ∧
      (E.card : ℝ≥0∞) ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (1025 ^ 4 * Q ^ 12) ∧
      (∀ g ∈ U, ∃ e ∈ E, (∀ i j, |g i j - e i j| < η / 4) ∧
        (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) ∧
      (E₆ : Set Group) ⊆ U ^ 6 ∧
      (E₆.card : ℝ≥0∞) ≤ (Y.card : ℝ≥0∞) ^ 5 * (F.card : ℝ≥0∞) *
        ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52) ∧
      (∀ g ∈ U ^ 6, ∃ e ∈ E₆, (∀ i j, |g i j - e i j| < η / 4) ∧
        (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hr : 0 < 64 * Q ^ 2 * η := by positivity
  obtain ⟨E, hE, hcard, hclose⟩ := exists_frobenius_refinement F hQ0 hr hη (hF.trans hU) hcover
  have hb : 16 * Q * (64 * Q ^ 2 * η) / η + 1 ≤ 1025 * Q ^ 3 := by
    have he : 16 * Q * (64 * Q ^ 2 * η) / η = 1024 * Q ^ 3 := by field_simp; ring
    rw [he]
    have hone : 1 ≤ Q ^ 3 := one_le_pow₀ hQ
    linarith
  have hb4 : (16 * Q * (64 * Q ^ 2 * η) / η + 1) ^ 4 ≤ 1025 ^ 4 * Q ^ 12 := by
    calc
      _ ≤ (1025 * Q ^ 3) ^ 4 := pow_le_pow_left₀ (by positivity) hb 4
      _ = _ := by ring
  have hEcard : (E.card : ℝ≥0∞) ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (1025 ^ 4 * Q ^ 12) :=
    hcard.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hb4))
  let Z : Finset Group := Y ^ 5 * F
  have hZ : (Z : Set Group) ⊆ U ^ 11 := by
    simp only [Z, Finset.coe_mul, Finset.coe_pow]
    calc
      (Y : Set Group) ^ 5 * (F : Set Group) ⊆ (U ^ 2) ^ 5 * U :=
        Set.mul_subset_mul (Set.pow_subset_pow_left hY) hF
      _ = U ^ 11 := by rw [← pow_mul, ← pow_succ]
  have hZcard : (Z.card : ℝ≥0∞) ≤ (Y.card : ℝ≥0∞) ^ 5 * (F.card : ℝ≥0∞) := by
    have hn : Z.card ≤ Y.card ^ 5 * F.card :=
      (Finset.card_mul_le (s := Y ^ 5) (t := F)).trans (Nat.mul_le_mul_right _ Finset.card_pow_le)
    exact_mod_cast hn
  have hpow : U ^ 6 ⊆ (Z : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η) := by
    calc
      U ^ 6 ⊆ (Y : Set Group) ^ 5 * U := Set.pow_subset_pow_mul_of_sq_subset_mul hdouble (by decide)
      _ ⊆ (Y : Set Group) ^ 5 * ((F : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η)) :=
        Set.mul_subset_mul le_rfl hcover
      _ = (Z : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η) := by
        simp only [Z, Finset.coe_mul, Finset.coe_pow, mul_assoc]
  obtain ⟨E₆, hE₆, hcard₆, hclose₆⟩ := exists_frobenius_refinement Z
    (by positivity : 0 < (2 * Q) ^ 11) hr hη (hZ.trans (matrixEntryBox_set_pow hU 11)) hpow
  have hb₆ : 16 * (2 * Q) ^ 11 * (64 * Q ^ 2 * η) / η + 1 ≤ (2 ^ 21 + 1) * Q ^ 13 := by
    have he : 16 * (2 * Q) ^ 11 * (64 * Q ^ 2 * η) / η = 2 ^ 21 * Q ^ 13 := by field_simp; ring
    rw [he]
    have hone : 1 ≤ Q ^ 13 := one_le_pow₀ hQ
    calc
      2 ^ 21 * Q ^ 13 + 1 ≤ 2 ^ 21 * Q ^ 13 + Q ^ 13 := add_le_add le_rfl hone
      _ = _ := by ring
  have hb₆4 : (16 * (2 * Q) ^ 11 * (64 * Q ^ 2 * η) / η + 1) ^ 4 ≤
      (2 ^ 21 + 1) ^ 4 * Q ^ 52 := by
    calc
      _ ≤ ((2 ^ 21 + 1) * Q ^ 13) ^ 4 := pow_le_pow_left₀ (by positivity) hb₆ 4
      _ = _ := by ring
  refine ⟨E, E₆, hE, hEcard, hclose, hE₆, ?_, hclose₆⟩
  exact hcard₆.trans (mul_le_mul' hZcard (ENNReal.ofReal_le_ofReal hb₆4))

end TransposeFollowup.RealMobius
