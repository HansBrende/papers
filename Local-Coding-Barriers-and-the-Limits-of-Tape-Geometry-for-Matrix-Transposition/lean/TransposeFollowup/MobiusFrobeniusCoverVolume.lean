import TransposeFollowup.MobiusLocalCoverGeometry
import TransposeFollowup.MobiusSmallBallVolume

/-! Every external ordinary Frobenius cover of a near-identity set has
cardinality at least its Haar volume divided by a controlled ball volume. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

theorem entry_error_lt_of_frobenius {g e : Matrix (Fin 2) (Fin 2) ℝ} {η : ℝ} (hη : 0 < η)
    (h : (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) (i j : Fin 2) :
    |g i j - e i j| < η := by
  have hj : (g i j - e i j) ^ 2 ≤ ∑ j : Fin 2, (g i j - e i j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (g i j - e i j)) (Finset.mem_univ j)
  have hi : (∑ j : Fin 2, (g i j - e i j) ^ 2) ≤ ∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2 :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (g i j - e i j))) (Finset.mem_univ i)
  exact (sq_lt_sq₀ (abs_nonneg _) hη.le).mp (by simpa only [sq_abs] using (hj.trans hi).trans_lt h)

variable [MeasurableSpace Group] [BorelSpace Group]

theorem haar_le_frobenius_cover_card {A : Set Group} (F : Finset (Matrix (Fin 2) (Fin 2) ℝ)) {η : ℝ}
    (hη : 0 < η) (hA : A ⊆ matrixEntryBox 2)
    (hcover : ∀ g ∈ A, ∃ e ∈ F, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) :
    (Measure.haar : Measure Group) A ≤
      (F.card : ℝ≥0∞) * (Measure.haar : Measure Group) (mobiusIdentityBall (16 * η)) := by
  let H : Measure Group := Measure.haar
  let S (e : Matrix (Fin 2) (Fin 2) ℝ) := A ∩ {g | (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2}
  have hpiece (e : Matrix (Fin 2) (Fin 2) ℝ) : H (S e) ≤ H (mobiusIdentityBall (16 * η)) := by
    by_cases hn : (S e).Nonempty
    · obtain ⟨a, ha⟩ := hn
      have hs : S e ⊆ (fun g => g * a⁻¹) ⁻¹' mobiusIdentityBall (16 * η) := by
        intro g hg
        have hdiff (i j : Fin 2) : |g i j - a i j| < 2 * η := by
          calc
            _ ≤ |g i j - e i j| + |a i j - e i j| := by
              simpa only [abs_sub_comm (e i j) (a i j)] using abs_sub_le (g i j) (e i j) (a i j)
            _ < η + η := add_lt_add (entry_error_lt_of_frobenius hη hg.2 i j)
              (entry_error_lt_of_frobenius hη ha.2 i j)
            _ = _ := by ring
        change g * a⁻¹ ∈ mobiusIdentityBall (16 * η)
        simpa only [show 4 * (2 * η) * 2 = 16 * η by ring] using
          mobius_quotient_ball_of_entry_difference (by norm_num : (0 : ℝ) < 2) (hA ha.1) hdiff
      exact (measure_mono hs).trans_eq (measure_preimage_mul_right H a⁻¹ _)
    · rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty]
      exact bot_le
  calc
    H A ≤ H (⋃ e ∈ F, S e) := by
      apply measure_mono
      intro g hg
      obtain ⟨e, he, hge⟩ := hcover g hg
      exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, ⟨hg, hge⟩⟩⟩
    _ ≤ ∑ e ∈ F, H (S e) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _e ∈ F, H (mobiusIdentityBall (16 * η)) := Finset.sum_le_sum (fun e _ => hpiece e)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, H]

theorem haar_identityBall_sixteen {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 32) :
    (Measure.haar : Measure Group) (mobiusIdentityBall (16 * η)) ≤
      393216 ^ 4 * (Measure.haar : Measure Group) (mobiusIdentityBall η) := by
  let H : Measure Group := Measure.haar
  have h1 := haar_identityBall_doubling hη (by linarith)
  have h2 := haar_identityBall_doubling (by positivity : 0 < 2 * η) (by linarith)
  have h4 := haar_identityBall_doubling (by positivity : 0 < 4 * η) (by linarith)
  have h8 := haar_identityBall_doubling (by positivity : 0 < 8 * η) (by linarith)
  calc
    H (mobiusIdentityBall (16 * η)) ≤ 393216 * H (mobiusIdentityBall (8 * η)) := by
      simpa only [show 2 * (8 * η) = 16 * η by ring] using h8
    _ ≤ 393216 * (393216 * H (mobiusIdentityBall (4 * η))) := mul_le_mul' le_rfl (by
      simpa only [show 2 * (4 * η) = 8 * η by ring] using h4)
    _ ≤ 393216 * (393216 * (393216 * H (mobiusIdentityBall (2 * η)))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (by
        simpa only [show 2 * (2 * η) = 4 * η by ring] using h2))
    _ ≤ 393216 * (393216 * (393216 * (393216 * H (mobiusIdentityBall η)))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl h1))
    _ = _ := by ring

theorem haar_le_frobenius_cover_card_at_scale {A : Set Group} (F : Finset (Matrix (Fin 2) (Fin 2) ℝ)) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 32) (hA : A ⊆ matrixEntryBox 2)
    (hcover : ∀ g ∈ A, ∃ e ∈ F, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) :
    (Measure.haar : Measure Group) A ≤
      393216 ^ 4 * (F.card : ℝ≥0∞) * (Measure.haar : Measure Group) (mobiusIdentityBall η) := by
  calc
    _ ≤ (F.card : ℝ≥0∞) * (Measure.haar : Measure Group) (mobiusIdentityBall (16 * η)) :=
      haar_le_frobenius_cover_card F hη hA hcover
    _ ≤ (F.card : ℝ≥0∞) * (393216 ^ 4 * (Measure.haar : Measure Group) (mobiusIdentityBall η)) :=
      mul_le_mul' le_rfl (haar_identityBall_sixteen hη hηsmall)
    _ = _ := by ring

end TransposeFollowup.RealMobius
