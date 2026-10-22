import TransposeFollowup.ShiftedTraceFrame
import TransposeFollowup.FinitePieceCoverBounds
import TransposeFollowup.SL2ConjugacyFiber
import TransposeFollowup.TraceBucketCover

/-! Retain covering mass in a small patch, then choose a translated
spanning frame whose trace coordinates avoid two throughout that patch.
The loss is an explicit polynomial of the original frame determinant. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem exists_retained_entry_patch {A : Set G} {B r : ℝ} {η : ℝ≥0}
    (hA : A.Nonempty) (hB : 0 ≤ B) (hr : 0 < r) (hη : 0 < η)
    (hAb : ∀ x ∈ A, ∀ i j, |x i j| ≤ B) :
    ∃ x₀ ∈ A,
      let R := {x : G | x ∈ A ∧ ∀ i j, |x i j - x₀ i j| ≤ r}
      R.Nonempty ∧ Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' R) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        (2 * (B + 1) / r + 1) ^ 4 *
          (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' R) : ℝ≥0∞).toReal := by
  have hpatch : ∀ x ∈ A, ∃ c ∈ ({1} : Finset G), ∀ i j, |x i j - c i j| ≤ B + 1 := by
    intro x hx
    refine ⟨1, by simp, ?_⟩
    intro i j
    have hI : |(1 : G) i j| ≤ 1 := by fin_cases i <;> fin_cases j <;> norm_num
    exact (abs_sub _ _).trans (add_le_add (hAb x hx i j) hI)
  obtain ⟨Z, hZA, hZcard, hZcover⟩ := exists_coordinate_refinement
    (fun x : G => fun i j => x i j) {1} hr hpatch
  have hZn : Z.Nonempty := by
    obtain ⟨x, hx⟩ := hA
    obtain ⟨z, hz, _⟩ := hZcover x hx
    exact ⟨z, hz⟩
  let P (z : G) : Set G := {x | x ∈ A ∧ ∀ i j, |x i j - z i j| ≤ r}
  have hfin (z : G) : Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' P z) ≠ ⊤ := by
    apply finite_coveringNumber_of_entry_bound hB hη
    rintro y ⟨x, hx, rfl⟩
    exact hAb x hx.1
  have hcover : ∀ x ∈ ((fun x : G => (x : RMat)) '' A),
      ∃ z ∈ Z, x ∈ ((fun x : G => (x : RMat)) '' P z) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hc⟩ := hZcover x hx
    exact ⟨z, hz, x, ⟨hx, fun i j => (hc i j).le⟩, rfl⟩
  have hsum := (coveringNumber_le_sum_of_cover Z ((fun x : G => (x : RMat)) '' A)
    (fun z => (fun x : G => (x : RMat)) '' P z) hcover (fun z _ => hfin z)).2
  let N (z : G) := (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' P z) : ℝ≥0∞).toReal
  obtain ⟨z, hz, hmax⟩ := Z.exists_max_image N hZn
  have hcard : (Z.card : ℝ) ≤ (2 * (B + 1) / r + 1) ^ 4 := by
    have hh : Z.card ≤ binCount (B + 1) r ^ 4 := by simpa only [Finset.card_singleton, one_mul] using hZcard
    have hhR : (Z.card : ℝ) ≤ (binCount (B + 1) r : ℝ) ^ 4 := by exact_mod_cast hh
    exact hhR.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (binCount_le (by positivity) hr) 4)
  refine ⟨z, hZA hz, ⟨z, hZA hz, by intro i j; simpa only [sub_self, abs_zero] using hr.le⟩, hfin z, ?_⟩
  calc
    _ ≤ ∑ y ∈ Z, N y := hsum
    _ ≤ ∑ _y ∈ Z, N z := Finset.sum_le_sum hmax
    _ = (Z.card : ℝ) * N z := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard ENNReal.toReal_nonneg

theorem exists_retained_trace_gap :
    ∃ n₀ : ℕ, ∃ α₀ C : ℝ,
      34 ≤ n₀ ∧ 0 < α₀ ∧ α₀ ≤ 1 / 2 ∧ 0 < C ∧
      ∀ {A : Set G} {α d : ℝ} {η : ℝ≥0} {p q : G},
      1 ∈ A → A⁻¹ = A → 0 < α → α ≤ α₀ → A ⊆ mobiusIdentityBall α →
      0 < d → d ≤ 1 → 0 < η → p ∈ A ^ 34 → q ∈ A ^ 34 → p * q ∈ A ^ 34 →
      d ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det| →
      ∃ R : Set G, R ⊆ A ∧ R.Nonempty ∧
        Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' R) ≠ ⊤ ∧
        ∃ h ∈ A ^ n₀,
          (∀ x ∈ R, d / 16 < |Matrix.trace ((h⁻¹ * x : G) : RMat) - 2|) ∧
          d ^ 11 * (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
            C * (Metric.externalCoveringNumber η
              ((fun x : G => Matrix.trace ((h⁻¹ * x : G) : RMat)) '' R) : ℝ≥0∞).toReal ^ 3 := by
  obtain ⟨n₀, α₀, hn₀, hα₀, hαhalf, hframe⟩ := exists_actual_frame_away_trace_two
  let M := (4 : ℝ) ^ n₀
  have hM : 2 ≤ M := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show 1 ≤ n₀ by omega)
    exact (by norm_num : (2 : ℝ) ≤ 4 ^ 1).trans hh
  let P := 256 * M * (M + 1) + 1
  let T := (12288 * (M + 1) * M ^ 5 + 1) ^ 4 * (6144 * M ^ 5 + 3) ^ 3
  have hP : 0 < P := by dsimp only [P]; positivity
  have hT : 0 < T := by dsimp only [T, M]; positivity
  refine ⟨n₀, α₀, P ^ 4 * T, hn₀, hα₀, hαhalf, by positivity, ?_⟩
  intro A α d η p q hA1 hAi hα hαbound hA hd hd1 hη hp hq hpq hspan
  have hαhalf' : α ≤ 1 / 2 := hαbound.trans hαhalf
  have hAb : A ⊆ matrixEntryBox 2 := hA.trans
    (mobiusIdentityBall_subset_entryBox_two hα (by linarith only [hαhalf']))
  have hAM : ∀ x ∈ A, ∀ i j, |x i j| ≤ M := fun x hx i j => (hAb hx i j).trans hM
  have hpow : A ^ n₀ ⊆ matrixEntryBox M := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using set_pow_subset_matrixEntryBox hAb n₀
  let r := d / (128 * M)
  have hr : 0 < r := by dsimp only [r, M]; positivity
  obtain ⟨x₀, hx₀, hRn, hRfin, hretain⟩ := exists_retained_entry_patch
    ⟨1, hA1⟩ (zero_le_two.trans hM) hr hη hAM
  let R := {x : G | x ∈ A ∧ ∀ i j, |x i j - x₀ i j| ≤ r}
  have hRA : R ⊆ A := fun _ hx => hx.1
  obtain ⟨k, hk, hkdet, hkgap⟩ := hframe hA1 hAi hα hαbound hA hd hp hq hpq hspan x₀
  have hgap (i : Fin 4) (x : G) (hx : x ∈ R) :
      d / 16 < |Matrix.trace (((k i)⁻¹ * x : G) : RMat) - 2| := by
    have hdist : dist (x : RMat) (x₀ : RMat) ≤ 2 * r :=
      frobenius_dist_le_of_entry_error hr.le hx.2
    have hnorm := frobenius_norm_le_of_entry_bound (zero_le_two.trans hM)
      (matrixEntryBox_inv (hpow (hk i)))
    have he : |Matrix.trace (((k i)⁻¹ * x : G) : RMat) -
        Matrix.trace (((k i)⁻¹ * x₀ : G) : RMat)| ≤ d / 16 := by
      have hh := (trace_error_le_frobenius_dist
        (((k i)⁻¹ * x : G) : RMat) (((k i)⁻¹ * x₀ : G) : RMat)).trans
        (mul_le_mul_of_nonneg_left
          ((frobenius_dist_left_mul (((k i)⁻¹ : G) : RMat) (x : RMat) (x₀ : RMat)).trans
            (mul_le_mul hnorm hdist dist_nonneg (by positivity))) (by norm_num))
      have heq : 2 * ((2 * M) * (2 * r)) = d / 16 := by dsimp only [r]; field_simp; ring
      simpa only [heq] using hh
    have hh := abs_sub_le (Matrix.trace (((k i)⁻¹ * x₀ : G) : RMat))
      (Matrix.trace (((k i)⁻¹ * x : G) : RMat)) 2
    rw [abs_sub_comm (Matrix.trace (((k i)⁻¹ * x₀ : G) : RMat))
      (Matrix.trace (((k i)⁻¹ * x : G) : RMat))] at hh
    linarith only [hkgap i, he, hh]
  obtain ⟨i, hi⟩ := exists_large_trace_of_frame k (A := R) (M := M) (η := η)
    (by linarith only [hM]) hd hd1 hη (fun i => hpow (hk i))
    (fun x hx => hAM x (hRA hx))
    (fun x hx => mobiusIdentityBall_entry_zero_lower hα hαhalf' (hA (hRA hx))) hkdet
  refine ⟨R, hRA, hRn, hRfin, k i, hk i, hgap i, ?_⟩
  have hK : (2 * (M + 1) / r + 1) ^ 4 ≤ P ^ 4 / d ^ 4 := by
    have heq : 2 * (M + 1) / r + 1 = (256 * M * (M + 1) + d) / d := by
      dsimp only [r]
      field_simp
      ring
    rw [heq, ← div_pow]
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (by dsimp only [P]; linarith only [hd1]) hd.le
  have hbound := hretain.trans (mul_le_mul hK hi ENNReal.toReal_nonneg (by positivity : 0 ≤ P ^ 4 / d ^ 4))
  have hh := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le 11)
  convert hh using 1
  dsimp only [T]
  field_simp

end TransposeFollowup.SL2Projection
