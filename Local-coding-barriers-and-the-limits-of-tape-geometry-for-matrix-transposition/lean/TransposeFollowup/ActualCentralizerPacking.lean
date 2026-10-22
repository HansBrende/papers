import TransposeFollowup.LocalizedCentralizerPacking
import TransposeFollowup.SL2NearIdentityAdjointFrame

/-! Actual bounded words select the frame for a retained commuting sample.
The conclusion concerns the exact approximants; transfer to their source
words, including its error and scale losses, is a separate obligation. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius BoundedCoordinatePacking
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem centered_near_identity_generator_bounds (z : G)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) :
    let b := (z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)
    ‖b‖ ≤ 32 ∧ |b.det| ≤ 32 := by
  let b := (z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)
  have he : ∀ i j, |z i j| ≤ 2 :=
    mobiusIdentityBall_subset_entryBox_two (by norm_num) (by norm_num) hz
  have htr : |Matrix.trace (z : RMat) / 2| ≤ 2 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, abs_div,
      show |(2 : ℝ)| = 2 by norm_num]
    have hh := (abs_add_le (z 0 0) (z 1 1)).trans (add_le_add (he 0 0) (he 1 1))
    linarith
  have hb : ∀ i j, |b i j| ≤ 4 := by
    intro i j
    have hI : |(1 : RMat) i j| ≤ 1 := by
      fin_cases i <;> fin_cases j <;> norm_num
    change |z i j - (Matrix.trace (z : RMat) / 2) * (1 : RMat) i j| ≤ 4
    calc
      _ ≤ |z i j| + |(Matrix.trace (z : RMat) / 2) * (1 : RMat) i j| := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (z i j) ((Matrix.trace (z : RMat) / 2) * (1 : RMat) i j)
      _ ≤ 2 + 2 * 1 := by
        rw [abs_mul]
        exact add_le_add (he i j) (mul_le_mul htr hI (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  change ‖b‖ ≤ 32 ∧ |b.det| ≤ 32
  constructor
  · exact (frobenius_norm_le_of_entry_bound (by norm_num) hb).trans (by norm_num)
  · rw [Matrix.det_fin_two]
    calc
      _ ≤ |b 0 0 * b 1 1| + |b 0 1 * b 1 0| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (b 0 0 * b 1 1) (b 0 1 * b 1 0)
      _ ≤ 4 * 4 + 4 * 4 := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hb 0 0) (hb 1 1) (abs_nonneg _) (by norm_num))
          (mul_le_mul (hb 0 1) (hb 1 0) (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num

theorem exists_actual_localized_cubic_packing {ι : Type*} [Fintype ι]
    (f : ι → G) (c t : ι → ℝ) {A : Set G} {p q z : G}
    {α d₀ r₀ B M r δ d : ℝ} {η : ℝ≥0} {m : ℕ}
    (hA1 : 1 ∈ A) (hAi : A⁻¹ = A) (hα : 0 < α) (hαone : α ≤ 1)
    (hA : A ⊆ mobiusIdentityBall α) (hαsmall : 2 * (5 : ℝ) ^ 34 * α ≤ 1)
    (hp : p ∈ A ^ 34) (hq : q ∈ A ^ 34) (hpq : p * q ∈ A ^ 34)
    (hd₀ : 0 < d₀)
    (hspan : d₀ ≤ |(SL2Escape.pairSpanMatrix (p : RMat) (q : RMat)).det|)
    (hz : z ∈ mobiusIdentityBall (1 / 2)) (hr₀ : 0 < r₀)
    (hfar : r₀ ≤ dist (z : RMat) 1)
    (hB : 1 ≤ B) (hM : 1 ≤ M) (hscale : 128 * ((4 : ℝ) ^ 68) ^ 2 ≤ M)
    (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine (z : RMat) (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ (r₀ / 8) * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι)
    (hd : 0 < d)
    (hframe : d ≤ (r₀ / 8) ^ 3 / (3456 * (96 * ((4 : ℝ) ^ 34) ^ 4 / d₀) ^ 3))
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat)) :
    ∃ u ∈ A ^ 34, ∃ v ∈ A ^ 68, ∃ x₀ : ι, ∃ F : Finset ℝ, ∃ s : ℝ → ι,
      m ≤ F.card ∧
      (∀ x ∈ F, dist (f (s x) : RMat) (f x₀ : RMat) ≤ 2 * δ) ∧
      let w := fun x => (f x₀)⁻¹ * f (s x)
      let S := Set.range (fun x : Fin 3 → ↥F =>
        ((w (x 0) * (u * w (x 1) * u⁻¹) * (v * w (x 2) * v⁻¹) : G) : RMat))
      Metric.externalCoveringNumber η S ≠ ⊤ ∧
        (m : ℝ) ^ 3 ≤ (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal := by
  let b := (z : RMat) - (Matrix.trace (z : RMat) / 2) • (1 : RMat)
  obtain ⟨u, hu, v, hv, hdet⟩ := exists_adjoint_frame_from_actual_spanning
    hA1 hAi hα hαone hA hαsmall hp hq hpq hd₀ hspan hz hr₀ hfar
  have hAb : A ⊆ matrixEntryBox 2 :=
    hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hub : ∀ i j, |u i j| ≤ (4 : ℝ) ^ 68 := by
    intro i j
    have hh : |u i j| ≤ (4 : ℝ) ^ 34 := by
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        set_pow_subset_matrixEntryBox hAb 34 hu i j
    exact hh.trans (pow_le_pow_right₀ (by norm_num) (by norm_num : 34 ≤ 68))
  have hvb : ∀ i j, |v i j| ≤ (4 : ℝ) ^ 68 := by
    intro i j
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      set_pow_subset_matrixEntryBox hAb 68 hv i j
  have hb : Matrix.trace b = 0 := (centered_generator_coordinates (z : RMat)).1
  have hpivot : ∃ i, r₀ / 8 ≤ |noncentralCoordinates b i| := by
    rw [show noncentralCoordinates b = noncentralCoordinates (z : RMat) from
      (centered_generator_coordinates (z : RMat)).2]
    exact exists_near_identity_noncentral_pivot z (by norm_num) (by norm_num) hz hfar
  have hbf : ∀ x, (f x : RMat) =
      scalarAffine b (c x + t x * Matrix.trace (z : RMat) / 2) (t x) := by
    intro x
    rw [hform x, scalarAffine_recenter]
  obtain ⟨hbn, hbd⟩ := centered_near_identity_generator_bounds z hz
  refine ⟨u, hu, v, hv, ?_⟩
  apply exists_localized_conjugated_cubic_packing f b
    (fun x => c x + t x * Matrix.trace (z : RMat) / 2) t u v
    hB (by norm_num) (by norm_num : (1 : ℝ) ≤ 32) hM
    (by convert hscale using 1; ring) hub hvb (by positivity : 0 < r₀ / 8)
    hδ hr hr1 hm hb hbn hbd hpivot hf hbf hbranch hradius hcard hd hsmall habsorb
    (hframe.trans hdet) hsep

end TransposeFollowup.SL2Projection
