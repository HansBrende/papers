import TransposeFollowup.SL2TraceCover

/-! Combine small determinant-one patches into a global three-trace
cover. The patch count and local distortion are explicit polynomial losses. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set BoundedCoordinatePacking
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem exists_global_three_trace_cover (g : Fin 4 → G) {A : Set G} {M d r η : ℝ}
    (hM : 1 ≤ M) (hd : 0 < d) (hr : 0 < r) (hη : 0 < η)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hA : ∀ x ∈ A, ∀ j k, |x j k| ≤ M)
    (hA0 : ∀ x ∈ A, 1 / 2 ≤ |x 0 0|)
    (hdet : d ≤ |(traceFrame g).det|) (hsmall : 6144 * M ^ 5 * r ≤ d)
    (F : Fin 4 → Finset ℝ)
    (hF : ∀ x ∈ A, ∀ i, ∃ c ∈ F i,
      |Matrix.trace (((g i)⁻¹ * x : G) : RMat) - c| ≤ η) :
    ∃ (i : Fin 4) (E : Finset G), (E : Set G) ⊆ A ∧
      (E.card : ℝ) ≤ (2 * (M + 1) / r + 1) ^ 4 * (6144 * M ^ 5 / d + 3) ^ 3 *
        (∏ k : Fin 3, ((F (i.succAbove k)).card : ℝ)) ∧
      ∀ x ∈ A, ∃ e ∈ E, dist (x : RMat) (e : RMat) ≤ η := by
  have hpatch0 : ∀ x ∈ A, ∃ c ∈ ({1} : Finset G), ∀ j k, |x j k - c j k| ≤ M + 1 := by
    intro x hx
    refine ⟨1, by simp, ?_⟩
    intro j k
    have hi : |(1 : G) j k| ≤ 1 := by fin_cases j <;> fin_cases k <;> norm_num
    have hh := norm_sub_le (x j k) ((1 : G) j k)
    simp only [Real.norm_eq_abs] at hh
    linarith [hA x hx j k]
  obtain ⟨Z, hZA, hZcard, hZcover⟩ := exists_coordinate_refinement
    (fun x : G => fun j k => x j k) ({1} : Finset G) hr hpatch0
  have hZcard' : (Z.card : ℝ) ≤ (2 * (M + 1) / r + 1) ^ 4 := by
    have hn : Z.card ≤ binCount (M + 1) r ^ 4 := by simpa using hZcard
    have hc : (Z.card : ℝ) ≤ (binCount (M + 1) r : ℝ) ^ 4 := by exact_mod_cast hn
    exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (binCount_le (by linarith) hr) 4)
  let L := (6144 * M ^ 5 / d + 3) ^ 3
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let T (i : Fin 4) : ℝ := ∏ k : Fin 3, ((F (i.succAbove k)).card : ℝ)
  have hT (i : Fin 4) : 0 ≤ T i := Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  let patch (z : Z) : Set G := {x | x ∈ A ∧ ∀ j k, |x j k - (z : G) j k| ≤ r}
  have hlocal : ∀ z : Z, ∃ (i : Fin 4) (E : Finset G), (E : Set G) ⊆ A ∧
      (E.card : ℝ) ≤ T i * L ∧
      ∀ x ∈ patch z, ∃ e ∈ E, dist (x : RMat) (e : RMat) ≤ η := by
    intro z
    have hzA : (z : G) ∈ A := hZA z.2
    obtain ⟨i, hi⟩ := exists_local_three_trace_cover g z hM hd hr.le hg (hA z hzA)
      (hA0 z hzA) hdet hsmall
    obtain ⟨E, hE, hcard, hcover⟩ := hi (A := patch z) hη (fun x hx => hx.2)
      (fun k => F (i.succAbove k)) (fun x hx k => hF x hx.1 (i.succAbove k))
    exact ⟨i, E, fun x hx => (hE hx).1, hcard, hcover⟩
  choose index cover hsub hcard hcover using hlocal
  obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image T Finset.univ_nonempty
  let E := Finset.univ.biUnion cover
  refine ⟨i, E, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, _, hx⟩ := Finset.mem_biUnion.mp hx
    exact hsub z hx
  · have hsum : (E.card : ℝ) ≤ ∑ z : Z, ((cover z).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : E.card ≤ ∑ z : Z, (cover z).card)
    calc
      _ ≤ ∑ z : Z, ((cover z).card : ℝ) := hsum
      _ ≤ ∑ _z : Z, T i * L := by
        apply Finset.sum_le_sum
        intro z _
        exact (hcard z).trans (mul_le_mul_of_nonneg_right (hmax _ (Finset.mem_univ _)) hL)
      _ = (Z.card : ℝ) * (T i * L) := by simp
      _ ≤ (2 * (M + 1) / r + 1) ^ 4 * (T i * L) :=
        mul_le_mul_of_nonneg_right hZcard' (mul_nonneg (hT i) hL)
      _ = _ := by dsimp only [T, L]; ring
  · intro x hx
    obtain ⟨z, hz, hclose⟩ := hZcover x hx
    obtain ⟨e, he, hdist⟩ := hcover ⟨z, hz⟩ x ⟨hx, fun j k => (hclose j k).le⟩
    exact ⟨e, Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, he⟩, hdist⟩

theorem trace_abs_le_of_entry_bounds {g x : G} {M : ℝ}
    (hg : ∀ j k, |g j k| ≤ M) (hx : ∀ j k, |x j k| ≤ M) :
    |Matrix.trace ((g⁻¹ * x : G) : RMat)| ≤ 4 * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0 0)
  have hn (i : Fin 4) : |determinantNormal (matrixCoordinates (g : RMat)) i| ≤ M := by
    fin_cases i <;> simpa [determinantNormal, matrixCoordinates] using hg _ _
  have hv (i : Fin 4) : |matrixCoordinates (x : RMat) i| ≤ M := by
    fin_cases i <;> simpa [matrixCoordinates] using hx _ _
  change |Matrix.trace (((g⁻¹ : G) : RMat) * (x : RMat))| ≤ _
  rw [← normal_dot_matrix]
  calc
    _ ≤ ∑ i : Fin 4,
        |determinantNormal (matrixCoordinates (g : RMat)) i * matrixCoordinates (x : RMat) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, M * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hn i) (hv i) (abs_nonneg _) hM
    _ = _ := by simp; ring

theorem global_three_trace_coveringNumber (g : Fin 4 → G) {A : Set G} {M d r : ℝ}
    {η : ℝ≥0} (hM : 1 ≤ M) (hd : 0 < d) (hr : 0 < r) (hη : 0 < η)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hA : ∀ x ∈ A, ∀ j k, |x j k| ≤ M)
    (hA0 : ∀ x ∈ A, 1 / 2 ≤ |x 0 0|)
    (hdet : d ≤ |(traceFrame g).det|) (hsmall : 6144 * M ^ 5 * r ≤ d) :
    ∃ i : Fin 4,
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        (2 * (M + 1) / r + 1) ^ 4 * (6144 * M ^ 5 / d + 3) ^ 3 *
        ∏ k : Fin 3, (Metric.externalCoveringNumber η
          ((fun x : G => Matrix.trace (((g (i.succAbove k))⁻¹ * x : G) : RMat)) '' A) : ℝ≥0∞).toReal := by
  let S (i : Fin 4) : Set ℝ :=
    (fun x : G => Matrix.trace (((g i)⁻¹ * x : G) : RMat)) '' A
  have hfinite (i : Fin 4) : Metric.externalCoveringNumber η (S i) ≠ ⊤ := by
    have hsub : S i ⊆ Set.Icc (-(4 * M ^ 2)) (4 * M ^ 2) := by
      rintro _ ⟨x, hx, rfl⟩
      exact abs_le.mp (trace_abs_le_of_entry_bounds (hg i) (hA x hx))
    have ht : TotallyBounded (S i) := isCompact_Icc.totallyBounded.subset hsub
    obtain ⟨N, _hN, hNfin, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded hη.ne' ht
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin) hcover.externalCoveringNumber_le_encard
  have hattain (i : Fin 4) := Metric.exists_finset_card_eq_externalCoveringNumber (hfinite i)
  choose F hcover hcard using hattain
  have hF : ∀ x ∈ A, ∀ i, ∃ c ∈ F i,
      |Matrix.trace (((g i)⁻¹ * x : G) : RMat) - c| ≤ (η : ℝ) := by
    intro x hx i
    obtain ⟨c, hc, hdist⟩ := hcover i (Set.mem_image_of_mem _ hx)
    have hdR : dist (Matrix.trace (((g i)⁻¹ * x : G) : RMat)) c ≤ (η : ℝ) := by
      exact_mod_cast edist_le_coe.mp hdist
    exact ⟨c, hc, by simpa only [Real.dist_eq] using hdR⟩
  obtain ⟨i, E, _hE, hEcard, hEcover⟩ := exists_global_three_trace_cover g hM hd hr
    (by exact hη) hg hA hA0 hdet hsmall F hF
  have hc : Metric.IsCover η ((fun x : G => (x : RMat)) '' A)
      (E.image (fun x : G => (x : RMat)) : Set RMat) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, hdist⟩ := hEcover x hx
    exact ⟨(e : RMat), Finset.mem_image.mpr ⟨e, he, rfl⟩, edist_le_coe.mpr hdist⟩
  have hn : Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) ≤ (E.card : ℕ∞) := by
    have hh := hc.externalCoveringNumber_le_encard
    rw [Set.encard_coe_eq_coe_finsetCard] at hh
    exact hh.trans (by exact_mod_cast (Finset.card_image_le (f := fun x : G => (x : RMat)) (s := E)))
  have hnR : (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
      (E.card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using
      ENNReal.toReal_mono (by finiteness : (E.card : ℝ≥0∞) ≠ ⊤) (ENat.toENNReal_mono hn)
  have hFreal (j : Fin 4) : ((F j).card : ℝ) =
      (Metric.externalCoveringNumber η (S j) : ℝ≥0∞).toReal := by
    have hh : ((F j).card : ℝ≥0∞) = (Metric.externalCoveringNumber η (S j) : ℝ≥0∞) := by
      exact_mod_cast hcard j
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  refine ⟨i, hnR.trans ?_⟩
  simpa only [hFreal, S] using hEcard

theorem trace_cover_loss_bound {M d : ℝ} (hM : 1 ≤ M) (hd : 0 < d) (hd1 : d ≤ 1) :
    (2 * (M + 1) / (d / (6144 * M ^ 5)) + 1) ^ 4 * (6144 * M ^ 5 / d + 3) ^ 3 ≤
      (12288 * (M + 1) * M ^ 5 + 1) ^ 4 * (6144 * M ^ 5 + 3) ^ 3 / d ^ 7 := by
  have hM0 : 0 < M := by linarith
  have he : 2 * (M + 1) / (d / (6144 * M ^ 5)) + 1 =
      (12288 * (M + 1) * M ^ 5 + d) / d := by field_simp; ring
  have h₁ : 2 * (M + 1) / (d / (6144 * M ^ 5)) + 1 ≤
      (12288 * (M + 1) * M ^ 5 + 1) / d := by
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  have h₂ : 6144 * M ^ 5 / d + 3 ≤ (6144 * M ^ 5 + 3) / d := by
    apply (le_div_iff₀ hd).mpr
    have he' : (6144 * M ^ 5 / d + 3) * d = 6144 * M ^ 5 + 3 * d := by field_simp
    rw [he']
    linarith
  calc
    _ ≤ ((12288 * (M + 1) * M ^ 5 + 1) / d) ^ 4 * ((6144 * M ^ 5 + 3) / d) ^ 3 := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) h₁ 4)
        (pow_le_pow_left₀ (by positivity) h₂ 3) (by positivity) (by positivity)
    _ = _ := by rw [div_pow, div_pow, div_mul_div_comm, ← pow_add]

theorem global_three_trace_coveringNumber_polynomial (g : Fin 4 → G) {A : Set G} {M d : ℝ}
    {η : ℝ≥0} (hM : 1 ≤ M) (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η)
    (hg : ∀ i j k, |g i j k| ≤ M)
    (hA : ∀ x ∈ A, ∀ j k, |x j k| ≤ M)
    (hA0 : ∀ x ∈ A, 1 / 2 ≤ |x 0 0|)
    (hdet : d ≤ |(traceFrame g).det|) :
    ∃ i : Fin 4,
      (Metric.externalCoveringNumber η ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal ≤
        ((12288 * (M + 1) * M ^ 5 + 1) ^ 4 * (6144 * M ^ 5 + 3) ^ 3 / d ^ 7) *
        ∏ k : Fin 3, (Metric.externalCoveringNumber η
          ((fun x : G => Matrix.trace (((g (i.succAbove k))⁻¹ * x : G) : RMat)) '' A) : ℝ≥0∞).toReal := by
  have hM0 : 0 < M := by linarith
  let r := d / (6144 * M ^ 5)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsmall : 6144 * M ^ 5 * r ≤ d := by
    dsimp only [r]
    rw [mul_div_cancel₀ _ (by positivity : (6144 : ℝ) * M ^ 5 ≠ 0)]
  obtain ⟨i, hi⟩ := global_three_trace_coveringNumber g hM hd hr hη hg hA hA0 hdet hsmall
  refine ⟨i, hi.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (trace_cover_loss_bound hM hd hd1)
  exact Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)

end TransposeFollowup.SL2Projection
