import TransposeFollowup.SL2ConjugacyFiber

/-! Transfer actual external covers through bounded-error maps and pay
the enlarged radius by explicit four-coordinate refinement. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set BoundedCoordinatePacking
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ

theorem coveringNumber_le_coordinate_patches {A : Set RMat} (F : Finset RMat)
    {N : ℝ} {η : ℝ≥0} (hN : 0 ≤ N) (hη : 0 < η)
    (hpatch : ∀ x ∈ A, ∃ c ∈ F, ∀ i j, |x i j - c i j| ≤ N) :
    Metric.externalCoveringNumber η A ≠ ⊤ ∧
      (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤
        (4 * N / (η : ℝ) + 1) ^ 4 * (F.card : ℝ) := by
  have hηR : (0 : ℝ) < η := hη
  obtain ⟨E, _hEA, hcard, hcover⟩ := exists_coordinate_refinement (fun x : RMat => x) F
    (by positivity : 0 < (η : ℝ) / 2) hpatch
  have hc : Metric.IsCover η A (E : Set RMat) := by
    intro x hx
    obtain ⟨e, he, hdist⟩ := hcover x hx
    refine ⟨e, he, edist_le_coe.mpr ?_⟩
    have hh := frobenius_dist_le_of_entry_error (by positivity : 0 ≤ (η : ℝ) / 2)
      (fun i j => (hdist i j).le)
    have hd : dist x e ≤ (η : ℝ) := by linarith
    exact_mod_cast hd
  have hNc : Metric.externalCoveringNumber η A ≤ (E.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hc.externalCoveringNumber_le_encard
  have hfinite : Metric.externalCoveringNumber η A ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hNc
  have hNr : (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤ (E.card : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono
      (by finiteness : (E.card : ℝ≥0∞) ≠ ⊤) (ENat.toENNReal_mono hNc)
  have hbin : (binCount N ((η : ℝ) / 2) : ℝ) ≤ 4 * N / (η : ℝ) + 1 := by
    have hh := binCount_le hN (by positivity : 0 < (η : ℝ) / 2)
    convert hh using 1
    field_simp
    ring
  have hcardR : (E.card : ℝ) ≤ (F.card : ℝ) * (binCount N ((η : ℝ) / 2) : ℝ) ^ 4 := by
    exact_mod_cast hcard
  refine ⟨hfinite, hNr.trans (hcardR.trans ?_)⟩
  calc
    _ ≤ (F.card : ℝ) * (4 * N / (η : ℝ) + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hbin 4) (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

theorem finite_coveringNumber_of_entry_bound {A : Set RMat} {B : ℝ} {η : ℝ≥0}
    (hB : 0 ≤ B) (hη : 0 < η) (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B) :
    Metric.externalCoveringNumber η A ≠ ⊤ := by
  apply (coveringNumber_le_coordinate_patches ({0} : Finset RMat) hB hη ?_).1
  intro x hx
  exact ⟨0, by simp, by simpa only [Matrix.zero_apply, sub_zero] using hA x hx⟩

theorem coveringNumber_le_bounded_transport {X : Type*} (a b : X → RMat) (L : RMat → RMat)
    {Q D K : ℝ} {η : ℝ≥0} (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hK : 0 ≤ K) (hη : 0 < η)
    (hb : ∀ x i j, |b x i j| ≤ Q)
    (htrans : ∀ x c, dist (a x) (L c) ≤ D + K * dist (b x) c) :
    Metric.externalCoveringNumber η (Set.range a) ≠ ⊤ ∧
      Metric.externalCoveringNumber η (Set.range b) ≠ ⊤ ∧
      (Metric.externalCoveringNumber η (Set.range a) : ℝ≥0∞).toReal ≤
        (4 * (D + K * (η : ℝ)) / (η : ℝ) + 1) ^ 4 *
          (Metric.externalCoveringNumber η (Set.range b) : ℝ≥0∞).toReal := by
  have hfin := finite_coveringNumber_of_entry_bound hQ hη (A := Set.range b)
    (by rintro _ ⟨x, rfl⟩; exact hb x)
  obtain ⟨F, hcover, hcard⟩ := Metric.exists_finset_card_eq_externalCoveringNumber hfin
  have hpatch : ∀ z ∈ Set.range a, ∃ c ∈ F.image L, ∀ i j,
      |z i j - c i j| ≤ D + K * (η : ℝ) := by
    rintro z ⟨x, rfl⟩
    obtain ⟨c, hc, hdist⟩ := hcover (Set.mem_range_self x)
    have hd : dist (b x) c ≤ (η : ℝ) := by exact_mod_cast edist_le_coe.mp hdist
    refine ⟨L c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, ?_⟩
    intro i j
    exact (entry_error_le_frobenius_dist (a x) (L c) i j).trans
      ((htrans x c).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hK)))
  obtain ⟨hafin, habound⟩ := coveringNumber_le_coordinate_patches (F.image L) (by positivity) hη hpatch
  have hcardR : (F.card : ℝ) = (Metric.externalCoveringNumber η (Set.range b) : ℝ≥0∞).toReal := by
    have hh : (F.card : ℝ≥0∞) = (Metric.externalCoveringNumber η (Set.range b) : ℝ≥0∞) := by
      exact_mod_cast hcard
    simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hh
  refine ⟨hafin, hfin, habound.trans ?_⟩
  rw [← hcardR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (Finset.card_image_le (f := L) (s := F))

end TransposeFollowup.SL2Projection
