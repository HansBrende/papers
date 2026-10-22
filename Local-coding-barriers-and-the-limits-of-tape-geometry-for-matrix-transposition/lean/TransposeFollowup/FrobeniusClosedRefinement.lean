import TransposeFollowup.ExternalCoverAttainment
import TransposeFollowup.CoordinateCoverRefinement
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.Cover

/-! Use Mathlib's Frobenius metric, and refine its closed-ball covers
into strict covers at the same radius with an explicit constant loss. -/
namespace TransposeFollowup
open Classical Set
open scoped ENNReal NNReal Matrix.Norms.Frobenius
set_option autoImplicit false

theorem frobenius_dist_sq (a b : Matrix (Fin 2) (Fin 2) ℝ) :
    dist a b ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, (a i j - b i j) ^ 2 := by
  rw [dist_eq_norm, Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, Real.norm_eq_abs, Matrix.sub_apply, sq_abs, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (a i j - b i j))))

theorem frobenius_dist_le_iff {a b : Matrix (Fin 2) (Fin 2) ℝ} {η : ℝ} (hη : 0 ≤ η) :
    dist a b ≤ η ↔ (∑ i : Fin 2, ∑ j : Fin 2, (a i j - b i j) ^ 2) ≤ η ^ 2 := by
  rw [← frobenius_dist_sq]
  exact (sq_le_sq₀ dist_nonneg hη).symm

theorem isCover_of_strict_frobenius {A : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (F : Finset (Matrix (Fin 2) (Fin 2) ℝ)) {η : ℝ≥0}
    (hcover : ∀ g ∈ A, ∃ e ∈ F,
      (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < (η : ℝ) ^ 2) :
    Metric.IsCover η A (F : Set (Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro g hg
  obtain ⟨e, he, hge⟩ := hcover g hg
  refine ⟨e, he, edist_le_coe.mpr ?_⟩
  have hd : dist g e ≤ (η : ℝ) := (frobenius_dist_le_iff η.coe_nonneg).mpr hge.le
  exact_mod_cast hd

theorem exists_strict_frobenius_refinement {A : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (F : Finset (Matrix (Fin 2) (Fin 2) ℝ)) {η : ℝ≥0} (hη : 0 < η)
    (hcover : Metric.IsCover η A (F : Set (Matrix (Fin 2) (Fin 2) ℝ))) :
    ∃ E : Finset (Matrix (Fin 2) (Fin 2) ℝ), (E : Set (Matrix (Fin 2) (Fin 2) ℝ)) ⊆ A ∧
      E.card ≤ 6561 * F.card ∧
      ∀ g ∈ A, ∃ e ∈ E, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < (η : ℝ) ^ 2 := by
  have hηr : (0 : ℝ) < η := hη
  have hpatch : ∀ g ∈ A, ∃ e ∈ F, ∀ i j, |g i j - e i j| ≤ (η : ℝ) := by
    intro g hg
    obtain ⟨e, he, hed⟩ := hcover hg
    have hd : dist g e ≤ (η : ℝ) := by exact_mod_cast (edist_le_coe.mp hed)
    have hs := (frobenius_dist_le_iff η.coe_nonneg).mp hd
    refine ⟨e, he, fun i j => ?_⟩
    have hj : (g i j - e i j) ^ 2 ≤ ∑ j : Fin 2, (g i j - e i j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (g i j - e i j)) (Finset.mem_univ j)
    have hi : (∑ j : Fin 2, (g i j - e i j) ^ 2) ≤ ∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2 :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (g i j - e i j))) (Finset.mem_univ i)
    exact (sq_le_sq₀ (abs_nonneg _) η.coe_nonneg).mp (by simpa only [sq_abs] using (hj.trans hi).trans hs)
  obtain ⟨E, hE, hcard, hclose⟩ := BoundedCoordinatePacking.exists_coordinate_refinement
    (fun g : Matrix (Fin 2) (Fin 2) ℝ => fun i j => g i j) F (by positivity : (0 : ℝ) < η / 4) hpatch
  have hb : BoundedCoordinatePacking.binCount η ((η : ℝ) / 4) ≤ 9 := by
    have hh := BoundedCoordinatePacking.binCount_le η.coe_nonneg (by positivity : (0 : ℝ) < η / 4)
    have he : 2 * (η : ℝ) / ((η : ℝ) / 4) + 1 = 9 := by field_simp; ring
    rw [he] at hh
    exact_mod_cast hh
  refine ⟨E, hE, ?_, ?_⟩
  · calc
      E.card ≤ F.card * BoundedCoordinatePacking.binCount η ((η : ℝ) / 4) ^ 4 := hcard
      _ ≤ F.card * 9 ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 4)
      _ = _ := by ring
  · intro g hg
    obtain ⟨e, he, hge⟩ := hclose g hg
    refine ⟨e, he, ?_⟩
    have hs (i j : Fin 2) : (g i j - e i j) ^ 2 < ((η : ℝ) / 4) ^ 2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr (hge i j)
    simp only [Fin.sum_univ_two]
    nlinarith [hs 0 0, hs 0 1, hs 1 0, hs 1 1]

theorem strict_cover_cost_le_externalCoveringNumber {A : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    {η : ℝ≥0} (hη : 0 < η) (hfin : Metric.externalCoveringNumber η A ≠ ⊤) {c d : ℝ≥0∞}
    (hbound : ∀ F : Finset (Matrix (Fin 2) (Fin 2) ℝ),
      (∀ g ∈ A, ∃ e ∈ F, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < (η : ℝ) ^ 2) →
        c ≤ d * (F.card : ℝ≥0∞)) :
    c ≤ 6561 * d * (Metric.externalCoveringNumber η A : ℝ≥0∞) := by
  obtain ⟨F, hF, hFcard⟩ := Metric.exists_finset_card_eq_externalCoveringNumber hfin
  obtain ⟨E, _, hEcard, hEcover⟩ := exists_strict_frobenius_refinement F hη hF
  have hcast : (E.card : ℝ≥0∞) ≤ 6561 * (F.card : ℝ≥0∞) := by exact_mod_cast hEcard
  have he : (F.card : ℝ≥0∞) = (Metric.externalCoveringNumber η A : ℝ≥0∞) := by
    exact_mod_cast hFcard
  calc
    c ≤ d * (E.card : ℝ≥0∞) := hbound E hEcover
    _ ≤ d * (6561 * (F.card : ℝ≥0∞)) := mul_le_mul' le_rfl hcast
    _ = _ := by rw [he]; ring

end TransposeFollowup
