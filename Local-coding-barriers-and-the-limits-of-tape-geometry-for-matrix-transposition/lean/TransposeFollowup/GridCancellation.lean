import TransposeFollowup.GridCellMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic

/-! Cancellation against tests of bounded cell oscillation. The finite set of
grid endpoints is removed only through its proved zero Lebesgue measure. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false

theorem gridCells_univ_ae_unit {K : ℕ} (hK : 0 < K) :
    (⋃ i : Fin K, gridCell i) =ᵐ[volume] Icc (0 : ℝ) 1 := by
  apply ae_iff.mpr
  apply measure_mono_null ?_ (gridBoundary_volume K)
  intro x hx
  by_contra hb
  apply hx
  apply propext
  constructor
  · intro hi
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi
    exact gridCell_subset_unit i hi
  · intro hu
    obtain ⟨i, hi⟩ := exists_gridCell_of_not_boundary hK hu hb
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

theorem integral_unit_eq_sum_gridCells {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {K : ℕ} (hK : 0 < K) {f : ℝ → E}
    (hf : IntegrableOn f (Icc (0 : ℝ) 1)) :
    (∫ x in Icc (0 : ℝ) 1, f x) = ∑ i : Fin K, ∫ x in gridCell i, f x := by
  rw [← setIntegral_congr_set (gridCells_univ_ae_unit hK)]
  exact integral_iUnion_fintype (fun i => gridCell_measurable i)
    gridCell_pairwise_disjoint (fun i => hf.mono_set (gridCell_subset_unit i))

theorem integral_eq_sum_gridCells {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {K : ℕ} (hK : 0 < K) {f : ℝ → E}
    (hf : Integrable f) (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∫ x, f x) = ∑ i : Fin K, ∫ x in gridCell i, f x := by
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hsupport]
  exact integral_unit_eq_sum_gridCells hK hf.integrableOn

theorem gridCell_pairing_sub_const {K : ℕ} {f φ : ℝ → ℂ}
    (hf : Integrable f) (hpair : Integrable (fun x => f x * φ x))
    (i : Fin K) (hzero : (∫ x in gridCell i, f x) = 0) (a : ℂ) :
    (∫ x in gridCell i, f x * φ x) = ∫ x in gridCell i, f x * (φ x - a) := by
  simp_rw [mul_sub]
  rw [integral_sub hpair.integrableOn (hf.mul_const a).integrableOn,
    integral_mul_const, hzero, zero_mul, sub_zero]

/-- Only the oscillation on each cell matters; different constants may be
subtracted on different cells without changing the pairing. -/
theorem norm_pairing_le_cell_oscillation {K : ℕ} (hK : 0 < K) {f φ : ℝ → ℂ}
    (hf : Integrable f) (hpair : Integrable (fun x => f x * φ x))
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in gridCell i, f x) = 0)
    (a : Fin K → ℂ) (B : ℝ)
    (hosc : ∀ i : Fin K, ∀ x ∈ gridCell i, ‖φ x - a i‖ ≤ B) :
    ‖∫ x, f x * φ x‖ ≤ B * ∫ x, ‖f x‖ := by
  have hpSupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x * φ x = 0 := by
    filter_upwards [hsupport] with x hx hu
    rw [hx hu, zero_mul]
  have hnSupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → ‖f x‖ = 0 := by
    filter_upwards [hsupport] with x hx hu
    rw [hx hu, norm_zero]
  rw [integral_eq_sum_gridCells hK hpair hpSupport]
  calc
    _ ≤ ∑ i : Fin K, ‖∫ x in gridCell i, f x * φ x‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin K, B * ∫ x in gridCell i, ‖f x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [gridCell_pairing_sub_const hf hpair i (hzero i) (a i), ← integral_const_mul]
      apply norm_integral_le_of_norm_le ((hf.norm.const_mul B).integrableOn)
      filter_upwards [ae_restrict_mem (gridCell_measurable i)] with x hx
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hosc i x hx) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = B * ∫ x, ‖f x‖ := by
      rw [← Finset.mul_sum, integral_eq_sum_gridCells hK hf.norm hnSupport]

/-- A Lipschitz test has oscillation at most L/K on a grid cell. -/
theorem norm_pairing_le_lipschitz_grid {K : ℕ} (hK : 0 < K) {f φ : ℝ → ℂ}
    (hf : Integrable f) (hpair : Integrable (fun x => f x * φ x))
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (hzero : ∀ i : Fin K, (∫ x in gridCell i, f x) = 0)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ x y : ℝ, ‖φ x - φ y‖ ≤ L * |x - y|) :
    ‖∫ x, f x * φ x‖ ≤ (L / K) * ∫ x, ‖f x‖ := by
  apply norm_pairing_le_cell_oscillation hK hf hpair hsupport hzero
    (fun i => φ ((i.val : ℝ) / K)) (L / K)
  intro i x hx
  rw [gridCell_eq_Ioo] at hx
  calc
    _ ≤ L * |x - (i.val : ℝ) / K| := hLip _ _
    _ ≤ L * (1 / K) := by
      apply mul_le_mul_of_nonneg_left _ hL
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      have he : ((i.val : ℝ) + 1) / K - (i.val : ℝ) / K = 1 / K := by ring
      linarith [hx.2]
    _ = L / K := by ring

end TransposeFollowup
