import TransposeFollowup.FrobeniusCoverTransfer
import TransposeFollowup.ExternalCoverAttainment

/-! A finite separated sample of a bounded matrix set retains its native
covering complexity up to a fixed four-dimensional refinement constant. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ

theorem exists_separated_matrix_sample {A : Set RMat} {B : ℝ} {η : ℝ≥0}
    (hB : 0 ≤ B) (hη : 0 < η) (hAn : A.Nonempty)
    (hA : ∀ x ∈ A, ∀ i j, |x i j| ≤ B) :
    ∃ F : Finset RMat, F.Nonempty ∧ (F : Set RMat) ⊆ A ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → 2 * (η : ℝ) < dist x y) ∧
      Metric.externalCoveringNumber η A ≠ ⊤ ∧
      (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal ≤ 6561 * (F.card : ℝ) := by
  have hfin := finite_coveringNumber_of_entry_bound hB hη hA
  have hpack : Metric.packingNumber (2 * η) A ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (Metric.packingNumber_two_mul_le_externalCoveringNumber η A)
  let Z := Metric.maximalSeparatedSet (2 * η) A
  have hZfin : Z.Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  have hcover : Metric.IsCover (2 * η) A Z := Metric.isCover_maximalSeparatedSet hpack
  let F := hZfin.toFinset
  have hpatch : ∀ x ∈ A, ∃ c ∈ F, ∀ i j, |x i j - c i j| ≤ 2 * (η : ℝ) := by
    intro x hx
    obtain ⟨c, hc, hd⟩ := hcover hx
    have hdist : dist x c ≤ ((2 * η : ℝ≥0) : ℝ) := by exact_mod_cast edist_le_coe.mp hd
    refine ⟨c, hZfin.mem_toFinset.mpr hc, fun i j => ?_⟩
    exact (entry_error_le_frobenius_dist x c i j).trans (by simpa using hdist)
  obtain ⟨_, hbound⟩ := coveringNumber_le_coordinate_patches F
    (by positivity : 0 ≤ 2 * (η : ℝ)) hη hpatch
  have hcoeff : (4 * (2 * (η : ℝ)) / (η : ℝ) + 1) ^ 4 = 6561 := by
    have hηR : 0 < (η : ℝ) := hη
    field_simp
    ring
  rw [hcoeff] at hbound
  refine ⟨F, hZfin.toFinset_nonempty.mpr (hcover.nonempty hAn), ?_, ?_, hfin, hbound⟩
  · intro x hx
    exact Metric.maximalSeparatedSet_subset (hZfin.mem_toFinset.mp hx)
  · intro x hx y hy hne
    have hh := Metric.isSeparated_maximalSeparatedSet (ε := 2 * η) (A := A)
      (hZfin.mem_toFinset.mp hx) (hZfin.mem_toFinset.mp hy) hne
    have hn : (2 * η : ℝ≥0) < nndist x y :=
      ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hh)
    have hr : ((2 * η : ℝ≥0) : ℝ) < dist x y := by exact_mod_cast hn
    simpa using hr

theorem separated_matrix_card_le_coveringNumber {A : Set RMat} (F : Finset RMat)
    {η : ℝ≥0} (hFA : (F : Set RMat) ⊆ A)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 2 * (η : ℝ) < dist x y)
    (hfin : Metric.externalCoveringNumber η A ≠ ⊤) :
    (F.card : ℝ) ≤ (Metric.externalCoveringNumber η A : ℝ≥0∞).toReal := by
  have hs : Metric.IsSeparated (2 * η) (F : Set RMat) := by
    intro x hx y hy hne
    have hn : (2 * η : ℝ≥0) < nndist x y := by exact_mod_cast hsep x hx y hy hne
    simpa only [edist_nndist, ENNReal.coe_mul, ENNReal.coe_ofNat] using ENNReal.coe_lt_coe.mpr hn
  have hnum : (F.card : ℕ∞) ≤ Metric.externalCoveringNumber η A := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using
      (hs.encard_le_packingNumber hFA).trans (Metric.packingNumber_two_mul_le_externalCoveringNumber η A)
  have hnumR : (F.card : ℝ≥0∞) ≤ Metric.externalCoveringNumber η A := by exact_mod_cast hnum
  simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono
    (ENat.toENNReal_ne_top.mpr hfin) hnumR

end TransposeFollowup.SL2Projection
