import TransposeFollowup.ExpansionParameters
import TransposeFollowup.CellCenteredSpectralInput

/-! A measurable representative of the previously constructed normalized
L2 class, with its exact integral normalization and weighted correlation. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

noncomputable def normalizedCellFunction (K : ℕ) (A : Set ℝ) (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) : ℝ → ℝ :=
  fun x => ‖cellCenteredLp K A hA hunit‖⁻¹ * cellCenteredIndicator K A x

theorem normalizedCellFunction_coe {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) :
    ⇑(normalizedCellCentered K A hA hunit) =ᵐ[volume] normalizedCellFunction K A hA hunit :=
  normalizedCellCentered_coe hA hunit

theorem normalizedCellFunction_measurable {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) : Measurable (normalizedCellFunction K A hA hunit) :=
  measurable_const.mul (cellCenteredIndicator_measurable hA)

theorem normalizedCellFunction_square_integrable {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) :
    Integrable (fun x => (normalizedCellFunction K A hA hunit x)^2) volume := by
  simpa only [normalizedCellFunction,mul_pow] using
    (cellCenteredIndicator_memLp (K := K) hA hunit 2).integrable_sq.const_mul
      ((‖cellCenteredLp K A hA hunit‖⁻¹)^2)

theorem normalizedCellFunction_square_integral {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (hvar : 0<∫ x,(cellCenteredIndicator K A x)^2) :
    (∫ x,(normalizedCellFunction K A hA hunit x)^2)=1 := by
  have hn : ‖cellCenteredLp K A hA hunit‖≠0 := by
    intro hz
    rw [← cellCenteredLp_norm_sq hA hunit,hz] at hvar
    norm_num at hvar
  simp only [normalizedCellFunction,mul_pow]
  rw [integral_const_mul,← cellCenteredLp_norm_sq hA hunit]
  field_simp

theorem normalizedCellFunction_off_unit {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) {x : ℝ} (hx : x∉Icc (0:ℝ) 1) :
    normalizedCellFunction K A hA hunit x=0 := by
  simp only [normalizedCellFunction,cellCenteredIndicator_off_unit hunit hx,mul_zero]

theorem normalizedCellFunction_cell_integral {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (i : Fin K) :
    (∫ x in gridCell i,normalizedCellFunction K A hA hunit x)=0 := by
  unfold normalizedCellFunction
  rw [integral_const_mul,cellCenteredIndicator_cell_integral hA hunit,mul_zero]

theorem normalizedCellFunction_closed_cell_integral {K : ℕ} {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (i : Fin K) :
    (∫ x in Icc ((i.val:ℝ)/K) (((i.val:ℝ)+1)/K),normalizedCellFunction K A hA hunit x)=0 := by
  rw [integral_Icc_eq_integral_Ioo,← gridCell_eq_Ioo]
  exact normalizedCellFunction_cell_integral hA hunit i

namespace RationalUnitMobius

theorem normalizedCellFunction_correlation (G : RationalUnitMobius) {K : ℕ} {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (hvar : 0<∫ x,(cellCenteredIndicator K A x)^2)
    (hcorr : (3/4)*(∫ x,(cellCenteredIndicator K A x)^2) ≤
      ∫ x in Icc (0:ℝ) 1,G.whole.weightedPullback (cellCenteredIndicator K A) x*
        cellCenteredIndicator K A x) :
    3/4 ≤ ∫ x in Icc (0:ℝ) 1,
      G.whole.weightedPullback (normalizedCellFunction K A hA hunit) x*
        normalizedCellFunction K A hA hunit x := by
  let a := ‖cellCenteredLp K A hA hunit‖⁻¹
  have hn : ‖cellCenteredLp K A hA hunit‖≠0 := by
    intro hz
    rw [← cellCenteredLp_norm_sq hA hunit,hz] at hvar
    norm_num at hvar
  have hid : (fun x => G.whole.weightedPullback (normalizedCellFunction K A hA hunit) x*
      normalizedCellFunction K A hA hunit x)=
      fun x => a^2*(G.whole.weightedPullback (cellCenteredIndicator K A) x*cellCenteredIndicator K A x) := by
    funext x
    dsimp [a,normalizedCellFunction,RationalMobius.weightedPullback]
    ring
  rw [hid,integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hcorr (sq_nonneg a)
  have heq : a^2*((3/4)*(∫ x,(cellCenteredIndicator K A x)^2))=3/4 := by
    rw [← cellCenteredLp_norm_sq hA hunit]
    dsimp [a]
    field_simp
  rwa [heq] at hb

end RationalUnitMobius
end TransposeFollowup
