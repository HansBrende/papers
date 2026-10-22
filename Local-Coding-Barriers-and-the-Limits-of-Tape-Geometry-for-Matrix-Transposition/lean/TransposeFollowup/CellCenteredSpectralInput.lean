import TransposeFollowup.CellCenteredVariance
import Mathlib.Analysis.Normed.Module.Normalize

/-! The actual normalized L2 class of the trimmed cell-centered indicator.
Its representative is supported in the unit interval almost everywhere and
has zero integral on each cell. No spectral-gap theorem is assumed here. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

noncomputable def cellCenteredLp (K : ℕ) (A : Set ℝ) (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1) : Lp ℝ 2 (volume : Measure ℝ) :=
  (cellCenteredIndicator_memLp hA hunit 2).toLp (cellCenteredIndicator K A)

theorem cellCenteredLp_coe {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1) :
    ⇑(cellCenteredLp K A hA hunit) =ᵐ[volume] cellCenteredIndicator K A :=
  MemLp.coeFn_toLp _

theorem cellCenteredLp_norm_sq {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1) :
    ‖cellCenteredLp K A hA hunit‖^2 = ∫ x,(cellCenteredIndicator K A x)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  exact integral_congr_ae ((cellCenteredLp_coe (K := K) hA hunit).mono
    (fun x hx => by simp only [hx]))

theorem cellCenteredLp_variance {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A ⊆ Icc (0:ℝ) 1) :
    ‖cellCenteredLp K A hA hunit‖^2 =
      volume.real A-(K:ℝ)*∑ i : Fin K,(volume.real (A∩gridCell i))^2 := by
  rw [cellCenteredLp_norm_sq hA hunit,cellCenteredIndicator_variance hK hA hunit]

noncomputable def normalizedCellCentered (K : ℕ) (A : Set ℝ) (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1) : Lp ℝ 2 (volume : Measure ℝ) :=
  NormedSpace.normalize (cellCenteredLp K A hA hunit)

theorem normalizedCellCentered_coe {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1) :
    ⇑(normalizedCellCentered K A hA hunit) =ᵐ[volume]
      fun x => ‖cellCenteredLp K A hA hunit‖⁻¹ * cellCenteredIndicator K A x := by
  unfold normalizedCellCentered NormedSpace.normalize
  filter_upwards [Lp.coeFn_smul ‖cellCenteredLp K A hA hunit‖⁻¹
    (cellCenteredLp K A hA hunit),cellCenteredLp_coe (K := K) hA hunit] with x hs hx
  simpa only [Pi.smul_apply,smul_eq_mul,hx] using hs

theorem normalizedCellCentered_norm {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1)
    (hvar : 0<∫ x,(cellCenteredIndicator K A x)^2) :
    ‖normalizedCellCentered K A hA hunit‖=1 := by
  apply NormedSpace.norm_normalize
  intro hz
  rw [← cellCenteredLp_norm_sq hA hunit,hz,norm_zero,zero_pow (by decide : 2≠0)] at hvar
  exact lt_irrefl _ hvar

theorem normalizedCellCentered_off_unit {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A ⊆ Icc (0:ℝ) 1) :
    ∀ᵐ x ∂volume,x∉Icc (0:ℝ) 1 → normalizedCellCentered K A hA hunit x=0 := by
  filter_upwards [normalizedCellCentered_coe hA hunit] with x hx
  intro hu
  rw [hx,cellCenteredIndicator_off_unit hunit hu,mul_zero]

theorem normalizedCellCentered_cell_integral {K : ℕ} {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A ⊆ Icc (0:ℝ) 1) (i : Fin K) :
    (∫ x in gridCell i,normalizedCellCentered K A hA hunit x)=0 := by
  calc
    _ = ∫ x in gridCell i,‖cellCenteredLp K A hA hunit‖⁻¹ * cellCenteredIndicator K A x :=
      setIntegral_congr_ae (gridCell_measurable i)
        ((normalizedCellCentered_coe hA hunit).mono (fun _ hx _ => hx))
    _ = 0 := by rw [integral_const_mul,cellCenteredIndicator_cell_integral hA hunit,mul_zero]

theorem gridTrim_normalized_off_cells {K : ℕ} {A : Set ℝ}
    (hA : MeasurableSet A) (B : Finset (Fin K)) :
    ∀ᵐ x ∂volume,x∉gridCells B →
      normalizedCellCentered K (gridTrim A B) (gridTrim_measurable hA B)
        (gridTrim_subset_unit A B) x=0 := by
  filter_upwards [normalizedCellCentered_coe (K := K) (gridTrim_measurable hA B)
    (gridTrim_subset_unit A B)] with x hx
  intro hb
  rw [hx,cellCenteredIndicator_gridTrim_off_cells A B hb,mul_zero]

theorem centralTrim_normalized_support {K m : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∀ᵐ x ∂volume,x∉Icc ((m:ℝ)/K) (1-(m:ℝ)/K) →
      normalizedCellCentered K (gridTrim A (centralCells K m))
        (gridTrim_measurable hA _) (gridTrim_subset_unit A _) x=0 := by
  filter_upwards [gridTrim_normalized_off_cells hA (centralCells K m)] with x hx
  exact fun hu => hx (fun hc => hu (centralCells_subset_interval hK hc))

theorem gridTrim_normalized_spectral_input {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A ⊆ Icc (0:ℝ) 1)
    (hM : 0<volume.real A) (hhalf : volume.real A ≤ 1/2) (B : Finset (Fin K))
    (delta : ℝ) (hdelta : 0 ≤ delta) (hd : delta<1)
    (hremoved : (Bᶜ.card:ℝ)/(K:ℝ)*(1+delta)<1)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    let f := normalizedCellCentered K (gridTrim A B) (gridTrim_measurable hA B)
      (gridTrim_subset_unit A B)
    ‖f‖=1 ∧ (∀ᵐ x ∂volume,x∉Icc (0:ℝ) 1 → f x=0) ∧
      ∀ i : Fin K,(∫ x in gridCell i,f x)=0 := by
  have hv := (gridTrim_variance_pos hK hA hunit hM hhalf B delta hdelta hd hremoved huniform).2
  exact ⟨normalizedCellCentered_norm _ _ hv,normalizedCellCentered_off_unit _ _,
    normalizedCellCentered_cell_integral _ _⟩

end TransposeFollowup
