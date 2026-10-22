import TransposeFollowup.GridTrimming
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual squared-integral error of cell-mean centering after trimming.
Deleted cells contribute their full squared global mean. This contribution
is explicit in the bound and does not disappear with cell uniformity. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

noncomputable def gridStep {K : ℕ} (v : Fin K → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin K,(gridCell i).indicator (fun _ => v i) x

theorem gridStep_on_cell {K : ℕ} (v : Fin K → ℝ) (i : Fin K) {x : ℝ}
    (hx : x∈gridCell i) : gridStep v x=v i := by
  unfold gridStep
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    apply Set.indicator_of_notMem
    exact fun hj => Set.disjoint_left.mp (gridCell_pairwise_disjoint hji) hj hx
  · simp

theorem gridStep_off_cells {K : ℕ} (v : Fin K → ℝ) {x : ℝ}
    (hx : ∀ i : Fin K,x∉gridCell i) : gridStep v x=0 := by
  unfold gridStep
  apply Finset.sum_eq_zero
  intro i _
  exact Set.indicator_of_notMem (hx i) _

theorem gridStep_sub {K : ℕ} (v w : Fin K → ℝ) (x : ℝ) :
    gridStep (fun i => v i-w i) x=gridStep v x-gridStep w x := by
  by_cases hx : ∃ i : Fin K,x∈gridCell i
  · obtain ⟨i,hi⟩:=hx
    rw [gridStep_on_cell _ i hi,gridStep_on_cell _ i hi,gridStep_on_cell _ i hi]
  · have hn : ∀ i : Fin K,x∉gridCell i:=fun i hi => hx ⟨i,hi⟩
    rw [gridStep_off_cells _ hn,gridStep_off_cells _ hn,gridStep_off_cells _ hn,sub_self]

theorem gridStep_square {K : ℕ} (v : Fin K → ℝ) (x : ℝ) :
    (gridStep v x)^2=gridStep (fun i => (v i)^2) x := by
  by_cases hx : ∃ i : Fin K,x∈gridCell i
  · obtain ⟨i,hi⟩:=hx
    rw [gridStep_on_cell _ i hi,gridStep_on_cell _ i hi]
  · have hn : ∀ i : Fin K,x∉gridCell i:=fun i hi => hx ⟨i,hi⟩
    rw [gridStep_off_cells _ hn,gridStep_off_cells _ hn]
    norm_num

theorem gridStep_integrable {K : ℕ} (v : Fin K → ℝ) : Integrable (gridStep v) volume := by
  apply integrable_finsetSum Finset.univ
  intro i _
  exact (integrableOn_const (unit_subset_volume_ne_top (gridCell_subset_unit i))).integrable_indicator
    (gridCell_measurable i)

theorem gridStep_integral {K : ℕ} (v : Fin K → ℝ) :
    (∫ x,gridStep v x)= (∑ i : Fin K,v i)/(K:ℝ) := by
  unfold gridStep
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (gridCell_measurable _),smul_eq_mul,gridCell_volume_real]
    rw [← Finset.mul_sum]
    ring
  · intro i _
    exact (integrableOn_const (unit_subset_volume_ne_top (gridCell_subset_unit i))).integrable_indicator
      (gridCell_measurable i)

theorem gridStep_square_integral {K : ℕ} (v : Fin K → ℝ) :
    (∫ x,(gridStep v x)^2)=(∑ i : Fin K,(v i)^2)/(K:ℝ) := by
  simp_rw [gridStep_square]
  exact gridStep_integral _

theorem gridStep_const_ae {K : ℕ} (hK : 0<K) (a : ℝ) :
    (fun x => gridStep (fun _ : Fin K => a) x)=ᵐ[volume]
      (Icc (0:ℝ) 1).indicator (fun _ => a) := by
  apply ae_iff.mpr
  apply measure_mono_null ?_ (gridBoundary_volume K)
  intro x hx
  by_contra hb
  apply hx
  change gridStep (fun _ : Fin K => a) x=(Icc (0:ℝ) 1).indicator (fun _ => a) x
  by_cases hu : x∈Icc (0:ℝ) 1
  · obtain ⟨i,hi⟩:=exists_gridCell_of_not_boundary hK hu hb
    rw [gridStep_on_cell _ i hi,Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    exact gridStep_off_cells _ (fun i hi => hu (gridCell_subset_unit i hi))

noncomputable def centeredIndicator (A : Set ℝ) (x : ℝ) : ℝ :=
  A.indicator (fun _ => 1) x-(Icc (0:ℝ) 1).indicator (fun _ => volume.real A) x

noncomputable def cellCenteredIndicator (K : ℕ) (A : Set ℝ) (x : ℝ) : ℝ :=
  A.indicator (fun _ => 1) x-gridStep (fun i : Fin K => (K:ℝ)*volume.real (A∩gridCell i)) x

theorem cellCenteredIndicator_cell_integral {K : ℕ} {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (i : Fin K) :
    (∫ x in gridCell i,cellCenteredIndicator K A x)=0 := by
  have hInd : Integrable (A.indicator (fun _ : ℝ => (1:ℝ))) volume :=
    (integrableOn_const (unit_subset_volume_ne_top hunit)).integrable_indicator hA
  have hStep := gridStep_integrable (fun j : Fin K => (K:ℝ)*volume.real (A∩gridCell j))
  unfold cellCenteredIndicator
  rw [integral_sub hInd.integrableOn hStep.integrableOn]
  have hs : (∫ x in gridCell i,gridStep (fun j : Fin K => (K:ℝ)*volume.real (A∩gridCell j)) x)=
      (∫ _x in gridCell i,(K:ℝ)*volume.real (A∩gridCell i)) :=
    setIntegral_congr_fun (gridCell_measurable i) (fun _ hx => gridStep_on_cell _ i hx)
  rw [hs,integral_indicator_const 1 hA,measureReal_restrict_apply hA,setIntegral_const,
    smul_eq_mul,smul_eq_mul,gridCell_volume_real]
  have hk : (K:ℝ)≠0:=by exact_mod_cast (show K≠0 by have := i.isLt;omega)
  field_simp
  ring

theorem centering_error_ae {K : ℕ} (hK : 0<K) (A : Set ℝ) :
    (fun x => centeredIndicator A x-cellCenteredIndicator K A x)=ᵐ[volume]
      gridStep (fun i : Fin K => (K:ℝ)*volume.real (A∩gridCell i)-volume.real A) := by
  filter_upwards [gridStep_const_ae hK (volume.real A)] with x hx
  unfold centeredIndicator cellCenteredIndicator
  rw [← hx,gridStep_sub]
  ring

theorem centering_error_square_integral {K : ℕ} (hK : 0<K) (A : Set ℝ) :
    (∫ x,(centeredIndicator A x-cellCenteredIndicator K A x)^2)=
      (∑ i : Fin K,((K:ℝ)*volume.real (A∩gridCell i)-volume.real A)^2)/(K:ℝ) := by
  calc
    _ = ∫ x,(gridStep (fun i : Fin K => (K:ℝ)*volume.real (A∩gridCell i)-volume.real A) x)^2 :=
      integral_congr_ae ((centering_error_ae hK A).mono (fun _ h => congrArg (fun z : ℝ => z^2) h))
    _ = _ := gridStep_square_integral _

theorem centering_error_square_integrable {K : ℕ} (hK : 0<K) (A : Set ℝ) :
    Integrable (fun x => (centeredIndicator A x-cellCenteredIndicator K A x)^2) volume := by
  have ha : (fun x => (centeredIndicator A x-cellCenteredIndicator K A x)^2)=ᵐ[volume]
      gridStep (fun i : Fin K => ((K:ℝ)*volume.real (A∩gridCell i)-volume.real A)^2) := by
    filter_upwards [centering_error_ae hK A] with x hx
    rw [hx,gridStep_square]
  exact (gridStep_integrable _).congr ha.symm

/-- Retained cells pay the original uniformity error plus lost mass.
Every removed cell additionally pays the square of the trimmed mean. -/
theorem gridTrim_projection_error {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hunit : A⊆Icc (0:ℝ) 1) (B : Finset (Fin K)) (delta : ℝ) (hdelta : 0 ≤ delta)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    (∫ x,(centeredIndicator (gridTrim A B) x-cellCenteredIndicator K (gridTrim A B) x)^2) ≤
      (delta*volume.real A+(volume.real A-volume.real (gridTrim A B)))^2+
        (Bᶜ.card:ℝ)/(K:ℝ)*(volume.real (gridTrim A B))^2 := by
  let T := gridTrim A B
  let C := delta*volume.real A+(volume.real A-volume.real T)
  have hLoss : 0 ≤ volume.real A-volume.real T:=gridTrim_loss_nonneg hunit B
  have hC : 0 ≤ C:=add_nonneg (mul_nonneg hdelta measureReal_nonneg) hLoss
  have hret : ∀ i∈B,((K:ℝ)*volume.real (T∩gridCell i)-volume.real T)^2 ≤ C^2 := by
    intro i hi
    have hc : T∩gridCell i=A∩gridCell i := by
      change gridTrim A B∩gridCell i=_
      simp only [gridTrim_inter_cell,hi,ite_true]
    rw [hc]
    have hu:=abs_le.mp (huniform i)
    apply sq_le_sq'
    · dsimp [C]
      linarith
    · dsimp [C]
      linarith
  have hdel : ∀ i∈Bᶜ,((K:ℝ)*volume.real (T∩gridCell i)-volume.real T)^2=(volume.real T)^2 := by
    intro i hi
    have hc : T∩gridCell i=∅ := by
      change gridTrim A B∩gridCell i=_
      simp only [gridTrim_inter_cell,Finset.mem_compl.mp hi,ite_false]
    rw [hc]
    simp
  have hs : (∑ i : Fin K,((K:ℝ)*volume.real (T∩gridCell i)-volume.real T)^2) ≤
      (B.card:ℝ)*C^2+(Bᶜ.card:ℝ)*(volume.real T)^2 := by
    rw [← Finset.sum_add_sum_compl B]
    apply add_le_add
    · exact (Finset.sum_le_sum hret).trans_eq (by simp)
    · exact le_of_eq ((Finset.sum_congr rfl hdel).trans (by simp))
  have hb : (B.card:ℝ) ≤ K:=by
    exact_mod_cast (show B.card ≤ K by simpa only [Fintype.card_fin] using Finset.card_le_univ B)
  have hs' : (∑ i : Fin K,((K:ℝ)*volume.real (T∩gridCell i)-volume.real T)^2) ≤
      (K:ℝ)*C^2+(Bᶜ.card:ℝ)*(volume.real T)^2 :=
    hs.trans (add_le_add (mul_le_mul_of_nonneg_right hb (sq_nonneg C)) le_rfl)
  rw [centering_error_square_integral hK]
  have hk : (0:ℝ)<K:=by exact_mod_cast hK
  apply (div_le_iff₀ hk).mpr
  change _ ≤ (C^2+(Bᶜ.card:ℝ)/(K:ℝ)*(volume.real T)^2)*(K:ℝ)
  calc
    _ ≤ (K:ℝ)*C^2+(Bᶜ.card:ℝ)*(volume.real T)^2 := hs'
    _ = _ := by field_simp

theorem gridTrim_projection_error_explicit {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (B : Finset (Fin K))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    (∫ x,(centeredIndicator (gridTrim A B) x-cellCenteredIndicator K (gridTrim A B) x)^2) ≤
      ((delta+(Bᶜ.card:ℝ)/(K:ℝ)*(1+delta))^2+(Bᶜ.card:ℝ)/(K:ℝ))*(volume.real A)^2 := by
  let theta : ℝ := (Bᶜ.card:ℝ)/(K:ℝ)
  let T := gridTrim A B
  have ht : 0 ≤ theta:=by positivity
  have hM : 0 ≤ volume.real A:=measureReal_nonneg
  have hMt : 0 ≤ volume.real T:=measureReal_nonneg
  have hMtM : volume.real T ≤ volume.real A:=
    measureReal_mono (gridTrim_subset A B) (unit_subset_volume_ne_top hunit)
  have hL : volume.real A-volume.real T ≤ theta*(1+delta)*volume.real A:=
    gridTrim_loss_bound hK hA hunit delta huniform B
  have hC : 0 ≤ delta*volume.real A+(volume.real A-volume.real T):=
    add_nonneg (mul_nonneg hdelta hM) (sub_nonneg.mpr hMtM)
  have hCsq : (delta*volume.real A+(volume.real A-volume.real T))^2 ≤
      ((delta+theta*(1+delta))*volume.real A)^2 := by
    apply (sq_le_sq₀ hC (by positivity)).mpr
    nlinarith
  have hMsq : (volume.real T)^2 ≤ (volume.real A)^2:=(sq_le_sq₀ hMt hM).mpr hMtM
  calc
    _ ≤ (delta*volume.real A+(volume.real A-volume.real T))^2+theta*(volume.real T)^2 :=
      gridTrim_projection_error hK hunit B delta hdelta huniform
    _ ≤ ((delta+theta*(1+delta))*volume.real A)^2+theta*(volume.real A)^2 :=
      add_le_add hCsq (mul_le_mul_of_nonneg_left hMsq ht)
    _ = _ := by dsimp [theta];ring

namespace RationalUnitMobius

theorem augmented_central_projection_error {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let delta : ℝ := (K:ℝ)*((K-1:ℕ):ℝ)*sigma
    let theta : ℝ := 2*(m:ℝ)/(K:ℝ)
    (∫ x,(centeredIndicator (gridTrim A (centralCells K m)) x-
      cellCenteredIndicator K (gridTrim A (centralCells K m)) x)^2) ≤
      ((delta+theta*(1+delta))^2+theta)*(volume.real A)^2 := by
  dsimp only
  have h:=gridTrim_projection_error_explicit (by omega : 0<K) hA hunit (centralCells K m)
    ((K:ℝ)*((K-1:ℕ):ℝ)*sigma) (by positivity) (by
      intro i
      simpa only [mul_assoc] using augmented_cell_uniformity F hK hA hunit sigma hsigma hsmall i)
  simpa only [centralCells_compl_card hm,Nat.cast_mul,Nat.cast_ofNat] using h

end RationalUnitMobius
end TransposeFollowup
