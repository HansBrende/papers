import TransposeFollowup.GridProjectionError
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Membership in L2 and exact variance of the cell-centered indicator.
The trimmed variance stays positive when uniformity and deleted-cell mass
are small and the original set has positive measure at most one half. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem gridStep_memLp {K : ℕ} (p : ℝ≥0∞) (v : Fin K → ℝ) : MemLp (gridStep v) p volume := by
  apply memLp_finsetSum Finset.univ
  intro i _
  exact memLp_indicator_const p (gridCell_measurable i) (v i)
    (Or.inr (unit_subset_volume_ne_top (gridCell_subset_unit i)))

theorem cellCenteredIndicator_memLp {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (p : ℝ≥0∞) : MemLp (cellCenteredIndicator K A) p volume :=
  (memLp_indicator_const p hA (1:ℝ) (Or.inr (unit_subset_volume_ne_top hunit))).sub
    (gridStep_memLp p _)

theorem cellCenteredIndicator_off_unit {K : ℕ} {A : Set ℝ} (hunit : A⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∉Icc (0:ℝ) 1) : cellCenteredIndicator K A x=0 := by
  have ha : x∉A:=fun h => hx (hunit h)
  unfold cellCenteredIndicator
  rw [Set.indicator_of_notMem ha,gridStep_off_cells _ (fun i hi => hx (gridCell_subset_unit i hi))]
  simp

theorem cellCenteredIndicator_gridTrim_off_cells {K : ℕ} (A : Set ℝ)
    (B : Finset (Fin K)) {x : ℝ} (hx : x∉gridCells B) :
    cellCenteredIndicator K (gridTrim A B) x=0 := by
  have ht : x∉gridTrim A B := fun h => hx h.2
  unfold cellCenteredIndicator
  rw [Set.indicator_of_notMem ht,zero_sub,neg_eq_zero]
  unfold gridStep
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i∈B
  · apply Set.indicator_of_notMem
    exact fun h => hx (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,h⟩⟩)
  · change (gridCell i).indicator (fun _ => (K:ℝ)*volume.real (gridTrim A B∩gridCell i)) x=0
    rw [gridTrim_inter_cell]
    simp only [hi,ite_false,measureReal_empty,mul_zero,Set.indicator_zero]

theorem indicator_gridStep_product {K : ℕ} (A : Set ℝ) (v : Fin K → ℝ) (x : ℝ) :
    A.indicator (fun _ => (1:ℝ)) x*gridStep v x=
      ∑ i : Fin K,(A∩gridCell i).indicator (fun _ => v i) x := by
  unfold gridStep
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : x∈A <;> by_cases hi : x∈gridCell i <;> simp [ha,hi]

theorem indicator_gridStep_integral {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A)
    (v : Fin K → ℝ) :
    (∫ x,A.indicator (fun _ => (1:ℝ)) x*gridStep v x)=
      ∑ i : Fin K,volume.real (A∩gridCell i)*v i := by
  simp_rw [indicator_gridStep_product]
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (hA.inter (gridCell_measurable _)),smul_eq_mul]
  · intro i _
    exact (integrableOn_const (unit_subset_volume_ne_top
      (inter_subset_right.trans (gridCell_subset_unit i)))).integrable_indicator
      (hA.inter (gridCell_measurable i))

theorem cellCenteredIndicator_variance {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) :
    (∫ x,(cellCenteredIndicator K A x)^2)=
      volume.real A-(K:ℝ)*∑ i : Fin K,(volume.real (A∩gridCell i))^2 := by
  let u : ℝ → ℝ := A.indicator (fun _ => 1)
  let v : ℝ → ℝ := gridStep (fun i : Fin K => (K:ℝ)*volume.real (A∩gridCell i))
  have hu : Integrable u volume:=
    (integrableOn_const (unit_subset_volume_ne_top hunit)).integrable_indicator hA
  have hu2 : MemLp u 2 volume:=memLp_indicator_const 2 hA (1:ℝ)
    (Or.inr (unit_subset_volume_ne_top hunit))
  have hv2 : MemLp v 2 volume:=gridStep_memLp 2 _
  have huv : Integrable (fun x => u x*v x) volume:=hu2.integrable_mul hv2
  have hvv : Integrable (fun x => (v x)^2) volume:=hv2.integrable_sq
  have hpoint : (fun x => (cellCenteredIndicator K A x)^2)=
      fun x => u x-2*(u x*v x)+(v x)^2 := by
    funext x
    have hs : (u x)^2=u x:=by dsimp [u];by_cases hx : x∈A <;> simp [hx]
    change (u x-v x)^2=_
    nlinarith only [hs]
  rw [hpoint]
  rw [integral_add (f := fun x => u x-2*(u x*v x)) (g := fun x => (v x)^2)
    (hu.sub (huv.const_mul 2)) hvv]
  rw [integral_sub (f := u) (g := fun x => 2*(u x*v x)) hu (huv.const_mul 2),
    integral_const_mul]
  change (∫ x,A.indicator (fun _ => (1:ℝ)) x)-
    2*(∫ x,A.indicator (fun _ => (1:ℝ)) x*gridStep
      (fun i : Fin K => (K:ℝ)*volume.real (A∩gridCell i)) x)+
    (∫ x,(gridStep (fun i : Fin K => (K:ℝ)*volume.real (A∩gridCell i)) x)^2)=_
  rw [integral_indicator_const 1 hA,smul_eq_mul,mul_one,indicator_gridStep_integral hA,
    gridStep_square_integral]
  have hc : (∑ i : Fin K,volume.real (A∩gridCell i)*((K:ℝ)*volume.real (A∩gridCell i)))=
      (K:ℝ)*∑ i : Fin K,(volume.real (A∩gridCell i))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : (∑ i : Fin K,((K:ℝ)*volume.real (A∩gridCell i))^2)=
      (K:ℝ)^2*∑ i : Fin K,(volume.real (A∩gridCell i))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc,hs]
  have hk : (K:ℝ)≠0:=by exact_mod_cast hK.ne'
  field_simp
  ring

theorem cellCenteredIndicator_variance_lower {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (q : ℝ)
    (hcap : ∀ i : Fin K,(K:ℝ)*volume.real (A∩gridCell i) ≤ q) :
    (1-q)*volume.real A ≤ ∫ x,(cellCenteredIndicator K A x)^2 := by
  rw [cellCenteredIndicator_variance hK hA hunit]
  have hsum : (∑ i : Fin K,volume.real (A∩gridCell i))=volume.real A := by
    simp_rw [← gridMass_eq]
    simpa only [Fin.sum_univ_eq_sum_range] using gridMass_sum hK hA hunit
  have hb : ∑ i : Fin K,(K:ℝ)*(volume.real (A∩gridCell i))^2 ≤
      ∑ i : Fin K,q*volume.real (A∩gridCell i) := by
    apply Finset.sum_le_sum
    intro i _
    have h:=mul_le_mul_of_nonneg_right (hcap i) (measureReal_nonneg : 0 ≤ volume.real (A∩gridCell i))
    nlinarith only [h]
  rw [← Finset.mul_sum,← Finset.mul_sum,hsum] at hb
  nlinarith only [hb]

theorem gridTrim_cell_cap {K : ℕ} (A : Set ℝ) (B : Finset (Fin K)) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (i : Fin K) : (K:ℝ)*volume.real (gridTrim A B∩gridCell i) ≤ (1+delta)*volume.real A := by
  rw [gridTrim_inter_cell]
  by_cases hi : i∈B
  · simp only [hi,ite_true]
    have h:=(abs_le.mp (huniform i)).2
    linarith
  · simp only [hi,ite_false,measureReal_empty,mul_zero]
    positivity

theorem gridTrim_variance_lower {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (B : Finset (Fin K)) (delta : ℝ) (hdelta : 0 ≤ delta)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    (1-(1+delta)*volume.real A)*volume.real (gridTrim A B) ≤
      ∫ x,(cellCenteredIndicator K (gridTrim A B) x)^2 :=
  cellCenteredIndicator_variance_lower hK (gridTrim_measurable hA B) (gridTrim_subset_unit A B)
    ((1+delta)*volume.real A) (gridTrim_cell_cap A B delta hdelta huniform)

theorem gridTrim_variance_pos {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (hM : 0<volume.real A) (hhalf : volume.real A ≤ 1/2) (B : Finset (Fin K))
    (delta : ℝ) (hdelta : 0 ≤ delta) (hd : delta<1)
    (hremoved : (Bᶜ.card:ℝ)/(K:ℝ)*(1+delta)<1)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    0<volume.real (gridTrim A B) ∧ 0<∫ x,(cellCenteredIndicator K (gridTrim A B) x)^2 := by
  have hl:=gridTrim_loss_bound hK hA hunit delta huniform B
  have hr:=mul_pos (sub_pos.mpr hremoved) hM
  have hT : 0<volume.real (gridTrim A B):=by nlinarith only [hl,hr]
  have hcap : (1+delta)*volume.real A<1 := calc
    _ ≤ (1+delta)*(1/2) := mul_le_mul_of_nonneg_left hhalf (by linarith)
    _ < 1 := by linarith
  exact ⟨hT,(mul_pos (sub_pos.mpr hcap) hT).trans_le
    (gridTrim_variance_lower hK hA B delta hdelta huniform)⟩

theorem gridTrim_small_projection_error {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (hhalf : volume.real A ≤ 1/2) (B : Finset (Fin K)) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hd : delta ≤ 1/100)
    (hremoved : (Bᶜ.card:ℝ)/(K:ℝ) ≤ 1/200)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    49/100*volume.real A ≤ (∫ x,(cellCenteredIndicator K (gridTrim A B) x)^2) ∧
    (∫ x,(centeredIndicator (gridTrim A B) x-cellCenteredIndicator K (gridTrim A B) x)^2) ≤
      1/100*(∫ x,(cellCenteredIndicator K (gridTrim A B) x)^2) := by
  let M := volume.real A
  let T := volume.real (gridTrim A B)
  let theta := (Bᶜ.card:ℝ)/(K:ℝ)
  have hM : 0 ≤ M := measureReal_nonneg
  have hT : 0 ≤ T := measureReal_nonneg
  have ht : 0 ≤ theta := by dsimp [theta]; positivity
  have hd1 : 1+delta ≤ (101/100:ℝ) := by linarith
  have htd : theta*(1+delta) ≤ (1/100:ℝ) := by
    have h := mul_le_mul hremoved hd1 (by linarith : 0 ≤ 1+delta) (by norm_num : (0:ℝ) ≤ 1/200)
    change theta*(1+delta) ≤ _ at h
    linarith
  have hretained : 99/100*M ≤ T := by
    have hl := gridTrim_loss_bound hK hA hunit delta huniform B
    have hm := mul_le_mul_of_nonneg_right htd hM
    change M-T ≤ theta*(1+delta)*M at hl
    linarith
  have hcap : (1+delta)*M ≤ (101/200:ℝ) := by
    have h := mul_le_mul hd1 hhalf hM (by norm_num : (0:ℝ) ≤ 101/100)
    change (1+delta)*M ≤ _ at h
    linarith
  have hv := gridTrim_variance_lower hK hA B delta hdelta huniform
  have hprod := mul_le_mul_of_nonneg_right
    (show (99/200:ℝ) ≤ 1-(1+delta)*M by linarith) hT
  change (1-(1+delta)*M)*T ≤ _ at hv
  have hvar : 49/100*M ≤ ∫ x,(cellCenteredIndicator K (gridTrim A B) x)^2 := by
    nlinarith only [hv,hprod,hretained,hM]
  refine ⟨hvar,?_⟩
  have hb0 : 0 ≤ delta+theta*(1+delta) := by positivity
  have hb : delta+theta*(1+delta) ≤ (1/50:ℝ) := by linarith
  have hbsq := (sq_le_sq₀ hb0 (by norm_num : (0:ℝ) ≤ 1/50)).2 hb
  have hc : (delta+theta*(1+delta))^2+theta ≤ (3/500:ℝ) := by
    change theta ≤ (1/200:ℝ) at hremoved
    linarith
  have he := gridTrim_projection_error_explicit hK hA hunit B delta hdelta huniform
  have he' := he.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg M))
  have hm2 : M^2 ≤ (1/2)*M := by
    have h := mul_le_mul_of_nonneg_right hhalf hM
    change M*M ≤ _ at h
    nlinarith only [h]
  nlinarith only [he',hm2,hvar,hM]

end TransposeFollowup
