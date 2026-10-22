import TransposeFollowup.TranslationUniformity

/-! Exact cell trimming and quantitative mass loss. The complement-cardinality
bound specializes to removal of the first and last m cells, whose retained
union lies in the required central interval. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

def gridTrim {K : ℕ} (A : Set ℝ) (B : Finset (Fin K)) : Set ℝ := A∩gridCells B

theorem gridTrim_measurable {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A) (B : Finset (Fin K)) :
    MeasurableSet (gridTrim A B) := hA.inter (gridCells_measurable B)

theorem gridTrim_subset {K : ℕ} (A : Set ℝ) (B : Finset (Fin K)) : gridTrim A B⊆A :=
  inter_subset_left

theorem gridTrim_subset_unit {K : ℕ} (A : Set ℝ) (B : Finset (Fin K)) :
    gridTrim A B⊆Icc (0:ℝ) 1 := inter_subset_right.trans (gridCells_subset_unit B)

theorem gridTrim_volume_real {K : ℕ} {A : Set ℝ} (hA : MeasurableSet A) (B : Finset (Fin K)) :
    volume.real (gridTrim A B)=∑ i∈B,volume.real (A∩gridCell i) := by
  unfold gridTrim gridCells
  simp_rw [Set.inter_iUnion]
  apply measureReal_biUnion_finset
  · intro i _ j _ hij
    exact (gridCell_pairwise_disjoint hij).mono inter_subset_right inter_subset_right
  · exact fun i _ => hA.inter (gridCell_measurable i)
  · exact fun i _ => unit_subset_volume_ne_top (inter_subset_right.trans (gridCell_subset_unit i))

theorem gridCells_inter_cell {K : ℕ} (B : Finset (Fin K)) (i : Fin K) :
    gridCells B∩gridCell i=if i∈B then gridCell i else ∅ := by
  ext x
  by_cases hi : i∈B
  · simp only [hi,ite_true,mem_inter_iff]
    constructor
    · exact And.right
    · intro hx
      exact ⟨Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hx⟩⟩,hx⟩
  · simp only [hi,ite_false,mem_inter_iff,mem_empty_iff_false,iff_false,not_and]
    intro hx hx'
    obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hx
    obtain ⟨hjB,hxj⟩:=Set.mem_iUnion.mp hj
    have hji : j≠i:=by intro h;subst j;exact hi hjB
    exact Set.disjoint_left.mp (gridCell_pairwise_disjoint hji) hxj hx'

theorem gridTrim_inter_cell {K : ℕ} (A : Set ℝ) (B : Finset (Fin K)) (i : Fin K) :
    gridTrim A B∩gridCell i=if i∈B then A∩gridCell i else ∅ := by
  unfold gridTrim
  rw [Set.inter_assoc,gridCells_inter_cell]
  split_ifs <;> simp

theorem gridTrim_partition {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (B : Finset (Fin K)) :
    volume.real (gridTrim A B)+volume.real (gridTrim A Bᶜ)=volume.real A := by
  rw [gridTrim_volume_real hA,gridTrim_volume_real hA,Finset.sum_add_sum_compl]
  simp_rw [← gridMass_eq]
  simpa only [Fin.sum_univ_eq_sum_range] using gridMass_sum hK hA hunit

theorem gridTrim_loss_nonneg {K : ℕ} {A : Set ℝ} (hunit : A⊆Icc (0:ℝ) 1)
    (B : Finset (Fin K)) : 0 ≤ volume.real A-volume.real (gridTrim A B) :=
  sub_nonneg.mpr (measureReal_mono (gridTrim_subset A B) (unit_subset_volume_ne_top hunit))

theorem gridTrim_mass_bound {K : ℕ} (hK : 0<K) {A : Set ℝ} (hA : MeasurableSet A)
    (delta : ℝ)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (B : Finset (Fin K)) :
    volume.real (gridTrim A B) ≤ (B.card:ℝ)/(K:ℝ)*(1+delta)*volume.real A := by
  have hK' : (0:ℝ)<K:=by exact_mod_cast hK
  have hs : ∑ i∈B,(K:ℝ)*volume.real (A∩gridCell i) ≤ 
      ∑ _i∈B,(1+delta)*volume.real A := by
    apply Finset.sum_le_sum
    intro i _
    have hi:=(abs_le.mp (huniform i)).2
    linarith
  rw [← Finset.mul_sum,← gridTrim_volume_real hA] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have h : volume.real (gridTrim A B) ≤ (B.card:ℝ)*((1+delta)*volume.real A)/(K:ℝ) :=
    (le_div_iff₀ hK').mpr (by simpa only [mul_comm] using hs)
  calc
    _  ≤  (B.card:ℝ)*((1+delta)*volume.real A)/(K:ℝ) := h
    _ = _ := by ring

theorem gridTrim_loss_bound {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (delta : ℝ)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (B : Finset (Fin K)) :
    volume.real A-volume.real (gridTrim A B) ≤ (Bᶜ.card:ℝ)/(K:ℝ)*(1+delta)*volume.real A := by
  have hp:=gridTrim_partition hK hA hunit B
  have hb:=gridTrim_mass_bound hK hA delta huniform Bᶜ
  linarith

def centralCells (K m : ℕ) : Finset (Fin K) :=
  Finset.univ.filter (fun i => m ≤ i.val ∧ i.val+m<K)

def centralCellEmbedding {K m : ℕ} (hm : 2*m ≤ K) : Fin (K-2*m) ↪ Fin K where
  toFun i:=⟨m+i.val,by have := i.isLt;omega⟩
  inj':=by intro i j h;apply Fin.ext;have := congrArg Fin.val h;change m+i.val=m+j.val at this;omega

theorem centralCells_eq_map {K m : ℕ} (hm : 2*m ≤ K) :
    centralCells K m=Finset.univ.map (centralCellEmbedding hm) := by
  ext i
  simp only [centralCells,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
  constructor
  · intro hi
    refine ⟨⟨i.val-m,by have := i.isLt;omega⟩,?_⟩
    apply Fin.ext
    change m+(i.val-m)=i.val
    omega
  · rintro ⟨j,rfl⟩
    change m ≤ m+j.val ∧ m+j.val+m<K
    have := j.isLt
    omega

theorem centralCells_compl_card {K m : ℕ} (hm : 2*m ≤ K) : (centralCells K m)ᶜ.card=2*m := by
  rw [Finset.card_compl,centralCells_eq_map hm,Finset.card_map,Finset.card_univ]
  simp only [Fintype.card_fin]
  omega

theorem centralCells_subset_interval {K m : ℕ} (hK : 0<K) :
    gridCells (centralCells K m)⊆Icc ((m:ℝ)/K) (1-(m:ℝ)/K) := by
  intro x hx
  obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hx
  obtain ⟨hiC,hxi⟩:=Set.mem_iUnion.mp hi
  have hi:=(Finset.mem_filter.mp hiC).2
  have hl : (m:ℝ) ≤ i.val:=by exact_mod_cast hi.1
  have hu : (i.val:ℝ)+1+(m:ℝ) ≤ K:=by exact_mod_cast (show i.val+1+m ≤ K by omega)
  have hk : (0:ℝ)<K:=by exact_mod_cast hK
  have hd : (K:ℝ)*((m:ℝ)/K)=m:=mul_div_cancel₀ _ hk.ne'
  change (i.val:ℝ)<(K:ℝ)*x ∧ (K:ℝ)*x<(i.val:ℝ)+1 at hxi
  constructor
  · apply (div_le_iff₀ hk).mpr
    nlinarith [hxi.1]
  · nlinarith [hxi.2]

theorem centralTrim_loss_bound {K m : ℕ} (hK : 0<K) (hm : 2*m ≤ K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) (delta : ℝ)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A) :
    gridTrim A (centralCells K m)⊆Icc ((m:ℝ)/K) (1-(m:ℝ)/K) ∧
    volume.real A-volume.real (gridTrim A (centralCells K m)) ≤ 
      (2*(m:ℝ)/(K:ℝ))*(1+delta)*volume.real A := by
  refine ⟨inter_subset_right.trans (centralCells_subset_interval hK),?_⟩
  simpa only [centralCells_compl_card hm,Nat.cast_mul,Nat.cast_ofNat] using
    gridTrim_loss_bound hK hA hunit delta huniform (centralCells K m)

namespace RationalUnitMobius

theorem augmented_central_trim {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (sigma : ℝ) (hsigma : 0 ≤  sigma)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    gridTrim A (centralCells K m)⊆Icc ((m:ℝ)/K) (1-(m:ℝ)/K) ∧
    volume.real A-volume.real (gridTrim A (centralCells K m)) ≤ 
      (2*(m:ℝ)/(K:ℝ))*(1+(K:ℝ)*((K-1:ℕ):ℝ)*sigma)*volume.real A :=
  centralTrim_loss_bound (by omega) hm hA hunit _ (by
    intro i
    simpa only [mul_assoc] using augmented_cell_uniformity F hK hA hunit sigma hsigma hsmall i)

end RationalUnitMobius
end TransposeFollowup
