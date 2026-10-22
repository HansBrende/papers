import TransposeFollowup.TranslationExpansion

/-! Small expansion under the actual augmented map family forces nearly
uniform cell masses. The finite path estimate retains K(K-1), rather than
loosening it to K squared. The set may have any measure in the unit interval. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false

noncomputable def gridMass (A : Set ℝ) (K i : ℕ) : ℝ :=
  volume.real (A∩Ioo ((i:ℝ)/K) (((i:ℝ)+1)/K))

theorem gridMass_eq {K : ℕ} (A : Set ℝ) (i : Fin K) :
    gridMass A K i.val=volume.real (A∩gridCell i) := by
  rw [gridCell_eq_Ioo]
  rfl

theorem gridMass_sum {K : ℕ} (hK : 0<K) {A : Set ℝ}
    (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1) :
    ∑ i∈Finset.range K,gridMass A K i=volume.real A := by
  let pieces : Fin K → Set ℝ := fun i => A∩gridCell i
  have hsub : (⋃ i,pieces i)⊆A := by
    intro x hx
    obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hx
    exact hi.1
  have hmiss : A \ (⋃ i,pieces i)⊆gridBoundary K := by
    intro x hx
    by_contra hb
    obtain ⟨i,hi⟩:=exists_gridCell_of_not_boundary hK (hunit hx.1) hb
    exact hx.2 (Set.mem_iUnion.mpr ⟨i,hx.1,hi⟩)
  have hv : volume (⋃ i,pieces i)=volume A :=
    measure_eq_measure_of_null_sdiff hsub (measure_mono_null hmiss (gridBoundary_volume K))
  have hd : Pairwise (fun i j => Disjoint (pieces i) (pieces j)) := by
    intro i j hij
    exact (gridCell_pairwise_disjoint hij).mono inter_subset_right inter_subset_right
  have hm : ∀ i,MeasurableSet (pieces i):=fun i => hA.inter (gridCell_measurable i)
  have hf : ∀ i,volume (pieces i)≠⊤:=fun _ => unit_subset_volume_ne_top (inter_subset_left.trans hunit)
  have hs:=measureReal_iUnion_fintype (μ:=volume) hd hm hf
  have he : (∑ i : Fin K,gridMass A K i.val)=volume.real A := by
    simp_rw [gridMass_eq]
    exact hs.symm.trans (congrArg ENNReal.toReal hv)
  simpa only [Fin.sum_univ_eq_sum_range] using he

theorem adjacent_path_bound (f : ℕ → ℝ) {K i j : ℕ} (hij : i≤j) (hj : j<K)
    (delta : ℝ) (hstep : ∀ k,k+1<K → |f k-f (k+1)|≤delta) :
    |f i-f j|≤((j-i:ℕ):ℝ)*delta := by
  have h:=dist_le_Ico_sum_of_dist_le (f:=f) (d:=fun _ => delta) hij (by
    intro k _ hk
    simpa only [Real.dist_eq] using hstep k (by omega))
  simpa only [Real.dist_eq,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] using h

theorem adjacent_pair_bound (f : ℕ → ℝ) {K i j : ℕ} (hi : i<K) (hj : j<K)
    (delta : ℝ) (hdelta : 0≤delta) (hstep : ∀ k,k+1<K → |f k-f (k+1)|≤delta) :
    |f i-f j|≤((K-1:ℕ):ℝ)*delta := by
  rcases le_total i j with hij | hji
  · exact (adjacent_path_bound f hij hj delta hstep).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show j-i≤K-1 by omega)) hdelta)
  · rw [abs_sub_comm]
    exact (adjacent_path_bound f hji hi delta hstep).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show i-j≤K-1 by omega)) hdelta)

theorem adjacent_average_bound (f : ℕ → ℝ) {K i : ℕ} (hi : i<K)
    (delta : ℝ) (hdelta : 0≤delta) (hstep : ∀ k,k+1<K → |f k-f (k+1)|≤delta) :
    |(K:ℝ)*f i-∑ j∈Finset.range K,f j|≤(K:ℝ)*((K-1:ℕ):ℝ)*delta := by
  have he : (K:ℝ)*f i-∑ j∈Finset.range K,f j=
      ∑ j∈Finset.range K,(f i-f j) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [he]
  calc
    _ ≤ ∑ j∈Finset.range K,|f i-f j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j∈Finset.range K,((K-1:ℕ):ℝ)*delta := Finset.sum_le_sum (fun j hj =>
      adjacent_pair_bound f hi (Finset.mem_range.mp hj) delta hdelta hstep)
    _ = _ := by simp [mul_assoc]

namespace RationalUnitMobius

theorem augmented_cell_uniformity {c K : ℕ} (F : Fin c → RationalUnitMobius) (hK : 2≤K)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (sigma : ℝ) (hsigma : 0≤ sigma)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A)≤(1+sigma)*volume.real A)
    (i : Fin K) :
    |(K:ℝ)*volume.real (A∩gridCell i)-volume.real A|≤
      (K:ℝ)*((K-1:ℕ):ℝ)*sigma*volume.real A := by
  have hstep : ∀ k,k+1<K → |gridMass A K k-gridMass A K (k+1)|≤ sigma*volume.real A := by
    intro k hk
    let u : Fin K:=⟨k,by omega⟩
    let v : Fin K:=⟨k+1,hk⟩
    have h:=augmented_adjacent_gain F hK hA hunit u v rfl
    have hu : gridMass A K k=volume.real (A∩gridCell u):=gridMass_eq A u
    have hv : gridMass A K (k+1)=volume.real (A∩gridCell v):=gridMass_eq A v
    rw [hu,hv]
    linarith
  have h:=adjacent_average_bound (gridMass A K) i.isLt (sigma*volume.real A)
    (mul_nonneg hsigma measureReal_nonneg) hstep
  rw [gridMass_sum (by omega) hA hunit,gridMass_eq A i] at h
  simpa only [mul_assoc] using h

theorem augmented_expansion_or_uniformity {c K : ℕ} (F : Fin c → RationalUnitMobius) (hK : 2≤K)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (sigma : ℝ) (hsigma : 0≤ sigma) :
    (1+sigma)*volume.real A≤volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ∨
      ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A|≤
        (K:ℝ)*((K-1:ℕ):ℝ)*sigma*volume.real A := by
  by_cases h : (1+sigma)*volume.real A≤volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A)
  · exact Or.inl h
  · exact Or.inr (augmented_cell_uniformity F hK hA hunit sigma hsigma (le_of_not_ge h))

end RationalUnitMobius
end TransposeFollowup
