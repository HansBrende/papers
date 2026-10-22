import TransposeFollowup.SmallExpansionSymmDiff

/-! Exact indicator-composition energy and its small-expansion bound.
The square is integrable, and the preimage is identified with the actual
inverse image map before the symmetric-difference estimate is applied. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
open scoped symmDiff
set_option autoImplicit false

theorem indicator_difference_square (S T : Set ℝ) (x : ℝ) :
    (S.indicator (fun _ => (1:ℝ)) x-T.indicator (fun _ => (1:ℝ)) x)^2=
      (S ∆ T).indicator (fun _ => (1:ℝ)) x := by
  by_cases hs : x∈S <;> by_cases ht : x∈T <;> simp [Set.mem_symmDiff,hs,ht]

theorem indicator_difference_square_integrable {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSu : S⊆Icc (0:ℝ) 1) (hTu : T⊆Icc (0:ℝ) 1) :
    Integrable (fun x => (S.indicator (fun _ => (1:ℝ)) x-T.indicator (fun _ => (1:ℝ)) x)^2) volume := by
  have he : (fun x => (S.indicator (fun _ => (1:ℝ)) x-T.indicator (fun _ => (1:ℝ)) x)^2)=
      (S ∆ T).indicator (fun _ => (1:ℝ)) := funext (indicator_difference_square S T)
  rw [he]
  exact (integrableOn_const (unit_subset_volume_ne_top
    (Set.symmDiff_subset_union.trans (union_subset hSu hTu)))).integrable_indicator (hS.symmDiff hT)

theorem indicator_difference_square_integral {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫ x,(S.indicator (fun _ => (1:ℝ)) x-T.indicator (fun _ => (1:ℝ)) x)^2)=
      volume.real (S ∆ T) := by
  simp_rw [indicator_difference_square]
  exact integral_indicator_one (hS.symmDiff hT)

namespace RationalUnitMobius
variable (G : RationalUnitMobius)

theorem indicator_comp_eq_inverse_image {A : Set ℝ} (hunit : A⊆Icc (0:ℝ) 1)
    (hinv : MapsTo G.inverse.whole.eval A (Icc (0:ℝ) 1)) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    A.indicator (fun _ => (1:ℝ)) (G.whole.eval x)=
      (G.inverse.whole.eval '' A).indicator (fun _ => (1:ℝ)) x := by
  have heq := G.unit_preimage_eq_inverse_image hunit hinv
  have hmem : G.whole.eval x∈A ↔ x∈G.inverse.whole.eval '' A := by
    constructor
    · intro hy
      rw [← heq]
      exact ⟨hx,hy⟩
    · intro hy
      rw [← heq] at hy
      exact hy.2
  by_cases hy : G.whole.eval x∈A
  · simp only [Set.indicator_of_mem hy,Set.indicator_of_mem (hmem.mp hy)]
  · simp only [Set.indicator_of_notMem hy,Set.indicator_of_notMem (fun h => hy (hmem.mpr h))]

theorem indicator_comp_square_integrableOn {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (hinv : MapsTo G.inverse.whole.eval A (Icc (0:ℝ) 1)) :
    IntegrableOn (fun x => (A.indicator (fun _ => (1:ℝ)) (G.whole.eval x)-
      A.indicator (fun _ => (1:ℝ)) x)^2) (Icc (0:ℝ) 1) := by
  have hS := G.inverse.whole.measurableSet_image_eval hA (by simpa [whole] using hunit)
  have hSu : G.inverse.whole.eval '' A⊆Icc (0:ℝ) 1 := by
    rintro y ⟨x,hx,rfl⟩
    exact hinv hx
  apply (indicator_difference_square_integrable hS hA hSu hunit).integrableOn.congr_fun
    ?_ measurableSet_Icc
  intro x hx
  dsimp only
  rw [G.indicator_comp_eq_inverse_image hunit hinv hx]

theorem indicator_comp_square_integral {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (hinv : MapsTo G.inverse.whole.eval A (Icc (0:ℝ) 1)) :
    (∫ x in Icc (0:ℝ) 1,(A.indicator (fun _ => (1:ℝ)) (G.whole.eval x)-
      A.indicator (fun _ => (1:ℝ)) x)^2)=volume.real ((G.inverse.whole.eval '' A) ∆ A) := by
  have hS := G.inverse.whole.measurableSet_image_eval hA (by simpa [whole] using hunit)
  have hSu : G.inverse.whole.eval '' A⊆Icc (0:ℝ) 1 := by
    rintro y ⟨x,hx,rfl⟩
    exact hinv hx
  have hdiff := hS.symmDiff hA
  have hsub := Set.symmDiff_subset_union.trans (union_subset hSu hunit)
  calc
    _ = ∫ x in Icc (0:ℝ) 1,((G.inverse.whole.eval '' A) ∆ A).indicator (fun _ => (1:ℝ)) x := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only
      rw [G.indicator_comp_eq_inverse_image hunit hinv hx]
      exact indicator_difference_square _ _ x
    _ = _ := by
      rw [integral_indicator_const (1:ℝ) hdiff,measureReal_restrict_apply hdiff,
        smul_eq_mul,mul_one,inter_eq_left.mpr hsub]

theorem augmented_small_expansion_indicator_error {c : ℕ} (F : Fin c → RationalUnitMobius)
    (t : ℚ) (ht : |t|<1) (p : Fin c) {eta r sigma : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8) (hr : 8*eta ≤ r)
    {A T : Set ℝ} (hT : MeasurableSet T) (hunit : A⊆Icc (0:ℝ) 1)
    (hTA : T⊆A) (hcentral : T⊆Icc r (1-r))
    (hsmall : volume.real (restrictedImageUnion (augmentedFamily F t ht) A) ≤
      (1+sigma)*volume.real A) :
    (∫ x in Icc (0:ℝ) 1,(T.indicator (fun _ => (1:ℝ)) ((F p).whole.eval x)-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤
      2*sigma*volume.real A+2*(volume.real A-volume.real T)+32*eta*volume.real T ∧
    (∫ x in Icc (0:ℝ) 1,(T.indicator (fun _ => (1:ℝ)) ((F p).inverse.whole.eval x)-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤
      2*sigma*volume.real A+2*(volume.real A-volume.real T)+32*eta*volume.real T := by
  have hb := augmented_small_expansion_symmDiff F t ht p hnear he hr hT hunit hTA hcentral hsmall
  have hp : MapsTo (F p).whole.eval T (Icc (0:ℝ) 1) :=
    fun x hx => hnear.mapsTo_central he hr (hcentral hx)
  have hm : MapsTo (F p).inverse.whole.eval T (Icc (0:ℝ) 1) :=
    fun x hx => hnear.inverse.mapsTo_central he hr (hcentral hx)
  constructor
  · rw [(F p).indicator_comp_square_integral hT (hTA.trans hunit) hm]
    exact hb.2
  · rw [(F p).inverse.indicator_comp_square_integral hT (hTA.trans hunit)
      (by simpa only [inverse_inverse] using hp),inverse_inverse]
    exact hb.1

theorem augmented_central_trim_indicator_error {c K m : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 2 ≤ K) (hm : 2*m ≤ K) (p : Fin c) {eta sigma delta : ℝ}
    (hnear : (F p).NearIdentity eta) (he : eta ≤ 1/8) (hr : 8*eta ≤ (m:ℝ)/K)
    {A : Set ℝ} (hA : MeasurableSet A) (hunit : A⊆Icc (0:ℝ) 1)
    (huniform : ∀ i : Fin K,|(K:ℝ)*volume.real (A∩gridCell i)-volume.real A| ≤ delta*volume.real A)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small hK)) A) ≤ (1+sigma)*volume.real A) :
    let T := gridTrim A (centralCells K m)
    (∫ x in Icc (0:ℝ) 1,(T.indicator (fun _ => (1:ℝ)) ((F p).whole.eval x)-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤
      (2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta)*volume.real A ∧
    (∫ x in Icc (0:ℝ) 1,(T.indicator (fun _ => (1:ℝ)) ((F p).inverse.whole.eval x)-
      T.indicator (fun _ => (1:ℝ)) x)^2) ≤
      (2*sigma+4*(m:ℝ)/(K:ℝ)*(1+delta)+32*eta)*volume.real A := by
  have hb := augmented_central_trim_symmDiff F hK hm p hnear he hr hA hunit huniform hsmall
  have hcentral := (centralTrim_loss_bound (by omega : 0<K) hm hA hunit delta huniform).1
  have hp : MapsTo (F p).whole.eval (gridTrim A (centralCells K m)) (Icc (0:ℝ) 1) :=
    fun x hx => hnear.mapsTo_central he hr (hcentral hx)
  have hm' : MapsTo (F p).inverse.whole.eval (gridTrim A (centralCells K m)) (Icc (0:ℝ) 1) :=
    fun x hx => hnear.inverse.mapsTo_central he hr (hcentral hx)
  constructor
  · rw [(F p).indicator_comp_square_integral (gridTrim_measurable hA _) (gridTrim_subset_unit A _) hm']
    exact hb.2
  · rw [(F p).inverse.indicator_comp_square_integral (gridTrim_measurable hA _)
      (gridTrim_subset_unit A _) (by simpa only [inverse_inverse] using hp),inverse_inverse]
    exact hb.1

end RationalUnitMobius
end TransposeFollowup
