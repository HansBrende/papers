import TransposeFollowup.WeightedEnergyTransfer

/-! The unit-interval boundary contribution to weighted centering.
Points that leave the interval lie in two explicitly measured end strips. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

namespace RationalUnitMobius

def unitEscape (G : RationalUnitMobius) : Set ℝ :=
  Icc (0:ℝ) 1 \ G.whole.eval ⁻¹' Icc (0:ℝ) 1

theorem unitEscape_measurable (G : RationalUnitMobius) : MeasurableSet G.unitEscape :=
  measurableSet_Icc.diff (measurableSet_Icc.preimage G.whole.measurable_eval)

theorem unitEscape_subset_unit (G : RationalUnitMobius) : G.unitEscape⊆Icc (0:ℝ) 1 := sdiff_subset

theorem NearIdentity.unitEscape_subset {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) :
    G.unitEscape⊆Icc (0:ℝ) (8*eta) ∪ Icc (1-8*eta) 1 := by
  rintro x ⟨hx,hout⟩
  by_cases hl : x ≤ 8*eta
  · exact Or.inl ⟨hx.1,hl⟩
  by_cases hr : 1-8*eta ≤ x
  · exact Or.inr ⟨hr,hx.2⟩
  exact False.elim (hout (h.mapsTo_central he le_rfl ⟨(not_le.mp hl).le,(not_le.mp hr).le⟩))

theorem NearIdentity.unitEscape_volume {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) : volume.real G.unitEscape ≤ 16*eta := by
  have he0 := h.nonneg
  calc
    _ ≤ volume.real (Icc (0:ℝ) (8*eta) ∪ Icc (1-8*eta) 1) :=
      measureReal_mono (h.unitEscape_subset he)
        (measure_union_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    _ ≤ volume.real (Icc (0:ℝ) (8*eta))+volume.real (Icc (1-8*eta) 1) := measureReal_union_le _ _
    _ = 16*eta := by
      rw [Real.volume_real_Icc_of_le (by linarith : (0:ℝ) ≤ 8*eta),
        Real.volume_real_Icc_of_le (by linarith : 1-8*eta ≤ 1)]
      ring

theorem unitIndicator_comp_error_pointwise (G : RationalUnitMobius) {x : ℝ}
    (hx : x∈Icc (0:ℝ) 1) :
    ((Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) (G.whole.eval x)-
      (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x)^2=
      G.unitEscape.indicator (fun _ => (1:ℝ)) x := by
  by_cases hy : G.whole.eval x∈Icc (0:ℝ) 1 <;> simp [unitEscape,hx,hy]

theorem unitIndicator_comp_error_integrable (G : RationalUnitMobius) :
    IntegrableOn (fun x => ((Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) (G.whole.eval x)-
      (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x)^2) (Icc (0:ℝ) 1) := by
  have hi : Integrable (G.unitEscape.indicator (fun _ => (1:ℝ))) volume :=
    (integrableOn_const (unit_subset_volume_ne_top G.unitEscape_subset_unit)).integrable_indicator
      G.unitEscape_measurable
  apply hi.integrableOn.congr_fun ?_ measurableSet_Icc
  exact fun x hx => (G.unitIndicator_comp_error_pointwise hx).symm

theorem unitIndicator_comp_error_integral (G : RationalUnitMobius) :
    (∫ x in Icc (0:ℝ) 1,((Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) (G.whole.eval x)-
      (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x)^2)=volume.real G.unitEscape := by
  calc
    _ = ∫ x in Icc (0:ℝ) 1,G.unitEscape.indicator (fun _ => (1:ℝ)) x :=
      setIntegral_congr_fun measurableSet_Icc (fun x hx => G.unitIndicator_comp_error_pointwise hx)
    _ = _ := by
      rw [integral_indicator_const (1:ℝ) G.unitEscape_measurable,
        measureReal_restrict_apply G.unitEscape_measurable,smul_eq_mul,mul_one,
        inter_eq_left.mpr G.unitEscape_subset_unit]

theorem NearIdentity.weighted_unitIndicator_error {G : RationalUnitMobius} {eta : ℝ}
    (h : G.NearIdentity eta) (he : eta ≤ 1/8) :
    IntegrableOn (fun x => (G.whole.weightedPullback ((Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ))) x-
      (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x)^2) (Icc (0:ℝ) 1) ∧
    (∫ x in Icc (0:ℝ) 1,(G.whole.weightedPullback ((Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ))) x-
      (Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x)^2) ≤
      2*(1+32*eta)*(16*eta)+2*(32*eta)^2 := by
  have hi := (indicator_one_square_integrable measurableSet_Icc subset_rfl).integrableOn
    (s := Icc (0:ℝ) 1)
  have hb := h.weighted_local_error he (measurable_const.indicator measurableSet_Icc)
    G.unitIndicator_comp_error_integrable hi
  refine ⟨hb.1,?_⟩
  have hv : volume.real (Icc (0:ℝ) 1)=1 := by simp
  have hcoef : 0 ≤ 2*(1+32*eta) := by have h0 := h.nonneg; positivity
  have hbound := hb.2
  rw [G.unitIndicator_comp_error_integral,
    indicator_one_square_unit_integral measurableSet_Icc subset_rfl,hv,mul_one] at hbound
  exact hbound.trans (add_le_add (mul_le_mul_of_nonneg_left (h.unitEscape_volume he) hcoef) le_rfl)

end RationalUnitMobius
end TransposeFollowup
