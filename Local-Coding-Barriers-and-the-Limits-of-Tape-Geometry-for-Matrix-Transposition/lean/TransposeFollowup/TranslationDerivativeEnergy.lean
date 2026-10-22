import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! Translation differences are bounded in L2 by derivative energy.
The argument only requires a continuous derivative with finite energy;
the original function need not be integrable or Schwartz. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
set_option autoImplicit false

theorem translation_difference_pointwise_energy {u du : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hdu : Continuous du) (x t : ℝ) :
    ‖u (x + t) - u x‖ ^ 2 ≤ t ^ 2 * ∫ s in Icc (0 : ℝ) 1, ‖du (x + s * t)‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let v := fun s : ℝ => t • du (x + s * t)
  have hv : Continuous v := hdu.comp (continuous_const.add (continuous_id.mul_const t)) |>.const_smul t
  have hcurve (s : ℝ) : HasDerivAt (fun s => u (x + s * t)) (v s) s := by
    have hi : HasDerivAt (fun s : ℝ => x + s * t) t s := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id s).mul_const t).const_add x
    exact (hu (x + s * t)).scomp s hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hcurve s) (hv.intervalIntegrable 0 1)
    (a := (0 : ℝ)) (b := 1)
  simp only [one_mul, zero_mul, add_zero] at he
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc] at he
  have hconv : ConvexOn ℝ (univ : Set ℂ) (fun z => ‖z‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have hj := hconv.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _))
    (hv.integrableOn_Icc : Integrable v μ)
    ((hv.norm.pow 2).integrableOn_Icc : Integrable (fun s => ‖v s‖ ^ 2) μ)
  change ‖∫ s in Icc (0 : ℝ) 1, v s‖ ^ 2 ≤ ∫ s in Icc (0 : ℝ) 1, ‖v s‖ ^ 2 at hj
  rw [he] at hj
  simpa only [v, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, integral_const_mul] using hj

theorem translation_derivative_energy_kernel_integrable {du : ℝ → ℂ}
    (hdu : Continuous du) (he : Integrable (fun x => ‖du x‖ ^ 2)) (t : ℝ) :
    Integrable (fun z : ℝ × ℝ => ‖du (z.2 + z.1 * t)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  have hc : Continuous (fun z : ℝ × ℝ => ‖du (z.2 + z.1 * t)‖ ^ 2) := by fun_prop
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun s => he.comp_add_right (s * t))
  · have hh (s : ℝ) : (∫ x, ‖‖du (x + s * t)‖ ^ 2‖) = ∫ x, ‖du x‖ ^ 2 := by
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact integral_add_right_eq_self (μ := volume) (fun x : ℝ => ‖du x‖ ^ 2) (s * t)
    simp only [hh]
    exact integrable_const _

theorem translation_difference_integral_energy_le {u du : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hdu : Continuous du)
    (he : Integrable (fun x => ‖du x‖ ^ 2)) (t : ℝ) :
    (∫ x, ‖u (x + t) - u x‖ ^ 2) ≤ t ^ 2 * ∫ x, ‖du x‖ ^ 2 := by
  have hk := translation_derivative_energy_kernel_integrable hdu he t
  have hright : Integrable (fun x => t ^ 2 * ∫ s in Icc (0 : ℝ) 1, ‖du (x + s * t)‖ ^ 2) :=
    hk.integral_prod_right.const_mul (t ^ 2)
  have hcont : Continuous (fun x => ‖u (x + t) - u x‖ ^ 2) := by
    have hucont : Continuous u := continuous_iff_continuousAt.mpr (fun x => (hu x).continuousAt)
    fun_prop
  have hleft : Integrable (fun x => ‖u (x + t) - u x‖ ^ 2) :=
    hright.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u (x + t) - u x‖)] using
        translation_difference_pointwise_energy hu hdu x t))
  calc
    _ ≤ ∫ x, t ^ 2 * ∫ s in Icc (0 : ℝ) 1, ‖du (x + s * t)‖ ^ 2 :=
      integral_mono hleft hright (fun x => translation_difference_pointwise_energy hu hdu x t)
    _ = t ^ 2 * ∫ s in Icc (0 : ℝ) 1, ∫ x, ‖du (x + s * t)‖ ^ 2 := by
      rw [integral_const_mul]
      congr 1
      exact (integral_integral_swap (f := fun s x => ‖du (x + s * t)‖ ^ 2) hk).symm
    _ = _ := by
      simp_rw [integral_add_right_eq_self (μ := volume) (fun x : ℝ => ‖du x‖ ^ 2)]
      simp

end TransposeFollowup
