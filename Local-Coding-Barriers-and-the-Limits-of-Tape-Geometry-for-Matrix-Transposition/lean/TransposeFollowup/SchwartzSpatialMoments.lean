import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.L2Space

/-! Polynomial spatial moments of a Schwartz function and its derivative.
These are integrability results, not uniform bounds on the moments. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped SchwartzMap
set_option autoImplicit false

theorem schwartz_integrable_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : 𝓢(ℝ, E)) : Integrable (fun y => ‖u y‖ ^ 2) :=
  (u.memLp 2 volume).integrable_norm_pow (by decide : 2 ≠ 0)

theorem schwartz_integrable_even_moment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : 𝓢(ℝ, E)) (k : ℕ) :
    Integrable (fun y => y ^ (2 * k) * ‖u y‖ ^ 2) := by
  have ht : (fun y : ℝ => y ^ k).HasTemperateGrowth := by fun_prop
  have h := schwartz_integrable_norm_sq (SchwartzMap.smulLeftCLM E (fun y : ℝ => y ^ k) u)
  simpa only [SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, ← pow_mul, Nat.mul_comm k 2] using h

theorem schwartz_integrable_deriv_even_moment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : 𝓢(ℝ, E)) (k : ℕ) :
    Integrable (fun y => y ^ (2 * k) * ‖deriv u y‖ ^ 2) := by
  exact schwartz_integrable_even_moment (SchwartzMap.derivCLM ℝ E u) k

end TransposeFollowup
