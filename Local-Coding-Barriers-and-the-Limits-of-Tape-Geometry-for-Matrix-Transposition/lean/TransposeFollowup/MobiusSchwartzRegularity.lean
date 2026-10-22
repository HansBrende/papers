import TransposeFollowup.MobiusPoleDecay
import TransposeFollowup.MobiusSchwartzDerivative

/-! The null pole does not hide a jump or a singular derivative for Schwartz
inputs: cubic decay gives derivative zero there, and the global derivative
is the pullback of another Schwartz function. -/
namespace TransposeFollowup.RealMobius
open Classical Filter MeasureTheory
open scoped SchwartzMap Topology ContDiff
set_option autoImplicit false

theorem hasDerivAt_scaledPullback_pole_of_cubic_decay {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : ℝ → E) {B p : ℝ}
    (hu : ∀ y : ℝ, |y| ^ 3 * ‖u y‖ ≤ B) (hp : denom g p = 0) :
    HasDerivAt (scaledPullback g u) 0 p := by
  let η := |num g p| / 2
  have hn : 0 < |num g p| := abs_pos.mpr (num_ne_zero_at_pole g hp)
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : Continuous (fun x : ℝ => |num g x|) := by unfold num; fun_prop
  have hev : ∀ᶠ x in 𝓝 p, η ≤ |num g x| :=
    (hc.tendsto p).eventually_const_le (by dsimp [η]; linarith)
  let C := B / η ^ 3 * |g 1 0| ^ 2
  rw [hasDerivAt_iff_tendsto]
  simp only [scaledPullback_at_pole g u hp, smul_zero, sub_zero]
  apply squeeze_zero' (Eventually.of_forall (fun x => by positivity))
    (g := fun x : ℝ => C * ‖x - p‖)
  · filter_upwards [hev] with x hx
    have h := scaledPullback_norm_le_of_cubic_decay g u hη hu hx
    rw [denom_eq_mul_sub_at_pole g hp, abs_mul, mul_pow] at h
    rw [Real.norm_eq_abs]
    by_cases he : x = p
    · subst x
      simp
    · calc
        _ ≤ |x - p|⁻¹ * (B / η ^ 3 * (|g 1 0| ^ 2 * |x - p| ^ 2)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ = C * |x - p| := by
          dsimp [C]
          field_simp [abs_ne_zero.mpr (sub_ne_zero.mpr he)]
  · have hcont : Continuous (fun x : ℝ => C * ‖x - p‖) := by fun_prop
    simpa using hcont.tendsto p

theorem schwartz_hasDerivAt_scaledPullback_pole {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) {p : ℝ}
    (hp : denom g p = 0) : HasDerivAt (scaledPullback g u) 0 p := by
  obtain ⟨B, _, hB⟩ := u.decay 3 0
  apply hasDerivAt_scaledPullback_pole_of_cubic_decay g u (B := B) _ hp
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using hB

theorem schwartz_scaledPullback_differentiable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    Differentiable ℝ (scaledPullback g u) := by
  intro x
  by_cases hx : denom g x = 0
  · exact (schwartz_hasDerivAt_scaledPullback_pole g u hx).differentiableAt
  · exact (hasDerivAt_scaledPullback g hx (u.hasDerivAt _)).differentiableAt

theorem schwartz_scaledPullback_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    deriv (scaledPullback g u) = scaledPullback g (schwartzDifferentialTransport g u) := by
  funext x
  by_cases hx : denom g x = 0
  · rw [(schwartz_hasDerivAt_scaledPullback_pole g u hx).deriv,
      scaledPullback_at_pole g _ hx]
  · have h := (hasDerivAt_scaledPullback_transport g hx (u.hasDerivAt _)).deriv
    simpa only [scaledPullback, schwartzDifferentialTransport_apply] using h

theorem schwartz_scaledPullback_contDiff_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    ContDiff ℝ 1 (scaledPullback g u) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨schwartz_scaledPullback_differentiable g u, ?_⟩
  rw [schwartz_scaledPullback_deriv]
  exact (schwartz_scaledPullback_differentiable g (schwartzDifferentialTransport g u)).continuous

theorem schwartz_scaledPullback_contDiff_nat {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (n : ℕ) (u : 𝓢(ℝ, E)) :
    ContDiff ℝ n (scaledPullback g u) := by
  induction n generalizing u with
  | zero => exact contDiff_zero.mpr (schwartz_scaledPullback_differentiable g u).continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨schwartz_scaledPullback_differentiable g u, by simp, ?_⟩
    rw [schwartz_scaledPullback_deriv]
    exact ih (schwartzDifferentialTransport g u)

theorem schwartz_scaledPullback_smooth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    ContDiff ℝ ∞ (scaledPullback g u) :=
  contDiff_infty.mpr (fun n => schwartz_scaledPullback_contDiff_nat g n u)

theorem schwartz_scaledPullback_iteratedDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (n : ℕ) (u : 𝓢(ℝ, E)) :
    iteratedDeriv n (scaledPullback g u) =
      scaledPullback g ((schwartzDifferentialTransport g)^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply', schwartz_scaledPullback_deriv]

theorem schwartz_scaledPullback_iteratedDeriv_integrable_norm_sq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (n : ℕ) (u : 𝓢(ℝ, E)) :
    Integrable (fun x => ‖iteratedDeriv n (scaledPullback g u) x‖ ^ 2) := by
  rw [schwartz_scaledPullback_iteratedDeriv]
  exact (scaledPullback_integrable_norm_sq_iff g _).mpr
    (schwartz_integrable_norm_sq ((schwartzDifferentialTransport g)^[n] u))

theorem schwartz_scaledPullback_iteratedDeriv_energy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (n : ℕ) (u : 𝓢(ℝ, E)) :
    (∫ x, ‖iteratedDeriv n (scaledPullback g u) x‖ ^ 2) =
      ∫ y, ‖((schwartzDifferentialTransport g)^[n] u) y‖ ^ 2 := by
  rw [schwartz_scaledPullback_iteratedDeriv]
  exact scaledPullback_integral_norm_sq g _

end TransposeFollowup.RealMobius
