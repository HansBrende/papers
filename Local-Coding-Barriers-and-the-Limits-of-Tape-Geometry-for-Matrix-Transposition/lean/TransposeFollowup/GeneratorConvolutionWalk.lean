import TransposeFollowup.SymmetricGeneratorMeasure
import TransposeFollowup.SymmetricDyadicPowers

/-! Concrete generator walks, operator iterates and dyadic norm lower bounds. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

noncomputable def generatorWalkMeasure {c : ℕ} (G : Fin c → Group) : ℕ → Measure Group
  | 0 => Measure.dirac 1
  | n + 1 => symmetricGeneratorMeasure G ∗ₘ generatorWalkMeasure G n

omit [BorelSpace Group] in
theorem generatorWalkMeasure_probability {c : ℕ} (G : Fin c → Group) (hc : 0 < c) (n : ℕ) :
    IsProbabilityMeasure (generatorWalkMeasure G n) := by
  have : IsProbabilityMeasure (symmetricGeneratorMeasure G) := symmetricGeneratorMeasure_probability G hc
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac (1 : Group)); infer_instance
  | succ n ih =>
    change IsProbabilityMeasure (symmetricGeneratorMeasure G ∗ₘ generatorWalkMeasure G n)
    have : IsProbabilityMeasure (generatorWalkMeasure G n) := ih
    infer_instance

theorem groupActionAverage_dirac (g : Group) (f : ComplexL2) :
    groupActionAverage (Measure.dirac g) f = complexPullbackL2 g⁻¹ f := by
  simp [groupActionAverage]

theorem groupActionAverage_generatorWalk {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (n : ℕ) (f : ComplexL2) :
    groupActionAverage (generatorWalkMeasure G n) f = (complexAverage G : ComplexL2 → ComplexL2)^[n] f := by
  have : IsProbabilityMeasure (symmetricGeneratorMeasure G) := symmetricGeneratorMeasure_probability G hc
  induction n with
  | zero => simp [generatorWalkMeasure, groupActionAverage_dirac, complexPullbackL2_one]
  | succ n ih =>
    have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hc n
    rw [generatorWalkMeasure, groupActionAverage_mconv, groupActionAverage_symmetricGeneratorMeasure,
      ih, Function.iterate_succ_apply']

theorem generatorWalk_dyadic_norm_lower {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (f : ComplexL2) (hf : ‖f‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hlarge : r ≤ ‖complexAverage G f‖)
    (m : ℕ) : r ^ (2 ^ m) ≤ ‖groupActionAverage (generatorWalkMeasure G (2 ^ m)) f‖ := by
  rw [groupActionAverage_generatorWalk G hc]
  exact symmetric_dyadic_iterate_norm_lower (complexAverage G) (complexAverage_symmetric G)
    f hf hr hlarge m

theorem generatorWalk_smoothed_dyadic_norm_lower {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (ν : Measure Group) [IsProbabilityMeasure ν] (j : ℕ) (u : 𝓢(ℝ, ℂ))
    (hu : ‖u.toLp 2 volume‖ = 1) {R r η : ℝ} (hr : 0 ≤ r)
    (hlarge : r ≤ ‖complexAverage G (u.toLp 2 volume)‖)
    (hR : schwartzDyadicRegularityCost j u ≤ R) (hη : η ≤ 1 / 2)
    (hs : ∀ᵐ g ∂ν, |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ η ∧ |g 1 0| ≤ η)
    (m : ℕ) (he : 29 * (2 : ℝ) ^ j * Real.sqrt R * η ≤ r ^ (2 ^ m) / 2) :
    r ^ (2 ^ m) / 2 ≤
      ‖groupActionAverage (generatorWalkMeasure G (2 ^ m) ∗ₘ ν) (u.toLp 2 volume)‖ := by
  have : IsProbabilityMeasure (generatorWalkMeasure G (2 ^ m)) :=
    generatorWalkMeasure_probability G hc (2 ^ m)
  exact groupActionAverage_smoothing_norm_lower _ ν j u hR hη hs
    (generatorWalk_dyadic_norm_lower G hc _ hu hr hlarge m) he

end TransposeFollowup.RealMobius
