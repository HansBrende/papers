import TransposeFollowup.FreeWalkAtom
import TransposeFollowup.GeneratorConvolutionWalk
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! Identify the actual matrix-walk atoms with the free-walk recurrence,
then transfer its elementary exponential upper bound. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open FreeGroup (mk)
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem generatorWalkMeasure_singleton_succ {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    (n : ℕ) (x : Group) :
    generatorWalkMeasure G (n + 1) {x} = ((2 * m : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ a : Fin m × Bool, generatorWalkMeasure G n {(FreeGroup.lift G (mk [a]))⁻¹ * x} := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hm n
  have hi (a : Group) :
      (∫⁻ y, ({x} : Set Group).indicator 1 (a * y) ∂generatorWalkMeasure G n) =
        generatorWalkMeasure G n {a⁻¹ * x} := by
    calc
      _ = ∫⁻ y, ((a * ·) ⁻¹' ({x} : Set Group)).indicator 1 y ∂generatorWalkMeasure G n := rfl
      _ = generatorWalkMeasure G n ((a * ·) ⁻¹' ({x} : Set Group)) :=
        lintegral_indicator_one ((measurableSet_singleton x).preimage (by fun_prop))
      _ = _ := by rw [Set.preimage_mul_left_singleton]
  have hf : Measurable (({x} : Set Group).indicator (1 : Group → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_singleton x)
  rw [← lintegral_indicator_one (measurableSet_singleton x), generatorWalkMeasure,
    Measure.lintegral_mconv hf,
    symmetricGeneratorMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_add_measure, lintegral_dirac, hi]
  simp [Fintype.sum_prod_type, FreeGroup.lift_mk, add_comm]

theorem generatorWalkMeasure_singleton_lift {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    (hfree : Function.Injective (FreeGroup.lift G)) (n : ℕ) (w : FreeGroup (Fin m)) :
    generatorWalkMeasure G n {FreeGroup.lift G w} = ENNReal.ofReal (FreeWalk.atom n w) := by
  induction n generalizing w with
  | zero =>
    have he : FreeGroup.lift G w = 1 ↔ w = 1 := by rw [← map_one (FreeGroup.lift G), hfree.eq_iff]
    by_cases hw : w = 1
    · simp [hw, generatorWalkMeasure, FreeWalk.atom]
    · have hne : FreeGroup.lift G w ≠ 1 := he.not.mpr hw
      simp [generatorWalkMeasure, FreeWalk.atom, hw, hne.symm]
  | succ n ih =>
    rw [generatorWalkMeasure_singleton_succ G hm]
    have he (a : Fin m × Bool) : (FreeGroup.lift G (mk [a]))⁻¹ * FreeGroup.lift G w =
        FreeGroup.lift G ((mk [a])⁻¹ * w) := by simp only [map_mul, map_inv]
    simp_rw [he, ih]
    rw [FreeWalk.atom, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun a _ => FreeWalk.atom_nonneg n _)]
    simp only [Fintype.card_fin]
    rw [ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 * m)]
    norm_cast

theorem generatorWalkMeasure_singleton_eq_zero_of_not_range {m : ℕ} (G : Fin m → Group)
    (hm : 0 < m) (n : ℕ) {x : Group} (hx : x ∉ Set.range (FreeGroup.lift G)) :
    generatorWalkMeasure G n {x} = 0 := by
  induction n generalizing x with
  | zero =>
    have hne : x ≠ 1 := by
      intro h
      exact hx ⟨1, by simpa only [map_one] using h.symm⟩
    simp [generatorWalkMeasure, hne.symm]
  | succ n ih =>
    rw [generatorWalkMeasure_singleton_succ G hm]
    have hnone (a : Fin m × Bool) : (FreeGroup.lift G (mk [a]))⁻¹ * x ∉
        Set.range (FreeGroup.lift G) := by
      rintro ⟨w, hw⟩
      apply hx
      refine ⟨mk [a] * w, ?_⟩
      rw [map_mul, hw, mul_inv_cancel_left]
    simp_rw [ih (hnone _)]
    simp

theorem generatorWalkMeasure_atom_le {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    (hfree : Function.Injective (FreeGroup.lift G)) {k : ℝ} (hk : 1 ≤ k)
    (hcard : k ^ 2 ≤ 2 * m) (n : ℕ) (x : Group) :
    generatorWalkMeasure G n {x} ≤ ENNReal.ofReal ((2 / k) ^ n) := by
  by_cases hx : x ∈ Set.range (FreeGroup.lift G)
  · obtain ⟨w, rfl⟩ := hx
    rw [generatorWalkMeasure_singleton_lift G hm hfree]
    exact ENNReal.ofReal_le_ofReal (FreeWalk.atom_le hk (by simpa using hcard) n w)
  · rw [generatorWalkMeasure_singleton_eq_zero_of_not_range G hm n hx]
    exact bot_le

end TransposeFollowup.RealMobius
