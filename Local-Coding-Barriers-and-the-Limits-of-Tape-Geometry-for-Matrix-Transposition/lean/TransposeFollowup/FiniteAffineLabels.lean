import TransposeFollowup.WeightedAffinePriority
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Arbitrarily small classes and cut for a finite affine-return family.
All finite-set, mesh, collision and priority choices are discharged. The
measure's graph support and source-marginal bound remain explicit; deriving
these from the original countable-branch paths is a separate obligation. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem exists_finite_affine_small_cut {ι : Type*} [Fintype ι]
    (s : ι → ℝˣ) (b : ι → ℝ) (c₀ : ℝ)
    (μ : Measure (IntervalTimePair c₀)) [IsFiniteMeasure μ]
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hsupport : μ (finiteReturnGraphs s b c₀)ᶜ=0)
    (hmarginal : ∀ E : Set ℝ, MeasurableSet E →
      μ {p | p.1.val ∈ E} ≤ ENNReal.ofReal κ*volume E)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ Transpose.Tape.PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Set.Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      μ {p | β p.1.val ≠ β p.2.val} < ENNReal.ofReal ε := by
  let M := (μ Set.univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let δ := ε/(4*(M+1))
  let η := ε/(4*(κ+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨F,hF,hboundary⟩ := FiniteBoundary.exists_affine_small_symmetric_difference s b hδ
  have hboundary' (j : ι) :
      (((F ∪ F.image (FiniteBoundary.affineRight (s j) (b j))) \
        (F ∩ F.image (FiniteBoundary.affineRight (s j) (b j)))).card : ℝ≥0∞) ≤
        ENNReal.ofReal δ*(F ∪ F.image (FiniteBoundary.affineRight (s j) (b j))).card := by
    have ht := ENNReal.ofReal_le_ofReal (hboundary j)
    simpa only [ENNReal.ofReal_mul hδ.le,ENNReal.ofReal_natCast] using ht
  let K := affineCommonFamily F s b
  obtain ⟨ρ,hρ,hcoll⟩ := exists_small_affine_family_collisions K hη
  let L : ℝ := ∑ f : F, |((f.val.1 : ℝ))⁻¹|
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let τ := θ/(L+1)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let h := min ρ τ
  have hh : 0 < h := lt_min hρ hτ
  have hhρ : h ≤ ρ := min_le_left _ _
  have hhτ : h ≤ τ := min_le_right _ _
  have hclassReal : h*L ≤ θ := by
    have ht := (le_div_iff₀ (show (0 : ℝ) < L+1 by positivity)).mp hhτ
    nlinarith
  have hclass : ENNReal.ofReal h*∑ f : F, ENNReal.ofReal |((f.val.1 : ℝ))⁻¹| ≤
      ENNReal.ofReal θ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _),
      ← ENNReal.ofReal_mul hh.le]
    exact ENNReal.ofReal_le_ofReal hclassReal
  obtain ⟨β,hβ,hpc,hmass,hcut⟩ := exists_weighted_affine_priority_label
    s b F hF hh c₀ (ENNReal.ofReal δ) (ENNReal.ofReal κ) hboundary' μ hsupport hmarginal
  refine ⟨β,hβ,hpc,fun n => (hmass n).trans hclass,?_⟩
  have hμ : μ Set.univ=ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  have hbudget (x : ℝ) (hx : 0 ≤ x) : ε/(4*(x+1))*x ≤ ε/4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show (0 : ℝ) < 4*(x+1) by positivity)).mpr
    nlinarith
  have hsmall : δ*M+κ*η < ε := by
    have hm := hbudget M hM
    have hk := hbudget κ hκ
    dsimp only [δ,η]
    nlinarith
  calc
    μ {p | β p.1.val ≠ β p.2.val} ≤ ENNReal.ofReal δ*μ Set.univ+
        ENNReal.ofReal κ*volume (gridCollisions
          (fun f : K => (f.val.1 : ℝ)) (fun f : K => f.val.2) h) := hcut
    _ ≤ ENNReal.ofReal δ*μ Set.univ+ENNReal.ofReal κ*ENNReal.ofReal η := by
      gcongr
      exact hcoll h hh hhρ
    _ = ENNReal.ofReal (δ*M+κ*η) := by
      rw [hμ,← ENNReal.ofReal_mul hδ.le,← ENNReal.ofReal_mul hκ,
        ← ENNReal.ofReal_add (mul_nonneg hδ.le hM) (mul_nonneg hκ hη.le)]
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr hsmall

end TransposeFollowup.AffineMotion
