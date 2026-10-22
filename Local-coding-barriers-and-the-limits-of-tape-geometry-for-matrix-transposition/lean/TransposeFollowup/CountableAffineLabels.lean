import TransposeFollowup.FiniteAffineLabels
import Mathlib.MeasureTheory.Measure.Continuity

/-! Countably many affine return graphs: restrict to finitely many graphs,
use the already-proved finite label, and charge the discarded finite-measure
tail. Continuity from above is imported from mathlib. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Filter
open scoped ENNReal BigOperators Topology
set_option autoImplicit false

theorem exists_countable_affine_small_cut
    (s : ℕ → ℝˣ) (b : ℕ → ℝ) (c₀ : ℝ)
    (μ : Measure (IntervalTimePair c₀)) [IsFiniteMeasure μ]
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hsupport : μ (finiteReturnGraphs s b c₀)ᶜ=0)
    (hmarginal : ∀ E : Set ℝ, MeasurableSet E →
      μ {p | p.1.val ∈ E} ≤ ENNReal.ofReal κ*volume E)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ Transpose.Tape.PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Set.Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      μ {p | β p.1.val ≠ β p.2.val} < ENNReal.ofReal ε := by
  let G (N : ℕ) := finiteReturnGraphs (fun j : Fin N => s j.val) (fun j : Fin N => b j.val) c₀
  have hG (N : ℕ) : MeasurableSet (G N) := measurableSet_finiteReturnGraphs _ _ _
  have hmono : Monotone G := by
    intro n m hnm p hp
    obtain ⟨j,hj⟩ := hp
    exact ⟨⟨j.val,lt_of_lt_of_le j.isLt hnm⟩,hj⟩
  have hunion : (⋃ N, G N)=finiteReturnGraphs s b c₀ := by
    ext p
    constructor
    · intro hp
      obtain ⟨N,j,hj⟩ := Set.mem_iUnion.mp hp
      exact ⟨j.val,hj⟩
    · rintro ⟨j,hj⟩
      exact Set.mem_iUnion.mpr ⟨j+1,⟨j,Nat.lt_succ_self j⟩,hj⟩
  have hinter : (⋂ N, (G N)ᶜ)=(finiteReturnGraphs s b c₀)ᶜ := by
    rw [← Set.compl_iUnion,hunion]
  have hlim := tendsto_measure_iInter_atTop (μ:=μ)
    (fun N => (hG N).compl.nullMeasurableSet)
    (show Antitone (fun N => (G N)ᶜ) from fun _ _ h => Set.compl_subset_compl.mpr (hmono h))
    ⟨0,measure_ne_top μ _⟩
  rw [hinter,hsupport] at hlim
  have hehalf : 0 < ENNReal.ofReal (ε/2) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨N,hN⟩ := (hlim.eventually (gt_mem_nhds hehalf)).exists
  have hrestrict : (μ.restrict (G N)) (G N)ᶜ=0 := by
    rw [Measure.restrict_apply' (hG N),Set.compl_inter_self,measure_empty]
  have hmarg : ∀ E : Set ℝ, MeasurableSet E →
      (μ.restrict (G N)) {p | p.1.val ∈ E} ≤ ENNReal.ofReal κ*volume E := by
    intro E hE
    exact (Measure.restrict_apply_le (μ:=μ) _ _).trans (hmarginal E hE)
  obtain ⟨β,hβ,hpc,hmass,hcut⟩ := exists_finite_affine_small_cut
    (fun j : Fin N => s j.val) (fun j : Fin N => b j.val) c₀
    (μ.restrict (G N)) hκ hrestrict hmarg hθ (show 0 < ε/2 by positivity)
  refine ⟨β,hβ,hpc,hmass,?_⟩
  let E : Set (IntervalTimePair c₀) := {p | β p.1.val ≠ β p.2.val}
  have hsub : E ⊆ (E ∩ G N) ∪ (G N)ᶜ := by
    intro p hp
    by_cases hg : p ∈ G N
    · exact Set.mem_union_left _ ⟨hp,hg⟩
    · exact Set.mem_union_right _ hg
  calc
    μ E ≤ μ ((E ∩ G N) ∪ (G N)ᶜ) := measure_mono hsub
    _ ≤ μ (E ∩ G N)+μ (G N)ᶜ := measure_union_le _ _
    _ = (μ.restrict (G N)) E+μ (G N)ᶜ := by rw [Measure.restrict_apply' (hG N)]
    _ < ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hcut hN
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end TransposeFollowup.AffineMotion
