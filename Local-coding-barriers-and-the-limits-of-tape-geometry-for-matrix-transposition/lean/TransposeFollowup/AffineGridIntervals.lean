import Transpose.Tape.DefsM
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Actual finite grid universes and breakpoints on a compact time interval.
Any deterministic natural-valued function of finitely many affine grid
coordinates satisfies the original paper's `PiecewiseConstOn` definition. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset
set_option autoImplicit false

theorem exists_finite_continuous_floor_range (f : ℝ → ℝ) (hf : Continuous f) (c₀ : ℝ) :
    ∃ C : Finset ℤ, ∀ x ∈ Set.Icc 0 c₀, ⌊f x⌋ ∈ C := by
  have hc : IsCompact (f '' Set.Icc 0 c₀) := isCompact_Icc.image hf
  obtain ⟨lo,hlo⟩ := hc.bddBelow
  obtain ⟨hi,hhi⟩ := hc.bddAbove
  refine ⟨Finset.Icc ⌊lo⌋ ⌊hi⌋, fun x hx => ?_⟩
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono (hlo ⟨x,hx,rfl⟩),
    Int.floor_mono (hhi ⟨x,hx,rfl⟩)⟩

theorem exists_finite_affine_grid_range {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (h c₀ : ℝ) :
    ∃ C : Finset ℤ, ∀ i x, x ∈ Set.Icc 0 c₀ → ⌊(a i*x+b i)/h⌋ ∈ C := by
  have hf (i : ι) : Continuous (fun x : ℝ => (a i*x+b i)/h) := by fun_prop
  choose C hC using fun i => exists_finite_continuous_floor_range _ (hf i) c₀
  refine ⟨Finset.univ.biUnion C, fun i x hx => ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hC i x hx⟩

theorem affine_grid_threshold_mem {a h u v : ℝ} (ha : a ≠ 0) (hh : h ≠ 0)
    (b : ℝ) (huv : u ≤ v) (z : ℤ)
    (hz : (z : ℝ) ∈ Set.uIcc ((a*u+b)/h) ((a*v+b)/h)) :
    (h*z-b)/a ∈ Set.Icc u v := by
  have hf : ContinuousOn (fun x : ℝ => (a*x+b)/h) (Set.uIcc u v) := by fun_prop
  obtain ⟨x,hx,he⟩ := intermediate_value_uIcc hf hz
  have he' : x=(h*z-b)/a := by
    apply (eq_div_iff ha).mpr
    have ht := (div_eq_iff hh).mp he
    linarith
  rw [← he']
  simpa only [Set.uIcc_of_le huv] using hx

theorem affine_grid_eq_of_avoids {a h u v : ℝ} (ha : a ≠ 0) (hh : h ≠ 0)
    (b : ℝ) (huv : u ≤ v) (C : Finset ℤ)
    (hu : ⌊(a*u+b)/h⌋ ∈ C) (hv : ⌊(a*v+b)/h⌋ ∈ C)
    (havoid : ∀ z ∈ C, (h*z-b)/a ∉ Set.Icc u v) :
    ⌊(a*u+b)/h⌋=⌊(a*v+b)/h⌋ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact havoid _ hv (affine_grid_threshold_mem ha hh b huv _
      (Set.mem_uIcc_of_le (Int.floor_lt.mp hlt).le (Int.floor_le _)))
  · exact havoid _ hu (affine_grid_threshold_mem ha hh b huv _
      (Set.mem_uIcc_of_ge (Int.floor_lt.mp hgt).le (Int.floor_le _)))

theorem exists_affine_grid_breakpoints {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) {h : ℝ} (hh : h ≠ 0) (c₀ : ℝ) :
    ∃ Z : Finset ℝ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ c₀ →
      (∀ x ∈ Set.Icc u v, x ∉ (Z : Set ℝ)) →
      ∀ i, ⌊(a i*u+b i)/h⌋=⌊(a i*v+b i)/h⌋ := by
  obtain ⟨C,hC⟩ := exists_finite_affine_grid_range a b h c₀
  let Z := Finset.univ.biUnion (fun i => C.image (fun z : ℤ => (h*(z : ℝ)-b i)/a i))
  refine ⟨Z,fun u v hu huv hv havoid i => ?_⟩
  apply affine_grid_eq_of_avoids (ha i) hh (b i) huv C
    (hC i u ⟨hu,huv.trans hv⟩) (hC i v ⟨hu.trans huv,hv⟩)
  intro z hz hx
  have hZ : (h*z-b i)/a i ∈ Z :=
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  exact havoid _ hx hZ

theorem piecewiseConstOn_affine_grid {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) {h : ℝ} (hh : h ≠ 0)
    (c₀ : ℝ) (label : (ι → ℤ) → ℕ) :
    Transpose.Tape.PiecewiseConstOn (fun x => label (fun i => ⌊(a i*x+b i)/h⌋)) ∅ c₀ := by
  obtain ⟨Z,hZ⟩ := exists_affine_grid_breakpoints a b ha hh c₀
  refine ⟨Z,fun u v hu huv hv havoid => ?_⟩
  exact congrArg label (funext (hZ u v hu huv hv (fun x hx => (havoid x hx).2)))

end TransposeFollowup.AffineMotion
