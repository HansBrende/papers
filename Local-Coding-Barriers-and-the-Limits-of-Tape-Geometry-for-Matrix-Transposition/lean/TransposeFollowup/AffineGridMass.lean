import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Exact grid-cell mass under invertible real affine maps. These bounds
make every selected grid label small, independently of the priority order;
negative slopes are included through the absolute Jacobian. -/
namespace TransposeFollowup.AffineMotion
open Classical MeasureTheory Set
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem volume_affine_preimage {a : ℝ} (ha : a ≠ 0) (b : ℝ) (S : Set ℝ) :
    volume ((fun x : ℝ => a*x+b) ⁻¹' S)=ENNReal.ofReal |a⁻¹| * volume S := by
  change volume ((fun x : ℝ => a*x) ⁻¹' ((fun y : ℝ => y+b) ⁻¹' S))= _
  rw [Real.volume_preimage_mul_left ha, measure_preimage_add_right]

theorem volume_affine_grid_fiber {a h : ℝ} (ha : a ≠ 0) (hh : 0 < h) (b : ℝ) (z : ℤ) :
    volume {x : ℝ | ⌊(a*x+b)/h⌋=z}=ENNReal.ofReal (h/|a|) := by
  have he : {x : ℝ | ⌊(a*x+b)/h⌋=z}=
      (fun x : ℝ => (a/h)*x+b/h) ⁻¹' Ico (z : ℝ) (z+1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Int.floor_eq_iff, Set.mem_preimage, Set.mem_Ico]
    rw [show (a*x+b)/h=(a/h)*x+b/h by ring]
  rw [he, volume_affine_preimage (div_ne_zero ha hh.ne'), Real.volume_Ico,
    show (z : ℝ)+1-z=1 by ring, ENNReal.ofReal_one, mul_one]
  congr 1
  rw [inv_div, abs_div, abs_of_pos hh]

theorem selected_affine_grid_label_mass {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) {h : ℝ} (hh : 0 < h)
    (I : Set ℝ) (label : ℝ → ℤ)
    (hselect : ∀ x ∈ I, ∃ i, label x=⌊(a i*x+b i)/h⌋) (z : ℤ) :
    volume {x | x ∈ I ∧ label x=z} ≤ ENNReal.ofReal h*∑ i, ENNReal.ofReal |(a i)⁻¹| := by
  have hsub : {x | x ∈ I ∧ label x=z} ⊆ ⋃ i, {x : ℝ | ⌊(a i*x+b i)/h⌋=z} := by
    rintro x ⟨hx, hz⟩
    obtain ⟨i, hi⟩ := hselect x hx
    exact Set.mem_iUnion.mpr ⟨i, hi.symm.trans hz⟩
  calc
    _ ≤ volume (⋃ i, {x : ℝ | ⌊(a i*x+b i)/h⌋=z}) := measure_mono hsub
    _ ≤ ∑ i, volume {x : ℝ | ⌊(a i*x+b i)/h⌋=z} := measure_iUnion_fintype_le volume _
    _ = _ := by
      simp_rw [volume_affine_grid_fiber (ha _) hh, div_eq_mul_inv, ← abs_inv,
        ENNReal.ofReal_mul hh.le]
      rw [Finset.mul_sum]

theorem affine_grid_collision_subset {h : ℝ} (hh : 0 < h) (a b c d : ℝ) :
    {x : ℝ | ⌊(a*x+b)/h⌋=⌊(c*x+d)/h⌋} ⊆
      {x : ℝ | |(a-c)*x+(b-d)| < h} := by
  intro x hx
  have he := Int.abs_sub_lt_one_of_floor_eq_floor hx
  rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at he
  change |(a-c)*x+(b-d)| < h
  simpa only [show a*x+b-(c*x+d)=(a-c)*x+(b-d) by ring] using he

theorem volume_affine_grid_collision {h a c : ℝ} (hh : 0 < h) (hac : a ≠ c) (b d : ℝ) :
    volume {x : ℝ | ⌊(a*x+b)/h⌋=⌊(c*x+d)/h⌋} ≤ ENNReal.ofReal (2*h/|a-c|) := by
  have he : {x : ℝ | |(a-c)*x+(b-d)| < h}=
      (fun x : ℝ => (a-c)*x+(b-d)) ⁻¹' Ioo (-h) h := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]
  calc
    _ ≤ volume {x : ℝ | |(a-c)*x+(b-d)| < h} :=
      measure_mono (affine_grid_collision_subset hh a b c d)
    _ = _ := by
      rw [he, volume_affine_preimage (sub_ne_zero.mpr hac), Real.volume_Ioo,
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      rw [abs_inv]
      ring

theorem affine_grid_collision_empty_same_slope {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (hbd : h ≤ |b-d|) : {x : ℝ | ⌊(a*x+b)/h⌋=⌊(a*x+d)/h⌋}=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he := affine_grid_collision_subset hh a b a d hx
  have hlt : |b-d| < h := by
    simpa only [Set.mem_ofPred_eq, sub_self, zero_mul, zero_add] using he
  exact (not_lt_of_ge hbd) hlt

end TransposeFollowup.AffineMotion
