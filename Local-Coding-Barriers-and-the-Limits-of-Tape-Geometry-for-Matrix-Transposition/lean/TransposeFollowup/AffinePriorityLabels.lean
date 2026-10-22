import TransposeFollowup.AffineGridIntervals
import TransposeFollowup.AffineGridMass
import TransposeFollowup.FiniteMinimumCoupling
import Mathlib.MeasureTheory.Function.Floor

/-! Concrete natural-valued priority labels, with measurability, the original
finite-breakpoint condition and a uniform class-mass bound for every ordering.
The return-cut estimate is a separate remaining obligation. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

variable {ι : Type*} [Fintype ι]

noncomputable def gridSample (C : Finset ℤ) (q : ι → ℤ) : Finset C :=
  Finset.univ.filter (fun z => ∃ i, q i=z.val)

noncomputable def gridPriority (C : Finset ℤ) (σ : Equiv.Perm C) (q : ι → ℤ) : ℤ :=
  if hs : (gridSample C q).Nonempty then
    (FiniteMinimumCoupling.first σ (gridSample C q) hs).val else 0

theorem gridSample_nonempty [Nonempty ι] (C : Finset ℤ) (q : ι → ℤ)
    (hq : ∀ i, q i ∈ C) : (gridSample C q).Nonempty := by
  let i : ι := Classical.choice inferInstance
  refine ⟨⟨q i,hq i⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,rfl⟩

theorem gridPriority_eq_first (C : Finset ℤ) (σ : Equiv.Perm C) (q : ι → ℤ)
    (hq : (gridSample C q).Nonempty) :
    gridPriority C σ q=(FiniteMinimumCoupling.first σ (gridSample C q) hq).val := by
  simp only [gridPriority, dite_eq_left hq]


theorem encoded_gridPriority_ne_iff (C : Finset ℤ) (σ : Equiv.Perm C) (q r : ι → ℤ)
    (hq : (gridSample C q).Nonempty) (hr : (gridSample C r).Nonempty) :
    Encodable.encode (gridPriority C σ q) ≠ Encodable.encode (gridPriority C σ r) ↔
      FiniteMinimumCoupling.first σ (gridSample C q) hq ≠
        FiniteMinimumCoupling.first σ (gridSample C r) hr := by
  rw [gridPriority_eq_first C σ q hq,gridPriority_eq_first C σ r hr]
  constructor
  · intro hne he
    exact hne (congrArg (fun z : C => Encodable.encode z.val) he)
  · intro hne he
    exact hne (Subtype.ext (Encodable.encode_injective he))

theorem gridPriority_selects [Nonempty ι] (C : Finset ℤ) (σ : Equiv.Perm C)
    (q : ι → ℤ) (hq : ∀ i, q i ∈ C) : ∃ i, gridPriority C σ q=q i := by
  let hs := gridSample_nonempty C q hq
  have hm := FiniteMinimumCoupling.first_mem σ (gridSample C q) hs
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hm).2
  exact ⟨i,(gridPriority_eq_first C σ q hs).trans hi.symm⟩

theorem measurable_affine_grid_postprocess {α : Type*} [MeasurableSpace α]
    (a b : ι → ℝ) (h : ℝ) (label : (ι → ℤ) → α) :
    Measurable (fun x : ℝ => label (fun i => ⌊(a i*x+b i)/h⌋)) := by
  apply (measurable_of_countable label).comp
  apply Measurable.of_eval
  intro i
  exact (show Measurable (fun x : ℝ => (a i*x+b i)/h) by fun_prop).floor

theorem encoded_selected_grid_label_mass
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) {h : ℝ} (hh : 0 < h)
    (I : Set ℝ) (label : ℝ → ℤ)
    (hselect : ∀ x ∈ I, ∃ i, label x=⌊(a i*x+b i)/h⌋) (n : ℕ) :
    volume {x | x ∈ I ∧ Encodable.encode (label x)=n} ≤
      ENNReal.ofReal h*∑ i, ENNReal.ofReal |(a i)⁻¹| := by
  by_cases he : ({x | x ∈ I ∧ Encodable.encode (label x)=n} : Set ℝ).Nonempty
  · obtain ⟨x₀,hx₀⟩ := he
    have hsub : {x | x ∈ I ∧ Encodable.encode (label x)=n} ⊆
        {x | x ∈ I ∧ label x=label x₀} := by
      intro x hx
      exact ⟨hx.1,Encodable.encode_injective (hx.2.trans hx₀.2.symm)⟩
    exact (measure_mono hsub).trans (selected_affine_grid_label_mass a b ha hh I label hselect _)
  · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
    exact bot_le

theorem affine_priority_label_properties [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) {h : ℝ} (hh : 0 < h) (c₀ : ℝ)
    (C : Finset ℤ) (hC : ∀ i x, x ∈ Set.Icc 0 c₀ → ⌊(a i*x+b i)/h⌋ ∈ C)
    (σ : Equiv.Perm C) :
    let β := fun x : ℝ => Encodable.encode (gridPriority C σ (fun i => ⌊(a i*x+b i)/h⌋))
    Measurable β ∧ Transpose.Tape.PiecewiseConstOn β ∅ c₀ ∧
      ∀ n, volume {x | x ∈ Set.Icc 0 c₀ ∧ β x=n} ≤
        ENNReal.ofReal h*∑ i, ENNReal.ofReal |(a i)⁻¹| := by
  refine ⟨measurable_affine_grid_postprocess a b h (fun q => Encodable.encode (gridPriority C σ q)),
    piecewiseConstOn_affine_grid a b ha hh.ne' c₀ (fun q => Encodable.encode (gridPriority C σ q)),
    fun n => ?_⟩
  apply encoded_selected_grid_label_mass a b ha hh
  intro x hx
  exact gridPriority_selects C σ _ (fun i => hC i x hx)

theorem exists_affine_priority_universe [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0) {h : ℝ} (hh : 0 < h) (c₀ : ℝ) :
    ∃ C : Finset ℤ,
      (∀ i x, x ∈ Set.Icc 0 c₀ → ⌊(a i*x+b i)/h⌋ ∈ C) ∧
      ∀ σ : Equiv.Perm C,
        let β := fun x : ℝ => Encodable.encode (gridPriority C σ (fun i => ⌊(a i*x+b i)/h⌋))
        Measurable β ∧ Transpose.Tape.PiecewiseConstOn β ∅ c₀ ∧
          ∀ n, volume {x | x ∈ Set.Icc 0 c₀ ∧ β x=n} ≤
            ENNReal.ofReal h*∑ i, ENNReal.ofReal |(a i)⁻¹| := by
  obtain ⟨C,hC⟩ := exists_finite_affine_grid_range a b h c₀
  exact ⟨C,hC,fun σ => affine_priority_label_properties a b ha hh c₀ C hC σ⟩

end TransposeFollowup.AffineMotion
