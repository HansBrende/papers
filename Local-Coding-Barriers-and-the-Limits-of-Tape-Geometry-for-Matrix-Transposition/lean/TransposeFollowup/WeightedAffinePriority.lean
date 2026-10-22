import TransposeFollowup.AffineSampleBoundary
import TransposeFollowup.WeightedMinimumCoupling

/-! One actual admissible priority label for a weighted finite affine-return
family. The measure lives on interval-time pairs, so the samples are nonempty
everywhere in its domain. Graph-support exceptions and source collision mass
are both charged explicitly. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

abbrev IntervalTime (c₀ : ℝ) := {x : ℝ // x ∈ Set.Icc 0 c₀}
abbrev IntervalTimePair (c₀ : ℝ) := IntervalTime c₀ × IntervalTime c₀

def finiteReturnGraphs {ι : Type*} (s : ι → ℝˣ) (b : ι → ℝ) (c₀ : ℝ) :
    Set (IntervalTimePair c₀) := {p | ∃ j, p.2.val=(s j : ℝ)*p.1.val+b j}

theorem measurableSet_finiteReturnGraphs {ι : Type*} [Countable ι]
    (s : ι → ℝˣ) (b : ι → ℝ) (c₀ : ℝ) : MeasurableSet (finiteReturnGraphs s b c₀) := by
  have he : finiteReturnGraphs s b c₀=
      ⋃ j, {p : IntervalTimePair c₀ | p.2.val=(s j : ℝ)*p.1.val+b j} := by
    ext p
    simp only [finiteReturnGraphs,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion (fun j => measurableSet_eq_fun (by fun_prop) (by fun_prop))

noncomputable def affineCommonFamily {ι : Type*} [Fintype ι]
    (F : Finset (ℝˣ × ℝ)) (s : ι → ℝˣ) (b : ι → ℝ) : Finset (ℝˣ × ℝ) :=
  F ∪ Finset.univ.biUnion (fun j => F.image (FiniteBoundary.affineRight (s j) (b j)))

theorem local_collision_avoided_of_common {ι : Type*} [Fintype ι]
    (F : Finset (ℝˣ × ℝ)) (s : ι → ℝˣ) (b : ι → ℝ) (h x : ℝ) (j : ι)
    (hx : x ∉ gridCollisions
      (fun p : affineCommonFamily F s b => (p.val.1 : ℝ))
      (fun p : affineCommonFamily F s b => p.val.2) h) :
    x ∉ gridCollisions
      (fun p : ↥(F ∪ F.image (FiniteBoundary.affineRight (s j) (b j))) => (p.val.1 : ℝ))
      (fun p : ↥(F ∪ F.image (FiniteBoundary.affineRight (s j) (b j))) => p.val.2) h := by
  have hs : F ∪ F.image (FiniteBoundary.affineRight (s j) (b j)) ⊆ affineCommonFamily F s b := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hp⟩)
  have hi := affine_grid_injOn_off_collisions (affineCommonFamily F s b) h x hx
  apply grid_not_mem_collisions_of_injective
  intro p q he
  apply Subtype.ext
  exact hi (hs p.property) (hs q.property) he

theorem exists_weighted_affine_priority_label {ι : Type*} [Fintype ι]
    (s : ι → ℝˣ) (b : ι → ℝ) (F : Finset (ℝˣ × ℝ)) (hF : F.Nonempty)
    {h : ℝ} (hh : 0 < h) (c₀ : ℝ) (δ κ : ℝ≥0∞)
    (hδ : ∀ j, (((F ∪ F.image (FiniteBoundary.affineRight (s j) (b j))) \
      (F ∩ F.image (FiniteBoundary.affineRight (s j) (b j)))).card : ℝ≥0∞) ≤
      δ*(F ∪ F.image (FiniteBoundary.affineRight (s j) (b j))).card)
    (μ : Measure (IntervalTimePair c₀))
    (hsupport : μ (finiteReturnGraphs s b c₀)ᶜ=0)
    (hmarginal : ∀ E : Set ℝ, MeasurableSet E → μ {p | p.1.val ∈ E} ≤ κ*volume E) :
    ∃ β : ℝ → ℕ, Measurable β ∧ Transpose.Tape.PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Set.Icc 0 c₀ ∧ β x=n} ≤
        ENNReal.ofReal h*∑ f : F, ENNReal.ofReal |((f.val.1 : ℝ))⁻¹|) ∧
      μ {p | β p.1.val ≠ β p.2.val} ≤ δ*μ Set.univ+
        κ*volume (gridCollisions
          (fun f : affineCommonFamily F s b => (f.val.1 : ℝ))
          (fun f : affineCommonFamily F s b => f.val.2) h) := by
  let : Nonempty F := ⟨⟨hF.choose,hF.choose_spec⟩⟩
  let a : F → ℝ := fun f => (f.val.1 : ℝ)
  let d : F → ℝ := fun f => f.val.2
  have ha (f : F) : a f ≠ 0 := f.val.1.ne_zero
  obtain ⟨C,hC⟩ := exists_finite_affine_grid_range a d h c₀
  let A (p : IntervalTimePair c₀) := gridSample C (fun f : F => affineGridValue h p.1.val f.val)
  let B (p : IntervalTimePair c₀) := gridSample C (fun f : F => affineGridValue h p.2.val f.val)
  have hA (p : IntervalTimePair c₀) : (A p).Nonempty :=
    gridSample_nonempty C _ (fun f => hC f p.1.val p.1.property)
  have hB (p : IntervalTimePair c₀) : (B p).Nonempty :=
    gridSample_nonempty C _ (fun f => hC f p.2.val p.2.property)
  let label (σ : Equiv.Perm C) (x : ℝ) :=
    Encodable.encode (gridPriority C σ (fun f : F => affineGridValue h x f.val))
  have hlabel (σ : Equiv.Perm C) : Measurable (label σ) ∧
      Transpose.Tape.PiecewiseConstOn (label σ) ∅ c₀ ∧
      ∀ n, volume {x | x ∈ Set.Icc 0 c₀ ∧ label σ x=n} ≤
        ENNReal.ofReal h*∑ f : F, ENNReal.ofReal |((f.val.1 : ℝ))⁻¹| :=
    affine_priority_label_properties a d ha hh c₀ C hC σ
  let badTimes := gridCollisions
    (fun f : affineCommonFamily F s b => (f.val.1 : ℝ))
    (fun f : affineCommonFamily F s b => f.val.2) h
  have htimes : MeasurableSet badTimes := measurableSet_gridCollisions _ _ _
  let badPairs : Set (IntervalTimePair c₀) :=
    {p | p.1.val ∈ badTimes} ∪ (finiteReturnGraphs s b c₀)ᶜ
  have hbad : MeasurableSet badPairs :=
    (htimes.preimage (by fun_prop)).union (measurableSet_finiteReturnGraphs s b c₀).compl
  have hbadmass : μ badPairs ≤ κ*volume badTimes := by
    calc
      _ ≤ μ {p | p.1.val ∈ badTimes}+μ (finiteReturnGraphs s b c₀)ᶜ := measure_union_le _ _
      _ ≤ κ*volume badTimes := by rw [hsupport,add_zero]; exact hmarginal badTimes htimes
  have hratio (p : IntervalTimePair c₀) (hp : p ∉ badPairs) :
      (((A p ∪ B p) \ (A p ∩ B p)).card : ℝ≥0∞) ≤ δ*(A p ∪ B p).card := by
    have hx : p.1.val ∉ badTimes := fun hx => hp (Set.mem_union_left _ hx)
    have hg : p ∈ finiteReturnGraphs s b c₀ := by
      by_contra hn
      exact hp (Set.mem_union_right _ hn)
    obtain ⟨j,hj⟩ := hg
    dsimp only [A,B]
    have ht := affine_priority_samples_boundary F (s j) (b j) h p.1.val C
      (fun f => hC f p.1.val p.1.property)
      (fun f => by rw [← hj]; exact hC f p.2.val p.2.property) δ (hδ j)
      (local_collision_avoided_of_common F s b h p.1.val j hx)
    simpa only [hj] using ht
  have hevent (σ : Equiv.Perm C) :
      {p | FiniteMinimumCoupling.first σ (A p) (hA p) ≠
        FiniteMinimumCoupling.first σ (B p) (hB p)}=
      {p : IntervalTimePair c₀ | label σ p.1.val ≠ label σ p.2.val} := by
    ext p
    exact (encoded_gridPriority_ne_iff C σ _ _ (hA p) (hB p)).symm
  have hmeas (σ : Equiv.Perm C) :
      MeasurableSet {p | FiniteMinimumCoupling.first σ (A p) (hA p) ≠
        FiniteMinimumCoupling.first σ (B p) (hB p)} := by
    rw [hevent σ]
    exact (measurableSet_eq_fun ((hlabel σ).1.comp (by fun_prop))
      ((hlabel σ).1.comp (by fun_prop))).compl
  obtain ⟨σ,hσ⟩ := FiniteMinimumCoupling.exists_small_weighted_disagreement
    μ A B hA hB badPairs hbad δ hratio hmeas
  refine ⟨label σ,(hlabel σ).1,(hlabel σ).2.1,(hlabel σ).2.2,?_⟩
  rw [hevent σ] at hσ
  exact hσ.trans (add_le_add le_rfl hbadmass)

end TransposeFollowup.AffineMotion
