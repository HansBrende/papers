import TransposeFollowup.IncidenceFiberSelection
import TransposeFollowup.ProductDensityPairs

/-! Apply continuous fiber selection to the actual product relation,
with both measures restricted to the specified input sets. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def productIncidence (C : Set G) : Set (G × G) := {p | p.1 * p.2 ∈ C}

def productFiber (A C : Set G) (b : G) : Set G := A ∩ {a | a * b ∈ C}

omit [MeasurableInv G] in
theorem productIncidence_measurable {C : Set G} (hC : MeasurableSet C) :
    MeasurableSet (productIncidence C) := hC.preimage measurable_mul

omit [MeasurableInv G] in
theorem productIncidence_restrict_measure (σ : Measure G) [SFinite σ]
    {A B C : Set G} (hC : MeasurableSet C) :
    ((σ.restrict A).prod (σ.restrict B)) (productIncidence C) =
      (σ.prod σ) {p : G × G | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 ∈ C} := by
  rw [Measure.prod_restrict, Measure.restrict_apply (productIncidence_measurable hC)]
  congr 1
  ext p
  simp [productIncidence, and_assoc, and_comm]

omit [MeasurableInv G] in
theorem edgeFiberMass_restrict_product (σ : Measure G) {A C : Set G}
    (hC : MeasurableSet C) (b : G) :
    edgeFiberMass (σ.restrict A) (productIncidence C) b = σ (productFiber A C b) := by
  have hm : MeasurableSet {x | (x, b) ∈ productIncidence C} :=
    (productIncidence_measurable hC).preimage (by fun_prop)
  rw [edgeFiberMass_eq_measure _ (productIncidence_measurable hC),
    Measure.restrict_apply hm]
  congr 1
  ext a
  simp [productIncidence, productFiber, and_comm]

omit [MeasurableInv G] in
theorem edgeBadFiberMass_restrict_product (σ : Measure G) [SFinite σ] {A B C : Set G}
    (hC : MeasurableSet C) (t : ℝ≥0∞) (b : G) :
    edgeBadFiberMass (σ.restrict A) (σ.restrict B) (productIncidence C) t b =
      (σ.prod σ) {p : G × G | p.1 ∈ productFiber A C b ∧ p.2 ∈ productFiber A C b ∧
        edgeCodegree (σ.restrict B) (productIncidence C) p ≤ t} := by
  have he := productIncidence_measurable hC
  have hb : MeasurableSet {p : G × G | (p.1, b) ∈ productIncidence C ∧
      (p.2, b) ∈ productIncidence C ∧ edgeCodegree (σ.restrict B) (productIncidence C) p ≤ t} :=
    (he.preimage (by fun_prop)).inter ((he.preimage (by fun_prop)).inter
      (measurableSet_le (edgeCodegree_measurable _ he) measurable_const))
  rw [edgeBadFiberMass_eq_measure _ _ he, Measure.prod_restrict, Measure.restrict_apply hb]
  congr 1
  ext p
  simp [productIncidence, productFiber, and_assoc, and_comm, and_left_comm]

omit [MeasurableInv G] in
theorem exists_large_productFiber_few_low_codegrees (σ : Measure G) [SFinite σ]
    {A B C : Set G} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hA0 : 0 < σ A) (hAt : σ A < ⊤) (hB0 : 0 < σ B) (hBt : σ B < ⊤)
    {K ε : ℝ≥0∞} (hK : 0 < K) (hKt : K ≠ ⊤) (hε : 0 < ε) (hεt : ε ≠ ⊤)
    (hdense : σ A * σ B ≤ K * (σ.prod σ)
      {p : G × G | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 ∈ C}) :
    let t := ε * σ B / (2 * K ^ 2)
    ∃ b ∈ B, let S := productFiber A C b
      σ A ^ 2 < 4 * K ^ 2 * σ S ^ 2 ∧
      (σ.prod σ) {p : G × G | p.1 ∈ S ∧ p.2 ∈ S ∧
        edgeCodegree (σ.restrict B) (productIncidence C) p ≤ t} < ε * σ S ^ 2 := by
  let μ := σ.restrict A
  let ν := σ.restrict B
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hAt.ne
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hBt.ne
  obtain ⟨b, hb, hsize, hbad⟩ := exists_large_fiber_few_low_codegrees μ ν
    (productIncidence_measurable hC)
    (by simpa only [μ, Measure.restrict_apply_univ] using hA0)
    (by simpa only [ν, Measure.restrict_apply_univ] using hB0) (ae_restrict_mem hB)
    hK hKt hε hεt (by
      simpa only [μ, ν, Measure.restrict_apply_univ, productIncidence_restrict_measure σ hC] using hdense)
  refine ⟨b, hb, ?_, ?_⟩
  · simpa only [μ, Measure.restrict_apply_univ, edgeFiberMass_restrict_product σ hC] using hsize
  · simpa only [μ, ν, Measure.restrict_apply_univ, edgeFiberMass_restrict_product σ hC,
      edgeBadFiberMass_restrict_product σ hC] using hbad

end TransposeFollowup
