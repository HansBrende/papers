import TransposeFollowup.FiniteAffineLabels
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Measure.Sum

/-! A finite family of actual height-parameterized pairs. The measure is
constructed by pushing forward Lebesgue height measure, so no Jacobian is
hidden in the definition. Its source marginal is bounded by the reciprocal
source slopes. Consecutiveness is unnecessary: paying for all retained
branch pairs only strengthens the cut upper bound. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

noncomputable def heightPair {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d p : ℝ) : IntervalTimePair c₀ :=
  (Set.projIcc 0 c₀ hc ((a : ℝ)*p+b), Set.projIcc 0 c₀ hc ((c : ℝ)*p+d))

theorem measurable_heightPair {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d : ℝ) : Measurable (heightPair hc a c b d) := by
  exact ((continuous_projIcc.comp (by fun_prop)).prodMk
    (continuous_projIcc.comp (by fun_prop))).measurable

theorem heightPair_on_domain {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d p : ℝ)
    (hu : (a : ℝ)*p+b ∈ Icc 0 c₀) (hv : (c : ℝ)*p+d ∈ Icc 0 c₀) :
    (heightPair hc a c b d p).1.val=(a : ℝ)*p+b ∧
    (heightPair hc a c b d p).2.val=(c : ℝ)*p+d := by
  simp [heightPair,Set.projIcc_of_mem hc hu,Set.projIcc_of_mem hc hv]

noncomputable def heightPairMeasure {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d : ℝ) (D : Set ℝ) : Measure (IntervalTimePair c₀) :=
  (volume.restrict D).map (heightPair hc a c b d)

theorem heightPairMeasure_apply {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d : ℝ) (D : Set ℝ)
    (E : Set (IntervalTimePair c₀)) (hE : MeasurableSet E) :
    heightPairMeasure hc a c b d D E=
      volume ((heightPair hc a c b d ⁻¹' E) ∩ D) := by
  rw [heightPairMeasure,Measure.map_apply (measurable_heightPair hc a c b d) hE,
    Measure.restrict_apply ((measurable_heightPair hc a c b d) hE)]

theorem heightPairMeasure_source {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d : ℝ) (D : Set ℝ)
    (hD : ∀ p ∈ D, (a : ℝ)*p+b ∈ Icc 0 c₀ ∧ (c : ℝ)*p+d ∈ Icc 0 c₀)
    (E : Set ℝ) (hE : MeasurableSet E) :
    heightPairMeasure hc a c b d D {q | q.1.val ∈ E} ≤
      ENNReal.ofReal |((a : ℝ))⁻¹| *volume E := by
  have hset : MeasurableSet {q : IntervalTimePair c₀ | q.1.val ∈ E} := hE.preimage (by fun_prop)
  rw [heightPairMeasure_apply hc a c b d D _ hset]
  calc
    _ ≤ volume ((fun p : ℝ => (a : ℝ)*p+b) ⁻¹' E) := by
      apply measure_mono
      rintro p ⟨hp,hpD⟩
      change (heightPair hc a c b d p).1.val ∈ E at hp
      rw [(heightPair_on_domain hc a c b d p (hD p hpD).1 (hD p hpD).2).1] at hp
      exact hp
    _ = _ := volume_affine_preimage a.ne_zero b E

theorem heightPairMeasure_cut {c₀ : ℝ} (hc : 0 ≤ c₀)
    (a c : ℝˣ) (b d : ℝ) (D : Set ℝ)
    (hD : ∀ p ∈ D, (a : ℝ)*p+b ∈ Icc 0 c₀ ∧ (c : ℝ)*p+d ∈ Icc 0 c₀)
    (β : ℝ → ℕ) (hβ : Measurable β) :
    heightPairMeasure hc a c b d D {q | β q.1.val ≠ β q.2.val}=
      volume {p | p ∈ D ∧ β ((a : ℝ)*p+b) ≠ β ((c : ℝ)*p+d)} := by
  have hset : MeasurableSet {q : IntervalTimePair c₀ | β q.1.val ≠ β q.2.val} :=
    (measurableSet_eq_fun (hβ.comp (by fun_prop)) (hβ.comp (by fun_prop))).compl
  rw [heightPairMeasure_apply hc a c b d D _ hset]
  congr 1
  ext p
  constructor
  · rintro ⟨hp,hpD⟩
    have he := heightPair_on_domain hc a c b d p (hD p hpD).1 (hD p hpD).2
    exact ⟨hpD,by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,he.1,he.2] using hp⟩
  · rintro ⟨hpD,hp⟩
    have he := heightPair_on_domain hc a c b d p (hD p hpD).1 (hD p hpD).2
    exact ⟨by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,he.1,he.2] using hp,hpD⟩

theorem exists_small_height_pair_cut {ι : Type*} [Fintype ι]
    {c₀ : ℝ} (hc : 0 ≤ c₀) (a c : ι → ℝˣ) (b d : ι → ℝ) (D : ι → Set ℝ)
    (hD : ∀ j p, p ∈ D j →
      (a j : ℝ)*p+b j ∈ Icc 0 c₀ ∧ (c j : ℝ)*p+d j ∈ Icc 0 c₀)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ Transpose.Tape.PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ j, volume {p | p ∈ D j ∧ β ((a j : ℝ)*p+b j) ≠ β ((c j : ℝ)*p+d j)}) <
        ENNReal.ofReal ε := by
  let μj (j : ι) := heightPairMeasure hc (a j) (c j) (b j) (d j) (D j)
  let μ : Measure (IntervalTimePair c₀) := Measure.sum μj
  let κ : ℝ := ∑ j, |((a j : ℝ))⁻¹|
  have hκ : 0 ≤ κ := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hmarg (E : Set ℝ) (hE : MeasurableSet E) :
      μ {q | q.1.val ∈ E} ≤ ENNReal.ofReal κ*volume E := by
    have hset : MeasurableSet {q : IntervalTimePair c₀ | q.1.val ∈ E} := hE.preimage (by fun_prop)
    rw [show μ=Measure.sum μj from rfl,Measure.sum_apply _ hset,
      tsum_fintype]
    calc
      _ ≤ ∑ j, ENNReal.ofReal |((a j : ℝ))⁻¹| *volume E :=
        Finset.sum_le_sum (fun j _ => heightPairMeasure_source hc (a j) (c j) (b j) (d j)
          (D j) (hD j) E hE)
      _ = _ := by rw [← Finset.sum_mul,ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _)]
  have hmass : μ univ ≤ ENNReal.ofReal κ*ENNReal.ofReal c₀ := by
    have he : {q : IntervalTimePair c₀ | q.1.val ∈ Icc 0 c₀}=univ := by
      ext q
      simp only [Set.mem_ofPred_eq,q.1.property,Set.mem_univ]
    simpa only [he,Real.volume_Icc,sub_zero] using hmarg (Icc 0 c₀) measurableSet_Icc
  let : IsFiniteMeasure μ := ⟨hmass.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ENNReal.ofReal_lt_top)⟩
  let s (j : ι) : ℝˣ := c j / a j
  let e (j : ι) : ℝ := d j - (s j : ℝ)*b j
  have hsupp : μ (finiteReturnGraphs s e c₀)ᶜ=0 := by
    rw [show μ=Measure.sum μj from rfl,Measure.sum_apply_eq_zero]
    intro j
    rw [show μj j=heightPairMeasure hc (a j) (c j) (b j) (d j) (D j) from rfl,
      heightPairMeasure_apply hc (a j) (c j) (b j) (d j) (D j) _
        (measurableSet_finiteReturnGraphs s e c₀).compl]
    apply measure_mono_null (t:=∅) _ (measure_empty)
    rintro p ⟨hp,hpD⟩
    apply hp
    refine ⟨j,?_⟩
    have he := heightPair_on_domain hc (a j) (c j) (b j) (d j) p
      (hD j p hpD).1 (hD j p hpD).2
    rw [he.1,he.2]
    dsimp [e,s]
    simp only [Units.val_div_eq_div_val]
    field_simp
    ring
  obtain ⟨β,hβ,hpc,hm,hcut⟩ := exists_finite_affine_small_cut s e c₀ μ hκ hsupp hmarg hθ hε
  refine ⟨β,hβ,hpc,hm,?_⟩
  have hset : MeasurableSet {q : IntervalTimePair c₀ | β q.1.val ≠ β q.2.val} :=
    (measurableSet_eq_fun (hβ.comp (by fun_prop)) (hβ.comp (by fun_prop))).compl
  rw [show μ=Measure.sum μj from rfl,Measure.sum_apply _ hset,
    tsum_fintype] at hcut
  simpa only [μj,heightPairMeasure_cut hc _ _ _ _ _ (hD _) β hβ] using hcut

end TransposeFollowup.AffineMotion
