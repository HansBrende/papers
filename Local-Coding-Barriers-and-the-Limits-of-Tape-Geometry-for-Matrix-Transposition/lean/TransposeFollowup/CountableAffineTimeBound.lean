import TransposeFollowup.FiniteAffineTimeBound
import Mathlib.MeasureTheory.Measure.Continuity

/-! Countably many open affine branches, with positive exceptional time.
Finite-prefix complements decrease to the actual exceptional set. Mathlib's
measure continuity passes the quantitative finite bound to that limit. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape Filter
open scoped ENNReal BigOperators Topology
set_option autoImplicit false

theorem tendsto_open_omission_prefix_sum {k : ℕ} (c₀ : ℝ)
    (J : Fin k → ℕ → Set ℝ) (hJo : ∀ t n, IsOpen (J t n)) :
    Tendsto (fun N => ∑ t, volume (Icc 0 c₀ \ ⋃ i : Fin N, J t i.val)) atTop
      (𝓝 (∑ t, volume (Icc 0 c₀ \ ⋃ n, J t n))) := by
  let E (t : Fin k) (N : ℕ) := Icc 0 c₀ \ ⋃ i : Fin N, J t i.val
  have hEc (t : Fin k) (N : ℕ) : IsCompact (E t N) :=
    isCompact_Icc.diff (isOpen_iUnion (fun i : Fin N => hJo t i.val))
  have hmono (t : Fin k) : Antitone (E t) := by
    intro N M hNM x hx
    refine ⟨hx.1,?_⟩
    intro hi
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
    exact hx.2 (Set.mem_iUnion.mpr ⟨⟨i.val,lt_of_lt_of_le i.isLt hNM⟩,hi⟩)
  have hinter (t : Fin k) : (⋂ N, E t N)=Icc 0 c₀ \ ⋃ n, J t n := by
    ext x
    constructor
    · intro hx
      have hx0 := Set.mem_iInter.mp hx 0
      refine ⟨hx0.1,?_⟩
      intro hj
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hj
      exact (Set.mem_iInter.mp hx (n+1)).2
        (Set.mem_iUnion.mpr ⟨⟨n,Nat.lt_succ_self n⟩,hn⟩)
    · rintro ⟨hx,hout⟩
      apply Set.mem_iInter.mpr
      intro N
      refine ⟨hx,?_⟩
      intro hi
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
      exact hout (Set.mem_iUnion.mpr ⟨i.val,hi⟩)
  have hlim (t : Fin k) : Tendsto (fun N => volume (E t N)) atTop
      (𝓝 (volume (Icc 0 c₀ \ ⋃ n, J t n))) := by
    have h := tendsto_measure_iInter_atTop (μ:=volume)
      (fun N => (hEc t N).measurableSet.nullMeasurableSet) (hmono t)
      ⟨0,((hEc t 0).measure_lt_top (μ:=volume)).ne⟩
    simpa only [hinter t,Function.comp_def] using h
  simpa only [E] using tendsto_finsetSum Finset.univ (fun t _ => hlim t)

theorem star_half_le_countable_affine_omission {k : ℕ} {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (a b : Fin k → ℕ → ℝ) (J : Fin k → ℕ → Set ℝ)
    (hJo : ∀ t n, IsOpen (J t n)) (hJi : ∀ t n, J t n ⊆ Icc 0 c₀)
    (hPa : ∀ t n x, x ∈ J t n → P t x=a t n*x+b t n)
    (hstar : SatisfiesStar P c₀) :
    (1/2 : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 c₀ \ ⋃ n, J t n) := by
  have hlimsum := tendsto_open_omission_prefix_sum c₀ J hJo
  apply ge_of_tendsto' hlimsum
  intro N
  exact star_half_le_finite_affine_omission hc P hP
    (fun (t : Fin k) (i : Fin N) => a t i.val) (fun (t : Fin k) (i : Fin N) => b t i.val)
    (fun (t : Fin k) (i : Fin N) => J t i.val) (fun t i => (hJo t i.val).measurableSet)
    (fun t i => hJi t i.val) (fun t => isCompact_Icc.diff (isOpen_iUnion (fun i : Fin N => hJo t i.val))) (fun t i => hPa t i.val) hstar

theorem not_star_of_countable_affine_ae_cover {k : ℕ} {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (a b : Fin k → ℕ → ℝ) (J : Fin k → ℕ → Set ℝ)
    (hJo : ∀ t n, IsOpen (J t n)) (hJi : ∀ t n, J t n ⊆ Icc 0 c₀)
    (hPa : ∀ t n x, x ∈ J t n → P t x=a t n*x+b t n)
    (hcover : ∀ t, volume (Icc 0 c₀ \ ⋃ n, J t n)=0) :
    ¬SatisfiesStar P c₀ := by
  intro hstar
  have h := star_half_le_countable_affine_omission hc P hP a b J hJo hJi hPa hstar
  simp only [hcover,Finset.sum_const_zero] at h
  norm_num at h

end TransposeFollowup.AffineMotion
