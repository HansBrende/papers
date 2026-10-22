import TransposeFollowup.CountableAffineTimeBound

/-! The full small-class/small-cut path statement, not merely its M*
contradiction. Finite-prefix approximation retains the original countable
scope and charges positive exceptional time with coefficient two. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape Filter
open scoped ENNReal BigOperators Topology
set_option autoImplicit false

theorem exists_countable_affine_path_cut_bound {k : ℕ} {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (a b : Fin k → ℕ → ℝ) (J : Fin k → ℕ → Set ℝ)
    (hJo : ∀ t n, IsOpen (J t n)) (hJi : ∀ t n, J t n ⊆ Icc 0 c₀)
    (hPa : ∀ t n x, x ∈ J t n → P t x=a t n*x+b t n)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ t, ∫⁻ p, levelCross (P t) ∅ β c₀ p) <
        2*(∑ t, volume (Icc 0 c₀ \ ⋃ n, J t n))+ENNReal.ofReal ε := by
  let B : ℝ≥0∞ := ∑ t, volume (Icc 0 c₀ \ ⋃ n, J t n)
  have hB : B ≠ ∞ := ENNReal.sum_ne_top.mpr (fun t _ =>
    ((isCompact_Icc.diff (isOpen_iUnion (hJo t))).measure_lt_top (μ:=volume)).ne)
  have heq : 0 < ENNReal.ofReal (ε/4) := ENNReal.ofReal_pos.mpr (by positivity)
  have hlim := tendsto_open_omission_prefix_sum c₀ J hJo
  obtain ⟨N,hN⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.lt_add_right hB heq.ne'))).exists
  let JN (t : Fin k) (i : Fin N) := J t i.val
  have hEc (t : Fin k) : IsCompact (Icc 0 c₀ \ ⋃ i, JN t i) :=
    isCompact_Icc.diff (isOpen_iUnion (fun i : Fin N => hJo t i.val))
  obtain ⟨β,hβ,hpc,hm,hcut⟩ := exists_finite_affine_branch_small_cut hc P
    (fun (t : Fin k) (i : Fin N) => a t i.val)
    (fun (t : Fin k) (i : Fin N) => b t i.val) JN
    (fun t i => (hJo t i.val).measurableSet) (fun t i => hJi t i.val)
    (fun t i => hPa t i.val) hθ (show 0 < ε/2 by positivity)
  refine ⟨β,hβ,hpc,hm,?_⟩
  have hfinite : 2*(∑ t, volume (Icc 0 c₀ \ ⋃ i, JN t i)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.sum_ne_top.mpr (fun t _ => ((hEc t).measure_lt_top (μ:=volume)).ne))
  have herr : ENNReal.ofReal (ε/2)+2*ENNReal.ofReal (ε/4)=ENNReal.ofReal ε := by
    rw [show (2 : ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ ≤ ∑ t, ((∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, JN t i ∧ q.2 ∈ ⋃ i, JN t i}.ncard : ℝ≥0∞))+
          2*volume (Icc 0 c₀ \ ⋃ i, JN t i)) :=
      Finset.sum_le_sum (fun t _ => lintegral_levelCross_delete_le (hP t) β _ (hEc t))
    _ = (∑ t, ∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, JN t i ∧ q.2 ∈ ⋃ i, JN t i}.ncard : ℝ≥0∞))+
          2*∑ t, volume (Icc 0 c₀ \ ⋃ i, JN t i) := by rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ < ENNReal.ofReal (ε/2)+2*(∑ t, volume (Icc 0 c₀ \ ⋃ i, JN t i)) :=
      ENNReal.add_lt_add_right hfinite hcut
    _ ≤ ENNReal.ofReal (ε/2)+2*(B+ENNReal.ofReal (ε/4)) :=
      add_le_add le_rfl (mul_le_mul' (le_refl 2) hN.le)
    _ = 2*B+(ENNReal.ofReal (ε/2)+2*ENNReal.ofReal (ε/4)) := by ring
    _ = _ := by rw [herr]

theorem exists_countable_affine_path_small_cut {k : ℕ} {c₀ : ℝ}
    (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (a b : Fin k → ℕ → ℝ) (J : Fin k → ℕ → Set ℝ)
    (hJo : ∀ t n, IsOpen (J t n)) (hJi : ∀ t n, J t n ⊆ Icc 0 c₀)
    (hPa : ∀ t n x, x ∈ J t n → P t x=a t n*x+b t n)
    (hcover : ∀ t, volume (Icc 0 c₀ \ ⋃ n, J t n)=0)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ t, ∫⁻ p, levelCross (P t) ∅ β c₀ p) < ENNReal.ofReal ε := by
  simpa only [hcover,Finset.sum_const_zero,mul_zero,zero_add] using
    exists_countable_affine_path_cut_bound hc P hP a b J hJo hJi hPa hθ hε

end TransposeFollowup.AffineMotion
