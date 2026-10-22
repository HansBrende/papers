import TransposeFollowup.MaskedStrideMotionBounds
import TransposeFollowup.NativePhysicalLimits

/-! If the stride is sublinear in the bank length, the endpoint-frozen
processing paths converge uniformly, even over all nonnegative times.
The bank limit is min(t/4,1); the scratch limit is stationary. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical Set Filter Topology
set_option autoImplicit false

theorem quarter_sample_error {P : ℕ} (hP : 0<P) {t : ℝ} (ht : 0≤t) :
    |((min (⌊(P : ℝ)*t⌋₊/4) P : ℕ) : ℝ)/P-min (t/4) 1| ≤ 1/(P : ℝ) := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  let n : ℕ := ⌊(P : ℝ)*t⌋₊
  let q : ℕ := n/4
  have hnl : (n : ℝ)≤(P : ℝ)*t := Nat.floor_le (mul_nonneg hp.le ht)
  have hnu : (P : ℝ)*t<(n : ℝ)+1 := Nat.lt_floor_add_one _
  have hql : (q : ℝ)*4≤(n : ℝ) := by exact_mod_cast Nat.div_mul_le_self n 4
  have hqu : (n : ℝ)+1≤((q : ℝ)+1)*4 := by
    have h : n+1≤(q+1)*4 := by dsimp [q]; omega
    exact_mod_cast h
  have he : |(q : ℝ)/P-t/4| ≤ 1/(P : ℝ) := by
    rw [show (q : ℝ)/P-t/4=((q : ℝ)-(P : ℝ)*t/4)/P by field_simp,
      abs_div,abs_of_pos hp,div_le_div_iff_of_pos_right hp,abs_le]
    constructor <;> linarith
  change |((min q P : ℕ) : ℝ)/P-min (t/4) 1| ≤ _
  rw [Nat.cast_min,← min_div_div_right hp.le,div_self hp.ne']
  have hm := (LipschitzWith.id.min_const (1 : ℝ)).dist_le_mul ((q : ℝ)/P) (t/4)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hm
  exact hm.trans he

theorem normalized_bank_error {P S : ℕ} (hP : 0<P) (hS : 0<S) {t : ℝ} (ht : 0≤t) :
    |(bankPosition P S (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) : ℝ)/P-min (t/4) 1| ≤
      ((S : ℝ)+1)/P := by
  rw [bankPosition_freeze P hS]
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  have hb : |(bankPosition P S ⌊(P : ℝ)*t⌋₊ : ℝ)-((min (⌊(P : ℝ)*t⌋₊/4) P : ℕ) : ℝ)| ≤ S := by
    exact_mod_cast bankPosition_error P hS ⌊(P : ℝ)*t⌋₊
  have hb' : |(bankPosition P S ⌊(P : ℝ)*t⌋₊ : ℝ)/P-((min (⌊(P : ℝ)*t⌋₊/4) P : ℕ) : ℝ)/P| ≤ (S : ℝ)/P := by
    rw [← sub_div,abs_div,abs_of_pos hp]
    exact div_le_div_of_nonneg_right hb hp.le
  calc
    _ ≤ |(bankPosition P S ⌊(P : ℝ)*t⌋₊ : ℝ)/P-((min (⌊(P : ℝ)*t⌋₊/4) P : ℕ) : ℝ)/P|+
        |((min (⌊(P : ℝ)*t⌋₊/4) P : ℕ) : ℝ)/P-min (t/4) 1| := abs_sub_le _ _ _
    _ ≤ (S : ℝ)/P+1/(P : ℝ) := add_le_add hb' (quarter_sample_error hP ht)
    _ = ((S : ℝ)+1)/P := by ring

theorem normalized_scratch_error {P S : ℕ} (hP : 0<P) (hS : 0<S) (t : ℝ) :
    |(scratchPosition P S (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) : ℝ)/P-0| ≤ (S : ℝ)/P := by
  have h := scratchPosition_bounds P hS (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) (Nat.min_le_right _ _)
  have hl : (0 : ℝ) ≤ scratchPosition P S (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) := by exact_mod_cast h.1
  have hu : (scratchPosition P S (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) : ℝ)≤S := by exact_mod_cast h.2
  have hp : (0 : ℝ)≤P := by positivity
  rw [sub_zero,abs_of_nonneg (div_nonneg hl hp)]
  exact div_le_div_of_nonneg_right hu hp

theorem zero_stride_uniform_limits {P S : ℕ → ℕ}
    (hP : ∀ i, 0<P i) (hS : ∀ i, 0<S i)
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hsmall : Tendsto (fun i => (S i : ℝ)/P i) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun i t =>
      (bankPosition (P i) (S i) (min ⌊(P i : ℝ)*t⌋₊ (ticks (P i) (S i))) : ℝ)/P i)
      (fun t => min (t/4) 1) atTop (Ici 0) ∧
    TendstoUniformlyOn (fun i t =>
      (scratchPosition (P i) (S i) (min ⌊(P i : ℝ)*t⌋₊ (ticks (P i) (S i))) : ℝ)/P i)
      (fun _ => 0) atTop (Ici 0) := by
  have herror : Tendsto (fun i => ((S i : ℝ)+1)/P i) atTop (𝓝 0) := by
    have hrecip : Tendsto (fun i => 1/(P i : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hPinf
    simpa only [add_div,add_zero] using hsmall.add hrecip
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [herror.eventually_lt_const hε] with i hi
    intro t ht
    simpa only [Real.dist_eq,abs_sub_comm] using (normalized_bank_error (hP i) (hS i) ht).trans_lt hi
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hsmall.eventually_lt_const hε] with i hi
    intro t _
    simpa only [Real.dist_eq,abs_sub_comm] using (normalized_scratch_error (hP i) (hS i) t).trans_lt hi

end TransposeFollowup.MaskedStrideScan
