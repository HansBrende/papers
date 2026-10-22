import TransposeFollowup.RawMaskedStrideMotion
import TransposeFollowup.MaskedStrideAffineApproximation

/-! Bounded-piece approximations of the actual raw-input processing window.
A positive normalized stride gives an eventual bound on group count. This
is the input required by the existing affine-approximation obstruction;
the outer raw phases and composition remain separate obligations. -/
namespace TransposeFollowup.RawMaskedStride
open Classical Set Filter Topology AffineMotion
set_option autoImplicit false

theorem processing_bounded_affine_approximation {P S B : ℕ}
    (hP : 0<P) (hS : 0<S) (hB : P/S ≤ B) {H : ℝ} (hH : 0 ≤ H)
    (isPrefix : Bool) (mask : ℕ → Bool) (w : List Bool) :
    HasAffineIntervalCover (9^(B+1)) (fun t => MaskedStrideScan.bankCurve P S ((P : ℝ)*t)/P) H ∧
    HasAffineIntervalCover (9^(B+1)) (fun t => MaskedStrideScan.scratchCurve P S ((P : ℝ)*t)/P) H ∧
    ∀ t : ℝ,
      |(Transpose.Tape.workTraj (machine isPrefix mask P S) w
          (4*P+min ⌊(P : ℝ)*t⌋₊ (MaskedStrideScan.ticks P S)) ((encoding P S).port 0) : ℝ)/P-
        MaskedStrideScan.bankCurve P S ((P : ℝ)*t)/P| ≤ 2*((B : ℝ)+1)/P ∧
      |(Transpose.Tape.workTraj (machine isPrefix mask P S) w
          (4*P+min ⌊(P : ℝ)*t⌋₊ (MaskedStrideScan.ticks P S)) ((encoding P S).port 1) : ℝ)/P-
        MaskedStrideScan.scratchCurve P S ((P : ℝ)*t)/P| ≤ 2*((B : ℝ)+1)/P := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  have hc := MaskedStrideScan.bounded_curve_covers P S B hB (mul_nonneg hp.le hH)
  refine ⟨hc.1.rescale hp,hc.2.rescale hp,fun t => ?_⟩
  have he := MaskedStrideScan.normalized_curve_errors hP hS t
  have hn := processing_workTraj isPrefix mask P hS w
    (min ⌊(P : ℝ)*t⌋₊ (MaskedStrideScan.ticks P S)) (Nat.min_le_right _ _)
  have hb := congrArg (fun z : ℤ => (z : ℝ)/P) hn.1
  simp only [Int.cast_natCast] at hb
  have hs := congrArg (fun z : ℤ => (z : ℝ)/P) hn.2
  have hqb : ((P/S : ℕ) : ℝ) ≤ B := by exact_mod_cast hB
  constructor
  · exact (congrArg (fun z : ℝ => |z-MaskedStrideScan.bankCurve P S ((P : ℝ)*t)/P|) hb).trans_le
      (he.1.trans (div_le_div_of_nonneg_right (by linarith) hp.le))
  · exact (congrArg (fun z : ℝ => |z-MaskedStrideScan.scratchCurve P S ((P : ℝ)*t)/P|) hs).trans_le
      (he.2.trans (div_le_div_of_nonneg_right (by linarith) hp.le))

theorem eventually_bounded_groups {P S : ℕ → ℕ} (hP : ∀ i, 0<P i)
    {α : ℝ} (hα : 0<α) (hratio : Tendsto (fun i => (S i : ℝ)/P i) atTop (𝓝 α)) :
    ∃ B : ℕ, ∀ᶠ i in atTop, P i/S i ≤ B := by
  refine ⟨⌈2/α⌉₊,?_⟩
  filter_upwards [hratio.eventually_const_lt (show α/2<α by linarith)] with i hi
  have hp : (0 : ℝ)<P i := by exact_mod_cast hP i
  have hq : ((P i/S i : ℕ) : ℝ)*(S i : ℝ) ≤ P i := by
    exact_mod_cast Nat.div_mul_le_self (P i) (S i)
  have hq' : ((P i/S i : ℕ) : ℝ)*((S i : ℝ)/P i) ≤ 1 := by
    rw [← mul_div_assoc,div_le_one hp]
    exact hq
  have hm := mul_le_mul_of_nonneg_left hi.le (Nat.cast_nonneg (P i/S i) : (0 : ℝ) ≤ (P i/S i : ℕ))
  have hb : ((P i/S i : ℕ) : ℝ) ≤ 2/α := (le_div_iff₀ hα).mpr (by nlinarith)
  exact_mod_cast hb.trans (Nat.le_ceil (2/α))

theorem positive_stride_processing_approximation {P S : ℕ → ℕ}
    (hP : ∀ i, 0<P i) (hS : ∀ i, 0<S i)
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    {α : ℝ} (hα : 0<α) (hratio : Tendsto (fun i => (S i : ℝ)/P i) atTop (𝓝 α))
    (modes : ℕ → Bool) (masks : ℕ → ℕ → Bool) (inputs : ℕ → List Bool)
    {H : ℝ} (hH : 0 ≤ H) :
    ∃ (J : ℕ) (e : ℕ → ℝ) (b s : ℕ → ℝ → ℝ),
      Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ i in atTop, HasAffineIntervalCover J (b i) H ∧ HasAffineIntervalCover J (s i) H ∧
        ∀ t : ℝ,
          |(Transpose.Tape.workTraj (machine (modes i) (masks i) (P i) (S i)) (inputs i)
              (4*P i+min ⌊(P i : ℝ)*t⌋₊ (MaskedStrideScan.ticks (P i) (S i)))
              ((encoding (P i) (S i)).port 0) : ℝ)/P i-b i t| ≤ e i ∧
          |(Transpose.Tape.workTraj (machine (modes i) (masks i) (P i) (S i)) (inputs i)
              (4*P i+min ⌊(P i : ℝ)*t⌋₊ (MaskedStrideScan.ticks (P i) (S i)))
              ((encoding (P i) (S i)).port 1) : ℝ)/P i-s i t| ≤ e i := by
  obtain ⟨B,hB⟩ := eventually_bounded_groups hP hα hratio
  refine ⟨9^(B+1),fun i => 2*((B : ℝ)+1)/P i,
    fun i t => MaskedStrideScan.bankCurve (P i) (S i) ((P i : ℝ)*t)/P i,
    fun i t => MaskedStrideScan.scratchCurve (P i) (S i) ((P i : ℝ)*t)/P i,
    tendsto_const_nhds.div_atTop hPinf,?_⟩
  filter_upwards [hB] with i hi
  exact processing_bounded_affine_approximation (hP i) (hS i) hi hH (modes i) (masks i) (inputs i)

end TransposeFollowup.RawMaskedStride
