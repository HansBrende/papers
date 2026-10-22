import TransposeFollowup.RawMaskedStrideCurves

/-! A fixed five-ramp comparison for the complete small-stride execution.
The processing duration and final phase offsets differ from their nominal
values by O(S); all such shifts are paid in the explicit error bound. -/
namespace TransposeFollowup.RawMaskedStride
open Classical Set Filter Topology AffineMotion
set_option autoImplicit false

theorem clippedRamp_start_error (L a b d t : ℝ) (hd : 0<d) :
    |clippedRamp L a d t-clippedRamp L b d t| ≤ |a-b|/d := by
  have h := ((LipschitzWith.id.max_const (0 : ℝ)).min_const L).dist_le_mul ((t-a)/d) ((t-b)/d)
  have he : (t-a)/d-(t-b)/d=-(a-b)/d := by ring
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul,he,abs_div,abs_neg,abs_of_pos hd,clippedRamp,id_eq] using h

noncomputable def smallBankApproximation (P : ℕ) (t : ℝ) : ℝ :=
  clippedRamp P 0 3 t-clippedRamp P (3*P : ℕ) 1 t+
    clippedRamp P (4*P : ℕ) 4 t-clippedRamp P (8*P : ℕ) 1 t+
    clippedRamp P (9*P : ℕ) 3 t

theorem smallBankApproximation_cover (P : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    HasAffineIntervalCover 243 (smallBankApproximation P) H :=
  ((((clippedRamp_cover hH (by positivity) (le_refl (0 : ℝ)) (show (0 : ℝ)<3 by norm_num)).sub
    (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).add
    (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<4 by norm_num))).sub
    (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).add
    (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num))

theorem smallBankApproximation_error (P : ℕ) {S : ℕ} (hS : 0<S) (t : ℝ) :
    |(bankPath P S ⌊t⌋₊ : ℝ)-smallBankApproximation P t| ≤ 9*(S : ℝ)+6 := by
  have hn := MaskedStrideScan.ticks_bounds P hS
  have hn0 : 4*(P : ℝ) ≤ MaskedStrideScan.ticks P S := by exact_mod_cast hn.1
  have hn1 : (MaskedStrideScan.ticks P S : ℝ) ≤ 4*(P : ℝ)+4*S := by exact_mod_cast hn.2
  have hR : |((4*P+MaskedStrideScan.ticks P S+2*S : ℕ) : ℝ)-(8*P : ℕ)| ≤ 6*(S : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hO : |((5*P+MaskedStrideScan.ticks P S+2*S : ℕ) : ℝ)-(9*P : ℕ)| ≤ 6*(S : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have h0 := loading_curve_error P t
  have h1 := clippedRamp_sample_error P (3*P) 1 t
  have h2a : |(MaskedStrideScan.bankPosition P S (⌊t⌋₊-4*P) : ℝ)-
      ((min ((⌊t⌋₊-4*P)/4) P : ℕ) : ℝ)| ≤ S := by
    exact_mod_cast MaskedStrideScan.bankPosition_error P hS (⌊t⌋₊-4*P)
  have h2b := clippedRamp_sample_error P (4*P) 4 t
  have h3a := clippedRamp_sample_error P (4*P+MaskedStrideScan.ticks P S+2*S) 1 t
  have h3b := clippedRamp_start_error P (4*P+MaskedStrideScan.ticks P S+2*S : ℕ)
    (8*P : ℕ) 1 t (by norm_num)
  simp only [div_one] at h3b
  have h3c := h3b.trans hR
  have h4a := clippedRamp_sample_error P (5*P+MaskedStrideScan.ticks P S+2*S) 3 t
  have h4b := clippedRamp_start_error P (5*P+MaskedStrideScan.ticks P S+2*S : ℕ)
    (9*P : ℕ) 3 t (by norm_num)
  have h4c : |clippedRamp P (5*P+MaskedStrideScan.ticks P S+2*S : ℕ) 3 t-
      clippedRamp P (9*P : ℕ) 3 t| ≤ 2*(S : ℝ) :=
    h4b.trans ((div_le_iff₀ (show (0 : ℝ)<3 by norm_num)).mpr (by linarith))
  simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat] at h1 h2b h3a h4a
  simp only [bankPath,cappedRamp,MaskedStrideScan.rise,Int.cast_add,Int.cast_sub,Int.cast_natCast,
    smallBankApproximation]
  rw [abs_le] at h0 h1 h2a h2b h3a h3c h4a h4c ⊢
  constructor <;> linarith

theorem scratchPath_bound (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    |scratchPath P S n| ≤ 2*(S : ℤ) := by
  have h := MaskedStrideScan.scratchPosition_bounds P hS
    (min (n-4*P) (MaskedStrideScan.ticks P S)) (Nat.min_le_right _ _)
  have h1 := Nat.min_le_right (n-(4*P+MaskedStrideScan.ticks P S)) S
  have h2 := Nat.min_le_right (n-(4*P+MaskedStrideScan.ticks P S+S)) S
  rw [scratchPath,abs_le]
  unfold cappedRamp
  constructor <;> omega

theorem full_small_affine_approximation {P S : ℕ} (hP : 0<P) (hS : 0<S)
    {H : ℝ} (hH : 0 ≤ H) (isPrefix : Bool) (mask : ℕ → Bool) (w : List Bool) :
    HasAffineIntervalCover 243 (fun t => smallBankApproximation P ((P : ℝ)*t)/P) H ∧
    HasAffineIntervalCover 243 (fun _ => (0 : ℝ)) H ∧
    ∀ t : ℝ,
      |(Transpose.Tape.workTraj (machine isPrefix mask P S) w ⌊(P : ℝ)*t⌋₊ ((encoding P S).port 0) : ℝ)/P-
        smallBankApproximation P ((P : ℝ)*t)/P| ≤ (9*(S : ℝ)+6)/P ∧
      |(Transpose.Tape.workTraj (machine isPrefix mask P S) w ⌊(P : ℝ)*t⌋₊ ((encoding P S).port 1) : ℝ)/P-0| ≤
        (9*(S : ℝ)+6)/P := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  refine ⟨(smallBankApproximation_cover P (mul_nonneg hp.le hH)).rescale hp,
    (HasAffineIntervalCover.const hH 0).mono (by decide) (by decide),fun t => ?_⟩
  have hb := workTraj_position isPrefix mask P hS w ⌊(P : ℝ)*t⌋₊ 0
  have hs := workTraj_position isPrefix mask P hS w ⌊(P : ℝ)*t⌋₊ 1
  simp only [ite_true] at hb
  simp only [show (1 : Fin 2) ≠ 0 by decide,ite_false] at hs
  have he0 := smallBankApproximation_error P hS ((P : ℝ)*t)
  have he1 : |(scratchPath P S ⌊(P : ℝ)*t⌋₊ : ℝ)| ≤ 2*(S : ℝ) := by
    exact_mod_cast scratchPath_bound P hS ⌊(P : ℝ)*t⌋₊
  have hb' := congrArg (fun z : ℤ => |(z : ℝ)/P-smallBankApproximation P ((P : ℝ)*t)/P|) hb
  have hs' := congrArg (fun z : ℤ => |(z : ℝ)/P-0|) hs
  refine ⟨hb'.trans_le ?_,hs'.trans_le ?_⟩
  · rw [← sub_div,abs_div,abs_of_pos hp]
    exact div_le_div_of_nonneg_right he0 hp.le
  · rw [sub_zero,abs_div,abs_of_pos hp]
    exact div_le_div_of_nonneg_right (he1.trans (by nlinarith [(Nat.cast_nonneg S : (0 : ℝ) ≤ S)])) hp.le

end TransposeFollowup.RawMaskedStride
