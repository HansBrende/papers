import TransposeFollowup.RawMaskedStridePaths
import TransposeFollowup.RawMaskedStrideAffineApproximation

/-! Finite-affine approximants for the WHOLE raw execution, including its
halted tail. The processing approximation is reused with its paid offset;
the other five nonstationary phases are ordinary clipped ramps. -/
namespace TransposeFollowup.RawMaskedStride
open Classical Set Filter Topology Finset AffineMotion
set_option autoImplicit false

theorem clippedRamp_shift (L a b d t : ℝ) :
    clippedRamp L a d (t-b)=clippedRamp L (a+b) d t := by
  have he : t-b-a=t-(a+b) := by ring
  simp only [clippedRamp,he]

theorem processing_curve_shift_covers (P S A : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    HasAffineIntervalCover (3^(P/S+1)) (fun t => MaskedStrideScan.bankCurve P S (t-A)) H ∧
    HasAffineIntervalCover (9^(P/S+1)) (fun t => MaskedStrideScan.scratchCurve P S (t-A)) H := by
  constructor
  · have hc : HasAffineIntervalCover (3^(P/S)*3)
        (fun t => (∑ r ∈ range (P/S), clippedRamp S ((r*(4*S) : ℕ)+(A : ℝ)) 3 t)+
          clippedRamp (P%S : ℕ) ((P/S*(4*S) : ℕ)+(A : ℝ)) 3 t) H :=
      (HasAffineIntervalCover.sum_range hH _ (fun _ _ =>
        clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num))).add
          (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num))
    convert hc using 1
    · rw [pow_succ]
    · funext t
      simp only [MaskedStrideScan.bankCurve,clippedRamp_shift]
  · have hc : HasAffineIntervalCover (9^(P/S+1))
        (fun t => ∑ r ∈ range (P/S+1),
          (clippedRamp S ((r*(4*S) : ℕ)+(A : ℝ)) 3 t-
            clippedRamp S ((r*(4*S)+3*S : ℕ)+(A : ℝ)) 1 t)) H :=
      HasAffineIntervalCover.sum_range hH _ (fun _ _ =>
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num)).sub
          (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num)))
    convert hc using 1
    funext t
    simp only [MaskedStrideScan.scratchCurve,clippedRamp_shift]

noncomputable def bankApproximation (P S : ℕ) (t : ℝ) : ℝ :=
  clippedRamp P 0 3 t-clippedRamp P (3*P : ℕ) 1 t+
    MaskedStrideScan.bankCurve P S (t-(4*P : ℕ))-
    clippedRamp P (4*P+MaskedStrideScan.ticks P S+2*S : ℕ) 1 t+
    clippedRamp P (5*P+MaskedStrideScan.ticks P S+2*S : ℕ) 3 t

noncomputable def scratchApproximation (P S : ℕ) (t : ℝ) : ℝ :=
  MaskedStrideScan.scratchCurve P S (t-(4*P : ℕ))+
    clippedRamp S (4*P+MaskedStrideScan.ticks P S : ℕ) 1 t-
    clippedRamp S (4*P+MaskedStrideScan.ticks P S+S : ℕ) 1 t

theorem loading_curve_error (P : ℕ) (t : ℝ) :
    |((min ((⌊t⌋₊+1)/3) P : ℕ) : ℝ)-clippedRamp P 0 3 t| ≤ 2 := by
  have h0 := clippedRamp_sample_error P 0 3 t
  simp only [Nat.sub_zero,Nat.cast_zero,Nat.cast_ofNat] at h0
  have hl : ((min (⌊t⌋₊/3) P : ℕ) : ℝ) ≤ (min ((⌊t⌋₊+1)/3) P : ℕ) := by
    exact_mod_cast (show min (⌊t⌋₊/3) P ≤ min ((⌊t⌋₊+1)/3) P by omega)
  have hu : ((min ((⌊t⌋₊+1)/3) P : ℕ) : ℝ) ≤ (min (⌊t⌋₊/3) P : ℕ)+1 := by
    exact_mod_cast (show min ((⌊t⌋₊+1)/3) P ≤ min (⌊t⌋₊/3) P+1 by omega)
  rw [abs_le] at h0 ⊢
  constructor <;> linarith

theorem bankApproximation_error (P : ℕ) {S : ℕ} (hS : 0<S) (t : ℝ) :
    |(bankPath P S ⌊t⌋₊ : ℝ)-bankApproximation P S t| ≤ (P/S : ℕ)+6 := by
  have h0 := loading_curve_error P t
  have h1 := clippedRamp_sample_error P (3*P) 1 t
  have h2 := MaskedStrideScan.bankCurve_error P hS (t-(4*P : ℕ))
  rw [MaskedStrideScan.bankPosition_freeze P hS,Nat.floor_sub_natCast] at h2
  have h3 := clippedRamp_sample_error P (4*P+MaskedStrideScan.ticks P S+2*S) 1 t
  have h4 := clippedRamp_sample_error P (5*P+MaskedStrideScan.ticks P S+2*S) 3 t
  simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat] at h1 h3 h4
  simp only [bankPath,cappedRamp,MaskedStrideScan.rise,Int.cast_add,Int.cast_sub,Int.cast_natCast,
    bankApproximation]
  rw [abs_le] at h0 h1 h2 h3 h4 ⊢
  constructor <;> linarith

theorem scratchApproximation_error (P : ℕ) {S : ℕ} (hS : 0<S) (t : ℝ) :
    |(scratchPath P S ⌊t⌋₊ : ℝ)-scratchApproximation P S t| ≤ 2*((P/S : ℕ)+2) := by
  have h0 := MaskedStrideScan.scratchCurve_error P hS (t-(4*P : ℕ))
  rw [Nat.floor_sub_natCast] at h0
  have h1 := clippedRamp_sample_error S (4*P+MaskedStrideScan.ticks P S) 1 t
  have h2 := clippedRamp_sample_error S (4*P+MaskedStrideScan.ticks P S+S) 1 t
  simp only [Nat.div_one,Nat.cast_one] at h1 h2
  simp only [scratchPath,cappedRamp,Int.cast_add,Int.cast_sub,Int.cast_natCast,scratchApproximation]
  rw [abs_le] at h0 h1 h2 ⊢
  constructor <;> linarith

theorem full_curve_covers (P S : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    HasAffineIntervalCover (81*3^(P/S+1)) (bankApproximation P S) H ∧
    HasAffineIntervalCover (9*9^(P/S+1)) (scratchApproximation P S) H := by
  have hp := processing_curve_shift_covers P S (4*P) hH
  constructor
  · have hc : HasAffineIntervalCover (((3*3)*3^(P/S+1))*3*3) (bankApproximation P S) H :=
      ((((clippedRamp_cover hH (by positivity) (le_refl (0 : ℝ)) (show (0 : ℝ)<3 by norm_num)).sub
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).add hp.1).sub
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).add
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num))
    convert hc using 1; ring
  · have hc : HasAffineIntervalCover ((9^(P/S+1)*3)*3) (scratchApproximation P S) H :=
      (hp.2.add (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).sub
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))
    convert hc using 1; ring

theorem full_bounded_affine_approximation {P S B : ℕ}
    (hP : 0<P) (hS : 0<S) (hB : P/S ≤ B) {H : ℝ} (hH : 0 ≤ H)
    (isPrefix : Bool) (mask : ℕ → Bool) (w : List Bool) :
    HasAffineIntervalCover (81*9^(B+1)) (fun t => bankApproximation P S ((P : ℝ)*t)/P) H ∧
    HasAffineIntervalCover (81*9^(B+1)) (fun t => scratchApproximation P S ((P : ℝ)*t)/P) H ∧
    ∀ t : ℝ,
      |(Transpose.Tape.workTraj (machine isPrefix mask P S) w ⌊(P : ℝ)*t⌋₊ ((encoding P S).port 0) : ℝ)/P-
        bankApproximation P S ((P : ℝ)*t)/P| ≤ 2*((B : ℝ)+3)/P ∧
      |(Transpose.Tape.workTraj (machine isPrefix mask P S) w ⌊(P : ℝ)*t⌋₊ ((encoding P S).port 1) : ℝ)/P-
        scratchApproximation P S ((P : ℝ)*t)/P| ≤ 2*((B : ℝ)+3)/P := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  have hc := full_curve_covers P S (mul_nonneg hp.le hH)
  have hpow : 9^(P/S+1) ≤ 9^(B+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbank : 81*3^(P/S+1) ≤ 81*9^(B+1) :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by decide : 3 ≤ 9) _).trans hpow)
  have hscratch : 9*9^(P/S+1) ≤ 81*9^(B+1) := Nat.mul_le_mul (by decide) hpow
  refine ⟨(hc.1.mono (by positivity) hbank).rescale hp,
    (hc.2.mono (by positivity) hscratch).rescale hp,fun t => ?_⟩
  have hb := workTraj_position isPrefix mask P hS w ⌊(P : ℝ)*t⌋₊ 0
  have hs := workTraj_position isPrefix mask P hS w ⌊(P : ℝ)*t⌋₊ 1
  simp only [ite_true] at hb
  simp only [show (1 : Fin 2) ≠ 0 by decide,ite_false] at hs
  have hqb : ((P/S : ℕ) : ℝ) ≤ B := by exact_mod_cast hB
  have he0 := bankApproximation_error P hS ((P : ℝ)*t)
  have he1 := scratchApproximation_error P hS ((P : ℝ)*t)
  have hb' := congrArg (fun z : ℤ => |(z : ℝ)/P-bankApproximation P S ((P : ℝ)*t)/P|) hb
  have hs' := congrArg (fun z : ℤ => |(z : ℝ)/P-scratchApproximation P S ((P : ℝ)*t)/P|) hs
  refine ⟨hb'.trans_le ?_,hs'.trans_le ?_⟩ <;> rw [← sub_div,abs_div,abs_of_pos hp]
  · exact div_le_div_of_nonneg_right (he0.trans (by linarith)) hp.le
  · exact div_le_div_of_nonneg_right (he1.trans (by linarith)) hp.le

end TransposeFollowup.RawMaskedStride
