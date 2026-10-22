import TransposeFollowup.MaskedStrideWordMotion
import TransposeFollowup.RawMaskedStrideSmallCurve

/-! Affine approximants for internal stages at arbitrary paid start times.
All processing/rounding estimates are reused. Small strides use two ramps;
bounded group counts use the existing shifted processing curves. -/
namespace TransposeFollowup.MaskedStrideBankStage
open Classical AffineMotion
set_option autoImplicit false

noncomputable def approximation (P S A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  if h=0 then MaskedStrideScan.bankCurve P S (t-A)-
    clippedRamp P (A+MaskedStrideScan.ticks P S+2*S : ℕ) 1 t
  else MaskedStrideScan.scratchCurve P S (t-A)+
    clippedRamp S (A+MaskedStrideScan.ticks P S : ℕ) 1 t-
    clippedRamp S (A+MaskedStrideScan.ticks P S+S : ℕ) 1 t

theorem approximation_error (P : ℕ) {S : ℕ} (hS : 0 < S) (A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P S h (⌊t⌋₊-A) : ℝ)-approximation P S A h t| ≤ 2*((P/S : ℕ)+2) := by
  have hb := MaskedStrideScan.bankCurve_error P hS (t-A)
  have hs := MaskedStrideScan.scratchCurve_error P hS (t-A)
  rw [Nat.floor_sub_natCast] at hb hs
  have hr := clippedRamp_sample_error P (A+MaskedStrideScan.ticks P S+2*S) 1 t
  have he := clippedRamp_sample_error S (A+MaskedStrideScan.ticks P S) 1 t
  have hw := clippedRamp_sample_error S (A+MaskedStrideScan.ticks P S+S) 1 t
  have h0 : ⌊t⌋₊-A-MaskedStrideScan.ticks P S-S-S = ⌊t⌋₊-(A+MaskedStrideScan.ticks P S+2*S) := by omega
  have h1 : ⌊t⌋₊-A-MaskedStrideScan.ticks P S = ⌊t⌋₊-(A+MaskedStrideScan.ticks P S) := by omega
  have h2 : ⌊t⌋₊-A-MaskedStrideScan.ticks P S-S = ⌊t⌋₊-(A+MaskedStrideScan.ticks P S+S) := by omega
  simp only [Nat.div_one,Nat.cast_one] at hr he hw
  rw [abs_le] at hb hs hr he hw
  by_cases hh : h=0
  · simp only [path,approximation,ite_eq_left hh,Int.cast_sub,Int.cast_natCast]
    rw [h0,abs_le]
    constructor <;> linarith [Nat.cast_nonneg (P/S) (α:=ℝ)]
  · simp only [path,approximation,ite_eq_right hh,Int.cast_sub,Int.cast_add,Int.cast_natCast]
    rw [h2,h1,abs_le]
    constructor <;> linarith

theorem approximation_cover (P S A B : ℕ) (hB : P/S ≤ B) {H : ℝ} (hH : 0 ≤ H) (h : Fin 2) :
    HasAffineIntervalCover (9^(B+1)*9) (approximation P S A h) H := by
  have hc := RawMaskedStride.processing_curve_shift_covers P S A hH
  have hq : 9^(P/S+1) ≤ 9^(B+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hb : 3^(P/S+1) ≤ 9^(B+1) := (Nat.pow_le_pow_left (by decide : 3 ≤ 9) _).trans hq
  fin_cases h
  · exact (hc.1.sub (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).mono
      (by positivity) (Nat.mul_le_mul hb (by decide : 3 ≤ 9))
  · exact ((hc.2.add (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).sub
      (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).mono
      (by positivity) (by simpa only [Nat.mul_assoc,show 3*3=9 from rfl] using Nat.mul_le_mul_right 9 hq)

noncomputable def smallApproximation (P A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  if h=0 then clippedRamp P A 4 t-clippedRamp P (A+4*P : ℕ) 1 t else 0

theorem smallApproximation_cover (P A : ℕ) {H : ℝ} (hH : 0 ≤ H) (h : Fin 2) :
    HasAffineIntervalCover 9 (smallApproximation P A h) H := by
  fin_cases h
  · exact (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<4 by norm_num)).sub
      (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))
  · exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)

theorem smallApproximation_error (P : ℕ) {S : ℕ} (hS : 0 < S) (A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P S h (⌊t⌋₊-A) : ℝ)-smallApproximation P A h t| ≤ 7*(S : ℝ)+2 := by
  by_cases hh : h=0
  · have hn := MaskedStrideScan.ticks_bounds P hS
    have hn0 : 4*(P : ℝ) ≤ MaskedStrideScan.ticks P S := by exact_mod_cast hn.1
    have hn1 : (MaskedStrideScan.ticks P S : ℝ) ≤ 4*(P : ℝ)+4*S := by exact_mod_cast hn.2
    have hR : |((A+MaskedStrideScan.ticks P S+2*S : ℕ) : ℝ)-(A+4*P : ℕ)| ≤ 6*(S : ℝ) := by
      push_cast
      rw [abs_le]
      constructor <;> linarith
    have hb : |(MaskedStrideScan.bankPosition P S (⌊t⌋₊-A) : ℝ)-
        ((min ((⌊t⌋₊-A)/4) P : ℕ) : ℝ)| ≤ S := by
      exact_mod_cast MaskedStrideScan.bankPosition_error P hS (⌊t⌋₊-A)
    have hs := clippedRamp_sample_error P A 4 t
    have hr := clippedRamp_sample_error P (A+MaskedStrideScan.ticks P S+2*S) 1 t
    have hd := RawMaskedStride.clippedRamp_start_error P (A+MaskedStrideScan.ticks P S+2*S : ℕ)
      (A+4*P : ℕ) 1 t (by norm_num)
    simp only [div_one] at hd
    have he := hd.trans hR
    have h0 : ⌊t⌋₊-A-MaskedStrideScan.ticks P S-S-S = ⌊t⌋₊-(A+MaskedStrideScan.ticks P S+2*S) := by omega
    simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat] at hs hr
    simp only [path,smallApproximation,ite_eq_left hh,Int.cast_sub,Int.cast_natCast,
      MaskedStrideScan.bankPosition_freeze P hS,h0]
    rw [abs_le] at hb hs hr he ⊢
    constructor <;> linarith
  · have hs := MaskedStrideScan.scratchPosition_bounds P hS
      (min (⌊t⌋₊-A) (MaskedStrideScan.ticks P S)) (Nat.min_le_right _ _)
    have h1 := Nat.min_le_right (⌊t⌋₊-A-MaskedStrideScan.ticks P S) S
    have h2 := Nat.min_le_right (⌊t⌋₊-A-MaskedStrideScan.ticks P S-S) S
    have hb : |path P S h (⌊t⌋₊-A)| ≤ 2*(S : ℤ) := by
      simp only [path,ite_eq_right hh]
      rw [abs_le]
      constructor <;> omega
    have hbR : |(path P S h (⌊t⌋₊-A) : ℝ)| ≤ 2*(S : ℝ) := by exact_mod_cast hb
    simpa only [smallApproximation,ite_eq_right hh,sub_zero] using
      hbR.trans (show 2*(S : ℝ) ≤ 7*(S : ℝ)+2 by nlinarith [Nat.cast_nonneg S (α:=ℝ)])

end TransposeFollowup.MaskedStrideBankStage
