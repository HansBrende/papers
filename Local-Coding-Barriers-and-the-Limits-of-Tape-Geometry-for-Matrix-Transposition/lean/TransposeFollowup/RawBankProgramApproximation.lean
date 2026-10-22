import TransposeFollowup.RawBankProgramMotion
import TransposeFollowup.RawMaskedStrideCurves

/-! The shared raw wrapper adds three clipped ramps, with at most four
cells of error. This reuses the existing loading and rounding estimates. -/
namespace TransposeFollowup.RawBankProgram
open Classical AffineMotion
set_option autoImplicit false

noncomputable def ioCurve (P C : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  if h=0 then clippedRamp P 0 3 t-clippedRamp P (3*P : ℕ) 1 t+
    clippedRamp P (4*P+C : ℕ) 3 t else 0

theorem ioCurve_cover (P C : ℕ) {H : ℝ} (hH : 0 ≤ H) (h : Fin 2) :
    HasAffineIntervalCover 27 (ioCurve P C h) H := by
  change HasAffineIntervalCover 27 (fun t => ioCurve P C h t) H
  by_cases hh : h=0
  · simp only [ioCurve,ite_eq_left hh]
    exact ((clippedRamp_cover hH (by positivity) (le_refl (0 : ℝ)) (show (0 : ℝ)<3 by norm_num)).sub
      (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))).add
      (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num))
  · simp only [ioCurve,ite_eq_right hh]
    exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)

def ioPath (P C : ℕ) (h : Fin 2) (n : ℕ) : ℤ :=
  if h=0 then ((min ((n+1)/3) P : ℕ) : ℤ)-(min (n-3*P) P : ℕ)+
    (min ((n-(4*P+C))/3) P : ℕ) else 0

theorem ioPath_curve_error (P C : ℕ) (h : Fin 2) (t : ℝ) :
    |(ioPath P C h ⌊t⌋₊ : ℝ)-ioCurve P C h t| ≤ 4 := by
  have ha := RawMaskedStride.loading_curve_error P t
  have hb := clippedRamp_sample_error P (3*P) 1 t
  have hc := clippedRamp_sample_error P (4*P+C) 3 t
  simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat] at hb hc
  rw [abs_le] at ha hb hc
  by_cases hh : h=0
  · simp only [ioPath,ioCurve,ite_eq_left hh,Int.cast_add,Int.cast_sub,Int.cast_natCast]
    rw [abs_le]
    constructor <;> linarith
  · simp [ioPath,ioCurve,hh]

theorem ioCurve_error (P : ℕ) (B : Body) (M : Motion B) (h : Fin 2) (t : ℝ) :
    |(path P B M h ⌊t⌋₊ : ℝ)-(M.path h (⌊t⌋₊-4*P) : ℝ)-ioCurve P B.cost h t| ≤ 4 := by
  have he : (path P B M h ⌊t⌋₊ : ℝ)-(M.path h (⌊t⌋₊-4*P) : ℝ)=
      (ioPath P B.cost h ⌊t⌋₊ : ℝ) := by
    change ((M.path h (⌊t⌋₊-4*P)+ioPath P B.cost h ⌊t⌋₊ : ℤ) : ℝ)-_= _
    push_cast
    ring
  rw [he]
  exact ioPath_curve_error P B.cost h t

end TransposeFollowup.RawBankProgram
