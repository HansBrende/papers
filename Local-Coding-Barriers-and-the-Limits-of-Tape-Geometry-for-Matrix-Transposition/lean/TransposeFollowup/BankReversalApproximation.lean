import TransposeFollowup.BankReversalMotion
import TransposeFollowup.ClippedAffineRamps

/-! Four clipped ramps approximate each reversal head at every time.
The error and cover count are independent of the bank size and of the
public start time. All rounding and cover closure are imported. -/
namespace TransposeFollowup.BankReversal
open Classical AffineMotion
set_option autoImplicit false

noncomputable def approximation (P A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  if h=0 then clippedRamp P A 2 t-clippedRamp P (A+2*P : ℕ) 1 t+
    clippedRamp P (A+3*P+1 : ℕ) 2 t-clippedRamp P (A+5*P+1 : ℕ) 1 t
  else clippedRamp P A 2 t-clippedRamp 1 (A+3*P : ℕ) 1 t-
    clippedRamp P (A+3*P+1 : ℕ) 2 t+clippedRamp 1 (A+6*P+1 : ℕ) 1 t

theorem approximation_cover (P A : ℕ) {H : ℝ} (hH : 0≤H) (h : Fin 2) :
    HasAffineIntervalCover 81 (approximation P A h) H := by
  have hc (L A : ℕ) {d : ℝ} (hd : 0<d) :=
    clippedRamp_cover hH (Nat.cast_nonneg L) (Nat.cast_nonneg A) hd
  change HasAffineIntervalCover 81 (fun t => approximation P A h t) H
  by_cases hh : h=0
  · simp only [approximation,ite_eq_left hh]
    exact (((hc P A (by norm_num : (0 : ℝ)<2)).sub (hc P (A+2*P) (by norm_num : (0 : ℝ)<1))).add
      (hc P (A+3*P+1) (by norm_num : (0 : ℝ)<2))).sub (hc P (A+5*P+1) (by norm_num : (0 : ℝ)<1))
  · simp only [approximation,ite_eq_right hh]
    simpa only [Nat.cast_one] using (((hc P A (by norm_num : (0 : ℝ)<2)).sub (hc 1 (A+3*P) (by norm_num : (0 : ℝ)<1))).sub
      (hc P (A+3*P+1) (by norm_num : (0 : ℝ)<2))).add (hc 1 (A+6*P+1) (by norm_num : (0 : ℝ)<1))

theorem approximation_error (P A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P h (⌊t⌋₊-A) : ℝ)-approximation P A h t|≤4 := by
  have e0 := clippedRamp_sample_error P A 2 t
  have e1 := clippedRamp_sample_error P (A+2*P) 1 t
  have e2 := clippedRamp_sample_error 1 (A+3*P) 1 t
  have e3 := clippedRamp_sample_error P (A+3*P+1) 2 t
  have e4 := clippedRamp_sample_error P (A+5*P+1) 1 t
  have e5 := clippedRamp_sample_error 1 (A+6*P+1) 1 t
  have hcap (m : ℕ) : min m (2*P)/2=min (m/2) P := by omega
  have h0 : ⌊t⌋₊-A-2*P=⌊t⌋₊-(A+2*P) := by omega
  have h1 : ⌊t⌋₊-A-2*P-P=⌊t⌋₊-(A+3*P) := by omega
  have h2 : ⌊t⌋₊-A-2*P-P-1=⌊t⌋₊-(A+3*P+1) := by omega
  have h3 : ⌊t⌋₊-A-2*P-P-1-2*P=⌊t⌋₊-(A+5*P+1) := by omega
  have h4 : ⌊t⌋₊-A-2*P-P-1-2*P-P=⌊t⌋₊-(A+6*P+1) := by omega
  simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat] at e0 e1 e2 e3 e4 e5
  rw [abs_le] at e0 e1 e2 e3 e4 e5
  by_cases hh : h=0
  · simp only [path,approximation,ite_eq_left hh,Int.cast_sub,Int.cast_add,Int.cast_natCast,hcap]
    rw [h3,h2,h0,abs_le]
    constructor <;> linarith
  · simp only [path,approximation,ite_eq_right hh,Int.cast_sub,Int.cast_add,Int.cast_natCast,hcap]
    rw [h4,h2,h1,abs_le]
    constructor <;> linarith

end TransposeFollowup.BankReversal
