import TransposeFollowup.BankRotationMotion
import TransposeFollowup.BankReversalApproximation

/-! Rotation inherits three reversal comparisons and two seek ramps.
Cover size and error are uniform in the public rotation offset. -/
namespace TransposeFollowup.BankRotation
open Classical AffineMotion
set_option autoImplicit false

noncomputable def approximation (P R A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  BankReversal.approximation P A h t+
    BankReversal.approximation (P-R) (A+BankReversal.ticks P) h t+
    BankReversal.approximation R (A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)) h t+
    if h=0 then clippedRamp (P-R : ℕ) (A+BankReversal.ticks P+BankReversal.ticks (P-R) : ℕ) 1 t-
      clippedRamp (P-R : ℕ)
        (A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)+BankReversal.ticks R : ℕ) 1 t
    else 0

theorem approximation_cover (P R A : ℕ) {H : ℝ} (hH : 0≤H) (h : Fin 2) :
    HasAffineIntervalCover (81*81*81*9) (approximation P R A h) H := by
  have hs : HasAffineIntervalCover 9 (fun t =>
      if h=0 then clippedRamp (P-R : ℕ) (A+BankReversal.ticks P+BankReversal.ticks (P-R) : ℕ) 1 t-
        clippedRamp (P-R : ℕ)
          (A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)+BankReversal.ticks R : ℕ) 1 t
      else 0) H := by
    by_cases hh : h=0
    · simp only [ite_eq_left hh]
      exact (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num)).sub
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))
    · simp only [ite_eq_right hh]
      exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)
  exact (((BankReversal.approximation_cover P A hH h).add
    (BankReversal.approximation_cover (P-R) (A+BankReversal.ticks P) hH h)).add
    (BankReversal.approximation_cover R (A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)) hH h)).add hs

theorem approximation_error (P R A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P R h (⌊t⌋₊-A) : ℝ)-approximation P R A h t|≤14 := by
  have ha := BankReversal.approximation_error P A h t
  have hb := BankReversal.approximation_error (P-R) (A+BankReversal.ticks P) h t
  have hc := BankReversal.approximation_error R (A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)) h t
  have hd := clippedRamp_sample_error (P-R) (A+BankReversal.ticks P+BankReversal.ticks (P-R)) 1 t
  have he := clippedRamp_sample_error (P-R)
    (A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)+BankReversal.ticks R) 1 t
  have h1 : ⌊t⌋₊-A-BankReversal.ticks P=⌊t⌋₊-(A+BankReversal.ticks P) := by omega
  have h2 : ⌊t⌋₊-A-BankReversal.ticks P-BankReversal.ticks (P-R)=
      ⌊t⌋₊-(A+BankReversal.ticks P+BankReversal.ticks (P-R)) := by omega
  have h3 : ⌊t⌋₊-A-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R)=
      ⌊t⌋₊-(A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)) := by omega
  have h4 : ⌊t⌋₊-A-BankReversal.ticks P-BankReversal.ticks (P-R)-(P-R)-BankReversal.ticks R=
      ⌊t⌋₊-(A+BankReversal.ticks P+BankReversal.ticks (P-R)+(P-R)+BankReversal.ticks R) := by omega
  simp only [Nat.div_one,Nat.cast_one] at hd he
  rw [abs_le] at ha hb hc hd he
  by_cases hh : h=0
  · simp only [path,approximation,ite_eq_left hh,Int.cast_add,Int.cast_sub,Int.cast_natCast]
    rw [h4,h3,h2,h1,abs_le]
    constructor <;> linarith
  · simp only [path,approximation,ite_eq_right hh,Int.cast_add,add_zero]
    rw [h3,h1,abs_le]
    constructor <;> linarith

end TransposeFollowup.BankRotation
