import TransposeFollowup.RawCarryBankMotion
import TransposeFollowup.ClippedAffineRamps

/-! Four reused clipped ramps per head approximate the full carry bank
with error at most eight cells, independently of the word width. -/
namespace TransposeFollowup.RawCarryBank
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
open CoupledRowCell (State)
set_option autoImplicit false

noncomputable def approximation (P A : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  if t=0 then clippedRamp P (A+1 : ℕ) 1 x-clippedRamp P (A+1+P : ℕ) 4 x+
    clippedRamp P (A+1+5*P : ℕ) 1 x-clippedRamp P (A+RawRowArithmetic.ticks P+2*P : ℕ) 1 x
  else clippedRamp P (A+1 : ℕ) 1 x-clippedRamp P (A+1+P : ℕ) 4 x+
    clippedRamp P (A+RawRowArithmetic.ticks P : ℕ) 1 x-
      clippedRamp P (A+RawRowArithmetic.ticks P+P : ℕ) 1 x

theorem approximation_cover (P A : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 81 (approximation P A t) H := by
  have hc (a : ℕ) {d : ℝ} (hd : 0 < d) :=
    clippedRamp_cover hH (Nat.cast_nonneg P) (Nat.cast_nonneg a) hd
  change HasAffineIntervalCover 81 (fun x => approximation P A t x) H
  by_cases ht : t=0
  · simp only [approximation,ite_eq_left ht]
    exact (((hc (A+1) (by norm_num : (0 : ℝ)<1)).sub
      (hc (A+1+P) (by norm_num : (0 : ℝ)<4))).add
      (hc (A+1+5*P) (by norm_num : (0 : ℝ)<1))).sub
      (hc (A+RawRowArithmetic.ticks P+2*P) (by norm_num : (0 : ℝ)<1))
  · simp only [approximation,ite_eq_right ht]
    exact (((hc (A+1) (by norm_num : (0 : ℝ)<1)).sub
      (hc (A+1+P) (by norm_num : (0 : ℝ)<4))).add
      (hc (A+RawRowArithmetic.ticks P) (by norm_num : (0 : ℝ)<1))).sub
      (hc (A+RawRowArithmetic.ticks P+P) (by norm_num : (0 : ℝ)<1))

theorem path_approximation_error (P A : ℕ) (t : Fin 2) (x : ℝ) :
    |(path P t (⌊x⌋₊-A) : ℝ)-approximation P A t x| ≤ 4 := by
  have h0 := clippedRamp_sample_error P (A+1) 1 x
  have h1 := clippedRamp_sample_error P (A+1+P) 4 x
  have h2 := clippedRamp_sample_error P (A+1+5*P) 1 x
  have h3 := clippedRamp_sample_error P (A+RawRowArithmetic.ticks P+2*P) 1 x
  have h4 := clippedRamp_sample_error P (A+RawRowArithmetic.ticks P) 1 x
  have h5 := clippedRamp_sample_error P (A+RawRowArithmetic.ticks P+P) 1 x
  simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat,Nat.add_assoc] at h0 h1 h2 h3 h4 h5
  rw [abs_le] at h0 h1 h2 h3 h4 h5
  by_cases ht : t=0
  · simp only [path,rowPath,approximation,ite_eq_left ht,Int.cast_sub,Int.cast_add,
      Int.cast_neg,Int.cast_natCast,Nat.sub_sub,Nat.add_assoc]
    rw [abs_le]; constructor <;> linarith
  · simp only [path,rowPath,approximation,ite_eq_right ht,Int.cast_sub,Int.cast_add,
      Int.cast_natCast,add_zero,Nat.sub_sub,Nat.add_assoc]
    rw [abs_le]; constructor <;> linarith

theorem schedule_curve_error (sub carry : Bool) (P A : ℕ) (hP : 0 < P)
    (w : List Bool) (c : State) (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule sub carry P) w c (min (⌊x⌋₊-A) (ticks P))).work.pos t : ℝ)-
      c.work.pos t-approximation P A t x| ≤ 8 := by
  have hi : |((trajectory (schedule sub carry P) w c (min (⌊x⌋₊-A) (ticks P))).work.pos t : ℝ)-
      c.work.pos t-(path P t (⌊x⌋₊-A) : ℝ)| ≤ 4 := by
    exact_mod_cast schedule_path_error sub carry P hP w c (⌊x⌋₊-A) t
  have ha := path_approximation_error P A t x
  rw [abs_le] at hi ha ⊢
  constructor <;> linarith

end TransposeFollowup.RawCarryBank
