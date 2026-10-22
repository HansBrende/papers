import TransposeFollowup.BankSymbolRotationMotion
import TransposeFollowup.BankBlockReversalApproximation

/-! Reuse the three block-reversal curves and two seek ramps for exact
symbol rotation. The physical execution error is constant even for a
whole-bank rotation; stationary padding contributes no new motion. -/
namespace TransposeFollowup.BankSymbolRotation
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

noncomputable def approximation (P R A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  BankBlockReversal.approximation P A h t+
    BankBlockReversal.approximation (P-R) (A+(10*P)) h t+
    BankBlockReversal.approximation R (A+(10*P)+(10*(P-R))+(P-R)) h t+
    if h=0 then clippedRamp (P-R : ℕ) (A+(10*P)+(10*(P-R)) : ℕ) 1 t-
      clippedRamp (P-R : ℕ)
        (A+(10*P)+(10*(P-R))+(P-R)+(10*R) : ℕ) 1 t
    else 0

theorem approximation_cover (P R A : ℕ) {H : ℝ} (hH : 0≤H) (h : Fin 2) :
    HasAffineIntervalCover (81*81*81*9) (approximation P R A h) H := by
  have hs : HasAffineIntervalCover 9 (fun t =>
      if h=0 then clippedRamp (P-R : ℕ) (A+(10*P)+(10*(P-R)) : ℕ) 1 t-
        clippedRamp (P-R : ℕ)
          (A+(10*P)+(10*(P-R))+(P-R)+(10*R) : ℕ) 1 t
      else 0) H := by
    by_cases hh : h=0
    · simp only [ite_eq_left hh]
      exact (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num)).sub
        (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))
    · simp only [ite_eq_right hh]
      exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)
  exact (((BankBlockReversal.approximation_cover P A hH h).add
    (BankBlockReversal.approximation_cover (P-R) (A+(10*P)) hH h)).add
    (BankBlockReversal.approximation_cover R (A+(10*P)+(10*(P-R))+(P-R)) hH h)).add hs

theorem approximation_error (P R A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P R h (⌊t⌋₊-A) : ℝ)-approximation P R A h t|≤14 := by
  have ha := BankBlockReversal.path_approximation_error P A h t
  have hb := BankBlockReversal.path_approximation_error (P-R) (A+(10*P)) h t
  have hc := BankBlockReversal.path_approximation_error R (A+(10*P)+(10*(P-R))+(P-R)) h t
  have hd := clippedRamp_sample_error (P-R) (A+(10*P)+(10*(P-R))) 1 t
  have he := clippedRamp_sample_error (P-R)
    (A+(10*P)+(10*(P-R))+(P-R)+(10*R)) 1 t
  have h1 : ⌊t⌋₊-A-(10*P)=⌊t⌋₊-(A+(10*P)) := by omega
  have h2 : ⌊t⌋₊-A-(10*P)-(10*(P-R))=
      ⌊t⌋₊-(A+(10*P)+(10*(P-R))) := by omega
  have h3 : ⌊t⌋₊-A-(10*P)-(10*(P-R))-(P-R)=
      ⌊t⌋₊-(A+(10*P)+(10*(P-R))+(P-R)) := by omega
  have h4 : ⌊t⌋₊-A-(10*P)-(10*(P-R))-(P-R)-(10*R)=
      ⌊t⌋₊-(A+(10*P)+(10*(P-R))+(P-R)+(10*R)) := by omega
  simp only [Nat.div_one,Nat.cast_one] at hd he
  rw [abs_le] at ha hb hc hd he
  by_cases hh : h=0
  · simp only [path,approximation,ite_eq_left hh,Int.cast_add,Int.cast_sub,Int.cast_natCast]
    rw [h4,h3,h2,h1,abs_le]
    constructor <;> linarith
  · simp only [path,approximation,ite_eq_right hh,Int.cast_add,add_zero]
    rw [h3,h1,abs_le]
    constructor <;> linarith

theorem schedule_curve_error (P R A : ℕ) (w : List Bool) (c : SharedRowBank.State)
    (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule P R) w c (min (⌊x⌋₊-A) (ticks P R))).work.pos t : ℝ)-
      c.work.pos t-approximation P R A t x| ≤ 29 := by
  have h := schedule_path_error P R w c (min (⌊x⌋₊-A) (ticks P R)) (Nat.min_le_right _ _) t
  rw [path_frozen] at h
  have hr : |((trajectory (schedule P R) w c (min (⌊x⌋₊-A) (ticks P R))).work.pos t : ℝ)-
      c.work.pos t-(path P R t (⌊x⌋₊-A) : ℝ)| ≤ 15 := by
    have hh : ((|(trajectory (schedule P R) w c (min (⌊x⌋₊-A) (ticks P R))).work.pos t-
        c.work.pos t-path P R t (⌊x⌋₊-A)| : ℤ) : ℝ) ≤ 15 := by exact_mod_cast h
    simpa only [Int.cast_abs,Int.cast_sub] using hh
  have ha := approximation_error P R A t x
  rw [abs_le] at hr ha ⊢
  constructor <;> linarith

end TransposeFollowup.BankSymbolRotation
