import TransposeFollowup.RawCarryBank
import TransposeFollowup.CoupledRowMotion
import TransposeFollowup.RepeatedScheduleMotion
import TransposeFollowup.ScheduledMotionError
import TransposeFollowup.ScheduledCleanupMotion

/-! A whole-bank scan needs a constant error, not the coarse O(row width)
bound for many rows. Reuse the four-instruction cell endpoint and the
general repeated-block estimate, then append the existing paid passes. -/
namespace TransposeFollowup.RawCarryBank
open Classical FixedTapeCompiler ScheduledNativeIO
open CoupledRowCell (Mode State)
set_option autoImplicit false

theorem scan_error (f : Mode → Mode) (P : ℕ) (w : List Bool) (c : State)
    (n : ℕ) (hn : n ≤ 4*P) (t : Fin 2) :
    |(trajectory (CoupledRowScan.schedule f P) w c n).work.pos t-c.work.pos t+
      ((n/4 : ℕ) : ℤ)| ≤ 4 := by
  have h := repeat_block_error (CoupledRowCell.schedule f) CoupledRowScan.idle 4 (by norm_num)
    w t (-1) (fun d => by rw [CoupledRowCell.cell_exact]; rfl) P c n (by omega)
  simpa only [repeatSchedule,CoupledRowScan.schedule,mul_neg_one,sub_neg_eq_add,Nat.cast_ofNat] using h

def rowPath (P : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  (min (n-1) P : ℕ)-(min ((n-1-P)/4) P : ℕ)+
    if t=0 then ((min (n-1-5*P) P : ℕ) : ℤ) else 0

theorem row_error (sub carry : Bool) (P : ℕ) (w : List Bool) (c : State)
    (n : ℕ) (hn : n ≤ RawRowArithmetic.ticks P) (t : Fin 2) :
    |(trajectory (RawRowArithmetic.scheduleWithCarry sub carry P) w c n).work.pos t-
      c.work.pos t-rowPath P t n| ≤ 4 := by
  have hr (select : Fin 2 → Bool) (d : State) (m : ℕ) :=
    CoupledRowMotion.right_position select w d m t
  have hi (d : State) (m : ℕ) :
      (trajectory (fun _ => CoupledRowScan.idle) w d m).work.pos t=d.work.pos t+0 := by
    rw [CoupledRowScan.idle_exact,add_zero]
  have hfinish := append_position _ _ P (P-1) w t
    (fun m => if t=0 then (m : ℤ) else 0) (fun _ => 0)
    (fun d m _ => by simpa [RawRowArithmetic.bankOnly] using hr RawRowArithmetic.bankOnly d m)
    (fun d m _ => hi d m)
  have hscan := append_position_error (CoupledRowScan.schedule (RawRowArithmetic.update sub) P) _
    (4*P) (P+(P-1)) w t (fun m => -((m/4 : ℕ) : ℤ))
    (fun m => if t=0 then ((min m P : ℕ) : ℤ) else 0) 4 0 le_rfl (by simp)
    (fun d m hm => by simpa only [sub_neg_eq_add] using scan_error _ P w d m hm t)
    (fun d m hm => by rw [hfinish d m hm]; simp)
  let g (m : ℕ) : ℤ := -((min m (4*P)/4 : ℕ) : ℤ)+
    if t=0 then ((min (m-4*P) P : ℕ) : ℤ) else 0
  have hseek := append_position_error (fun _ => CoupledRowMoves.right (fun _ => true)) _
    P (4*P+(P+(P-1))) w t (fun m => (m : ℤ)) g 0 4 (by norm_num) (by simp [g])
    (fun d m _ => by rw [hr]; simp)
    (fun d m hm => by simpa only [g,add_zero] using hscan d m hm)
  let k (m : ℕ) : ℤ := (min m P : ℕ)+g (m-P)
  have hreset := append_position_error (fun _ => RawRowArithmetic.reset carry) _
    1 (P+(4*P+(P+(P-1)))) w t (fun _ => 0) k 0 4 (by norm_num) (by simp [k,g])
    (fun d m hm => by interval_cases m <;> simp [trajectory,RawRowArithmetic.reset,NativeIO.step,
      NativeIO.workProgram,NativeMicrocode.step,Microcode.actualStep])
    (fun d m hm => by simpa only [k,zero_add] using hseek d m hm)
  have h := hreset c n hn
  change |(trajectory (RawRowArithmetic.scheduleWithCarry sub carry P) w c n).work.pos t-
    c.work.pos t-(0+k (n-1))| ≤ 0+4 at h
  have he : min (n-1-P) (4*P)/4=min ((n-1-P)/4) P := by omega
  have hs : n-1-P-4*P=n-1-5*P := by omega
  simpa only [k,g,he,hs,zero_add,rowPath,sub_eq_add_neg,add_assoc] using h

def path (P : ℕ) (t : Fin 2) (n : ℕ) : ℤ :=
  rowPath P t n+if t=0 then -((min (n-RawRowArithmetic.ticks P-2*P) P : ℕ) : ℤ)
    else ((min (n-RawRowArithmetic.ticks P) P : ℕ) : ℤ)-
      (min (n-RawRowArithmetic.ticks P-P) P : ℕ)

theorem schedule_path_error (sub carry : Bool) (P : ℕ) (hP : 0 < P)
    (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) :
    |(trajectory (schedule sub carry P) w c (min n (ticks P))).work.pos t-c.work.pos t-
      path P t n| ≤ 4 := by
  let N := RawRowArithmetic.ticks P
  have hN : N=7*P := RawRowArithmetic.ticks_eq P hP
  have hs := append_position_error (RawRowArithmetic.scheduleWithCarry sub carry P)
    (ScheduledBankCleanup.schedule P P) N (ScheduledBankCleanup.ticks P P) w t
    (rowPath P t) (ScheduledBankCleanup.path P t) 4 0 le_rfl (by simp [ScheduledBankCleanup.path])
    (fun d m hm => row_error sub carry P w d m hm t)
    (fun d m hm => by rw [ScheduledBankCleanup.schedule_position P P w d m hm t]; simp)
  have h := hs c (min n (ticks P)) (Nat.min_le_right _ _)
  have ht : ticks P=10*P := ticks_eq P hP
  have h0 : min (min (min n (ticks P)) N-1) P=min (n-1) P := by rw [ht,hN]; omega
  have h1 : min ((min (min n (ticks P)) N-1-P)/4) P=min ((n-1-P)/4) P := by rw [ht,hN]; omega
  have h2 : min (min (min n (ticks P)) N-1-5*P) P=min (n-1-5*P) P := by rw [ht,hN]; omega
  have h3 : min (min n (ticks P)-N) P=min (n-N) P := by rw [ht,hN]; omega
  have h4 : min (min n (ticks P)-N-P) P=min (n-N-P) P := by rw [ht,hN]; omega
  have h5 : min n (ticks P)-N-2*P=min (n-N-2*P) P := by rw [ht,hN]; omega
  change |(trajectory (schedule sub carry P) w c (min n (ticks P))).work.pos t-c.work.pos t-
    (rowPath P t (min (min n (ticks P)) N)+ScheduledBankCleanup.path P t (min n (ticks P)-N))| ≤ 4+0 at h
  simp only [rowPath,ScheduledBankCleanup.path,h0,h1,h2,h3,h4,h5,add_zero] at h
  fin_cases t <;> simpa [path,rowPath,N] using h

end TransposeFollowup.RawCarryBank
