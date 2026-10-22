import TransposeFollowup.ScheduledWord
import TransposeFollowup.ScheduledHeadDisplacement

/-! Repeated paid blocks with a fixed endpoint displacement approximate
a straight scan. Intermediate motion is bounded by the existing native
unit-step theorem; no data-independent path inside a block is assumed. -/
namespace TransposeFollowup.ScheduledNativeIO
open FixedTapeCompiler
set_option autoImplicit false
variable {T M : Type*}

def repeatSchedule (σ : ℕ → NativeIO.Program T M) (idle : NativeIO.Program T M)
    (N r : ℕ) : ℕ → NativeIO.Program T M :=
  ScheduledWord.schedule (fun _ : Unit => N) (fun _ => σ) idle (List.replicate r ())

theorem repeat_exact (σ : ℕ → NativeIO.Program T M) (idle : NativeIO.Program T M)
    (N r : ℕ) (w : List Bool) (c : NativeIO.Config T M) :
    trajectory (repeatSchedule σ idle N r) w c (r*N)=
      (fun d => trajectory σ w d N)^[r] c := by
  have h := ScheduledWord.schedule_exact (fun _ : Unit => N) (fun _ => σ) idle
    (fun _ d => trajectory σ w d N) (List.replicate r ()) w c (fun _ _ _ => rfl)
  simpa [repeatSchedule,ScheduledWord.ticks,ScheduledWord.transform,List.foldl_const] using h

theorem repeat_endpoint (σ : ℕ → NativeIO.Program T M) (idle : NativeIO.Program T M)
    (N : ℕ) (w : List Bool) (t : T) (D : ℤ)
    (hend : ∀ c, (trajectory σ w c N).work.pos t=c.work.pos t+D)
    (r : ℕ) (c : NativeIO.Config T M) :
    (trajectory (repeatSchedule σ idle N r) w c (r*N)).work.pos t=c.work.pos t+r*D := by
  induction r generalizing c with
  | zero => simp [trajectory]
  | succ r ih =>
    change (trajectory (append σ (repeatSchedule σ idle N r) N) w c ((r+1)*N)).work.pos t=_
    rw [show (r+1)*N=N+r*N by ring,append_exact,ih,hend]
    push_cast
    ring

theorem word_block_error {O : Type*} (code : O → ℕ → NativeIO.Program T M) (idle : NativeIO.Program T M)
    (N : ℕ) (hN : 0<N) (w : List Bool) (t : T) (D : ℤ)
    (hend : ∀ op c, (trajectory (code op) w c N).work.pos t=c.work.pos t+D)
    (ops : List O) (c : NativeIO.Config T M) (n : ℕ) (hn : n≤ops.length*N) :
    |(trajectory (ScheduledWord.schedule (fun _ => N) code idle ops) w c n).work.pos t-c.work.pos t-
      (n/N : ℕ)*D|≤N := by
  induction ops generalizing c n with
  | nil =>
    simp only [List.length_nil,zero_mul] at hn
    have hz : n=0 := by omega
    simp [hz,trajectory]
  | cons op ops ih =>
    change |(trajectory (append (code op) (ScheduledWord.schedule (fun _ => N) code idle ops) N) w c n).work.pos t-
      c.work.pos t-(n/N : ℕ)*D|≤N
    by_cases h : n<N
    · rw [append_prefix _ _ _ _ _ _ h.le,Nat.div_eq_of_lt h]
      simpa using (trajectory_displacement (code op) w c n t).trans (by exact_mod_cast h.le)
    · have hm : n-N≤ops.length*N := by simp only [List.length_cons,Nat.succ_mul] at hn; omega
      have ht : trajectory (append (code op) (ScheduledWord.schedule (fun _ => N) code idle ops) N) w c n=
          trajectory (ScheduledWord.schedule (fun _ => N) code idle ops) w (trajectory (code op) w c N) (n-N) := by
        conv_lhs => rw [show n=N+(n-N) by omega]
        exact append_exact _ _ _ _ _ _
      have hq : n/N=(n-N)/N+1 := by
        conv_lhs => rw [show n=N+(n-N) by omega]
        exact Nat.add_div_left _ hN
      calc
        _ = |(trajectory (ScheduledWord.schedule (fun _ => N) code idle ops) w (trajectory (code op) w c N) (n-N)).work.pos t-
            (trajectory (code op) w c N).work.pos t-((n-N)/N : ℕ)*D| := by
          rw [ht,hend op c,hq]
          congr 1
          push_cast
          ring
        _ ≤ N := ih _ _ hm

theorem repeat_block_error (σ : ℕ → NativeIO.Program T M) (idle : NativeIO.Program T M)
    (N : ℕ) (hN : 0<N) (w : List Bool) (t : T) (D : ℤ)
    (hend : ∀ c, (trajectory σ w c N).work.pos t=c.work.pos t+D)
    (r : ℕ) (c : NativeIO.Config T M) (n : ℕ) (hn : n≤r*N) :
    |(trajectory (repeatSchedule σ idle N r) w c n).work.pos t-c.work.pos t-
      (n/N : ℕ)*D|≤N := by
  simpa only [repeatSchedule,List.length_replicate] using
    word_block_error (fun _ : Unit => σ) idle N hN w t D (fun _ => hend)
      (List.replicate r ()) c n (by simpa only [List.length_replicate] using hn)

theorem repeat_linear_error (σ : ℕ → NativeIO.Program T M) (idle : NativeIO.Program T M)
    (N : ℕ) (hN : 0<N) (w : List Bool) (t : T) (D : ℤ)
    (hend : ∀ c, (trajectory σ w c N).work.pos t=c.work.pos t+D)
    (r : ℕ) (c : NativeIO.Config T M) (n : ℕ) (hn : n≤r*N) :
    |((trajectory (repeatSchedule σ idle N r) w c n).work.pos t : ℝ)-
      c.work.pos t-(n : ℝ)/N*D|≤N+|(D : ℝ)| := by
  have hb : |((trajectory (repeatSchedule σ idle N r) w c n).work.pos t : ℝ)-
      c.work.pos t-(n/N : ℕ)*(D : ℝ)|≤N := by
    have hi : ((|(trajectory (repeatSchedule σ idle N r) w c n).work.pos t-
        c.work.pos t-(n/N : ℕ)*D| : ℤ) : ℝ)≤(N : ℝ) := by
      exact_mod_cast repeat_block_error σ idle N hN w t D hend r c n hn
    simpa only [Int.cast_abs,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using hi
  have hp : (0 : ℝ)<N := by exact_mod_cast hN
  have he : (n : ℝ)=(n/N : ℕ)*(N : ℝ)+(n%N : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' n N).symm
  have hm : ((n%N : ℕ) : ℝ)<N := by exact_mod_cast Nat.mod_lt n hN
  have hz : (0 : ℝ)≤(n%N : ℕ) := Nat.cast_nonneg _
  have hd := div_mul_cancel₀ (n : ℝ) hp.ne'
  have hq : |(n/N : ℕ)-(n : ℝ)/N|≤1 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hs : |(n/N : ℕ)*(D : ℝ)-(n : ℝ)/N*D|≤|(D : ℝ)| := by
    rw [← sub_mul,abs_mul]
    simpa using mul_le_mul_of_nonneg_right hq (abs_nonneg (D : ℝ))
  rw [abs_le] at hb hs ⊢
  constructor <;> linarith

end TransposeFollowup.ScheduledNativeIO
