import TransposeFollowup.ScheduledAdvance
import TransposeFollowup.ScheduledTransfer
import TransposeFollowup.RepeatedScheduleMotion

/-! Paid transfer of equal-width blocks in reverse order. Symbols within
each block retain their order. The codec is arbitrary; its left-inverse
law is needed only for the symbol specification, not execution or motion.
The source bank is unchanged and cells outside the scratch window are
preserved. This works for all five tape symbols, including trit encodings. -/
namespace TransposeFollowup.BlockReverseTransfer
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}
variable (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)

def blockRun (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  rewind 0 w (ScheduledTransfer.copied false false false read write reset (rewind 0 w c B) B) B

def blockSchedule (B : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  append (fun _ => action 0 ⟨none,.left⟩)
    (append (ScheduledTransfer.schedule false false false read write reset)
      (fun _ => action 0 ⟨none,.left⟩) (2*B)) B

theorem block_exact (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (blockSchedule read write reset B) w c (4*B)=blockRun read write reset B w c := by
  rw [show 4*B=B+(2*B+B) by omega]
  simp only [blockSchedule,append_exact,ScheduledTransfer.schedule_exact]
  rfl

theorem block_active (B i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (blockSchedule read write reset B i) c := by
  apply append_active
  · intro _; exact active _ _ _
  · intro _
    apply append_active
    · intro _; exact ScheduledTransfer.schedule_active _ _ _ _ _ _ _ _
    · intro _; exact active _ _ _

theorem block_positions (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (blockRun read write reset B w c).work.pos 0=c.work.pos 0-B ∧
    (blockRun read write reset B w c).work.pos 1=c.work.pos 1+B := by
  have h := ScheduledTransfer.copied_positions false false false read write reset (rewind 0 w c B) B
  simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,
    Bool.false_eq_true,ite_false] at h
  simp [blockRun,rewind_position,h.1,h.2]

theorem block_source (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ) :
    cells (blockRun read write reset B w c) 0 z=cells c 0 z := by
  rw [blockRun,rewind_cells]
  exact (ScheduledTransfer.copied_source_preserved false false read write reset
    (rewind 0 w c B) B z).trans (rewind_cells 0 w c B 0 z)

theorem block_target (hinv : Function.LeftInverse write read) (B : ℕ) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (j : ℕ) (hj : j<B) :
    cells (blockRun read write reset B w c) 1 (c.work.pos 1+j)=
      cells c 0 (c.work.pos 0-B+j) := by
  have h := ScheduledTransfer.copied_target false false false read write reset (rewind 0 w c B) B j hj
  simp [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,
    rewind_position,rewind_cells] at h
  rw [blockRun,rewind_cells]
  exact h.trans (hinv _)

theorem block_outside (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 1 ∨ c.work.pos 1+B≤z) :
    cells (blockRun read write reset B w c) 1 z=cells c 1 z := by
  rw [blockRun,rewind_cells]
  have h := ScheduledTransfer.copied_target_outside false false false read write reset
    (rewind 0 w c B) B z (by simpa [ScheduledTransfer.target,rewind_position] using hz)
  exact h.trans (rewind_cells 0 w c B 1 z)

theorem block_io (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (blockRun read write reset B w c).inputPos=c.inputPos ∧
    (blockRun read write reset B w c).outRev=c.outRev := by
  have h := ScheduledTransfer.copied_io false false false read write reset (rewind 0 w c B) B
  have h₀ := rewind_io 0 w c B
  have h₁ := rewind_io 0 w (ScheduledTransfer.copied false false false read write reset (rewind 0 w c B) B) B
  exact ⟨h₁.1.trans (h.1.trans h₀.1),h₁.2.trans (h.2.trans h₀.2)⟩

def run (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  (blockRun read write reset B w)^[n] c

def schedule (B n : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  repeatSchedule (blockSchedule read write reset B) (action 0 ⟨none,.stay⟩) (4*B) n

theorem schedule_exact (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (schedule read write reset B n) w c (n*(4*B))=run read write reset B n w c := by
  simpa only [schedule,run,block_exact] using
    repeat_exact (blockSchedule read write reset B) (action 0 ⟨none,.stay⟩) (4*B) n w c

theorem schedule_active (B n i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (schedule read write reset B n i) c := by
  apply ScheduledWord.schedule_active
  · exact active _ _ _
  · intro _ _ j; exact block_active read write reset B j c

theorem positions (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (run read write reset B n w c).work.pos 0=c.work.pos 0-n*B ∧
    (run read write reset B n w c).work.pos 1=c.work.pos 1+n*B := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    simp only [run,Function.iterate_succ_apply']
    change (blockRun read write reset B w (run read write reset B n w c)).work.pos 0=_ ∧
      (blockRun read write reset B w (run read write reset B n w c)).work.pos 1=_
    rw [(block_positions read write reset B w _).1,(block_positions read write reset B w _).2,ih.1,ih.2]
    push_cast
    constructor <;> ring

theorem source_preserved (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ) :
    cells (run read write reset B n w c) 0 z=cells c 0 z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cells ((blockRun read write reset B w)^[n+1] c) 0 z=_
    rw [Function.iterate_succ_apply',block_source]
    exact ih

theorem target_outside (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (z : ℤ)
    (hz : z<c.work.pos 1 ∨ c.work.pos 1+n*B≤z) :
    cells (run read write reset B n w c) 1 z=cells c 1 z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cells ((blockRun read write reset B w)^[n+1] c) 1 z=_
    rw [Function.iterate_succ_apply',block_outside]
    · apply ih
      have : (n : ℤ)*B≤(n+1)*B := mul_le_mul_of_nonneg_right (by omega) (Nat.cast_nonneg B)
      push_cast at hz
      omega
    · change z<(run read write reset B n w c).work.pos 1 ∨
        (run read write reset B n w c).work.pos 1+B≤z
      rw [(positions read write reset B n w c).2]
      push_cast at hz
      have : (0 : ℤ)≤n*B := mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg B)
      rcases hz with hz | hz
      · left; omega
      · right; nlinarith

theorem target_blocks (hinv : Function.LeftInverse write read) (B n : ℕ) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (k j : ℕ) (hk : k<n) (hj : j<B) :
    cells (run read write reset B n w c) 1 (c.work.pos 1+k*B+j)=
      cells c 0 (c.work.pos 0-(k+1)*B+j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    change cells ((blockRun read write reset B w)^[n+1] c) 1 _=_
    rw [Function.iterate_succ_apply']
    change cells (blockRun read write reset B w (run read write reset B n w c)) 1 _=_
    by_cases hkn : k=n
    · subst k
      rw [← (positions read write reset B n w c).2,block_target read write reset hinv B w _ j hj,
        (positions read write reset B n w c).1,source_preserved]
      congr 2
      ring
    · rw [block_outside]
      · exact ih (by omega)
      · left
        rw [(positions read write reset B n w c).2]
        have hmul : (k+1)*B≤n*B := Nat.mul_le_mul_right B (by omega)
        have hlt : k*B+j<n*B := by nlinarith
        have hltz : (k : ℤ)*B+j<n*B := by exact_mod_cast hlt
        omega

theorem io (B n : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (run read write reset B n w c).inputPos=c.inputPos ∧
    (run read write reset B n w c).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [run,Function.iterate_succ_apply']
    have h := block_io read write reset B w (run read write reset B n w c)
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

def drift (B : ℕ) (t : Fin 2) : ℤ := if t=0 then -(B : ℤ) else B

theorem block_endpoint (B : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (trajectory (blockSchedule read write reset B) w c (4*B)).work.pos t=c.work.pos t+drift B t := by
  rw [block_exact]
  have h := block_positions read write reset B w c
  fin_cases t <;> simp [drift,h.1,h.2,sub_eq_add_neg]

theorem drift_abs (B : ℕ) (t : Fin 2) : |(drift B t : ℝ)|=B := by
  unfold drift
  split_ifs <;> simp

/-- All intermediate head positions stay within five block widths of
the straight interpolation of their endpoints. No inner-path hypothesis
is added: the generic paid unit-step bound supplies the estimate. -/
theorem linear_error (B n : ℕ) (hB : 0<B) (w : List Bool)
    (c : NativeIO.Config (Fin 2) M) (t : Fin 2) (m : ℕ) (hm : m≤n*(4*B)) :
    |((trajectory (schedule read write reset B n) w c m).work.pos t : ℝ)-
      c.work.pos t-(m : ℝ)/(4*B)*(drift B t : ℝ)|≤5*B := by
  have h := repeat_linear_error (blockSchedule read write reset B) (action 0 ⟨none,.stay⟩)
    (4*B) (by omega) w t (drift B t) (fun d => block_endpoint read write reset B w d t) n c m hm
  rw [drift_abs] at h
  simpa only [schedule,Nat.cast_mul,Nat.cast_ofNat,show (4 : ℝ)*B+B=5*B by ring] using h

end TransposeFollowup.BlockReverseTransfer
