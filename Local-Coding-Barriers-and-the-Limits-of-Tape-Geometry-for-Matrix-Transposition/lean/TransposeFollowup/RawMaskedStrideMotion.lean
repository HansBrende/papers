import TransposeFollowup.RawMaskedStrideCorrectness
import TransposeFollowup.MaskedStrideZeroLimit

/-! Exact processing-window head positions of the raw-input machine, and
their small-stride limits. Time is measured from the end of the paid 4P
loading/rewind prefix. Sampling freezes at the end of processing; the later
cleanup/output phases are not part of this window. -/
namespace TransposeFollowup.RawMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO Set Filter Topology
set_option autoImplicit false

theorem processing_prefix (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ)
    (w : List Bool) (n : ℕ) (hn : n ≤ MaskedStrideScan.ticks P S) :
    trajectory (schedule isPrefix mask P S) w initial (4*P+n)=
      trajectory (MaskedStrideScan.schedule isPrefix mask P S) w (prepared P w) n := by
  rw [show 4*P+n=3*P+(P+n) by omega]
  unfold schedule
  rw [append_exact,append_exact,ScheduledRawInput.schedule_exact,append_prefix _ _ _ _ _ _ hn]
  rfl

theorem processing_workTraj (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) (n : ℕ) (hn : n ≤ MaskedStrideScan.ticks P S) :
    Transpose.Tape.workTraj (machine isPrefix mask P S) w (4*P+n) ((encoding P S).port 0)=
      MaskedStrideScan.bankPosition P S n ∧
    Transpose.Tape.workTraj (machine isPrefix mask P S) w (4*P+n) ((encoding P S).port 1)=
      MaskedStrideScan.scratchPosition P S n := by
  have htime : 4*P+n ≤ ticks P S := by unfold ticks; omega
  have h := native_prefix (encoding P S) (schedule isPrefix mask P S) w initial
    (fun i _ => schedule_active isPrefix mask P S i _) (4*P+n) htime
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P S+1)) initial).denote
      (encoding P S) (program (schedule isPrefix mask P S) (ticks P S))=
      Transpose.init (machine isPrefix mask P S) :=
    NativeIO.blank_denote (encoding P S) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at h
  have hr := (Transpose.Tape.Impl.stepN_init_eq_some_iff (4*P+n) _).mp h
  have hp0 := congrArg (fun d => d.workPos ((encoding P S).port 0)) hr.2
  have hp1 := congrArg (fun d => d.workPos ((encoding P S).port 1)) hr.2
  change Transpose.Tape.workTraj (machine isPrefix mask P S) w (4*P+n) _=_ at hp0 hp1
  refine ⟨hp0.trans ?_,hp1.trans ?_⟩
  all_goals
    simp only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply,
      processing_prefix isPrefix mask P S w n hn]
  have hp := MaskedStrideScan.schedule_positions isPrefix mask P hS w (prepared P w) n
  · simpa only [prepared_position,zero_add] using hp.1
  · simpa only [prepared_position,zero_add] using
      (MaskedStrideScan.schedule_positions isPrefix mask P hS w (prepared P w) n).2

theorem processing_zero_stride_limits {P S : ℕ → ℕ}
    (hP : ∀ i, 0<P i) (hS : ∀ i, 0<S i)
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hsmall : Tendsto (fun i => (S i : ℝ)/P i) atTop (𝓝 0))
    (modes : ℕ → Bool) (masks : ℕ → ℕ → Bool) (inputs : ℕ → List Bool) :
    TendstoUniformlyOn (fun i t =>
      (Transpose.Tape.workTraj (machine (modes i) (masks i) (P i) (S i)) (inputs i)
        (4*P i+min ⌊(P i : ℝ)*t⌋₊ (MaskedStrideScan.ticks (P i) (S i)))
        ((encoding (P i) (S i)).port 0) : ℝ)/P i)
      (fun t => min (t/4) 1) atTop (Ici 0) ∧
    TendstoUniformlyOn (fun i t =>
      (Transpose.Tape.workTraj (machine (modes i) (masks i) (P i) (S i)) (inputs i)
        (4*P i+min ⌊(P i : ℝ)*t⌋₊ (MaskedStrideScan.ticks (P i) (S i)))
        ((encoding (P i) (S i)).port 1) : ℝ)/P i)
      (fun _ => 0) atTop (Ici 0) := by
  have h := MaskedStrideScan.zero_stride_uniform_limits hP hS hPinf hsmall
  constructor
  · apply h.1.congr
    exact Filter.Eventually.of_forall fun i t _ => by
      have hp := (processing_workTraj (modes i) (masks i) (P i) (hS i) (inputs i)
        (min ⌊(P i : ℝ)*t⌋₊ (MaskedStrideScan.ticks (P i) (S i))) (Nat.min_le_right _ _)).1
      simpa only [Int.cast_natCast] using (congrArg (fun z : ℤ => (z : ℝ)/P i) hp).symm
  · apply h.2.congr
    exact Filter.Eventually.of_forall fun i t _ => by
      exact (congrArg (fun z : ℤ => (z : ℝ)/P i)
        (processing_workTraj (modes i) (masks i) (P i) (hS i) (inputs i)
          (min ⌊(P i : ℝ)*t⌋₊ (MaskedStrideScan.ticks (P i) (S i))) (Nat.min_le_right _ _)).2).symm

end TransposeFollowup.RawMaskedStride
