import TransposeFollowup.RawProgramShell
import TransposeFollowup.RawBankProgramApproximation

/-! Exact composition with raw IO without an input-independent body path.
The body is evaluated on the actual prepared state, including its data.
Only the suffix emitter has a fixed displacement function. -/
namespace TransposeFollowup.ScheduledNativeIO
set_option autoImplicit false
variable {T M : Type*}

theorem append_position_right (σ τ : ℕ → NativeIO.Program T M) (N L : ℕ)
    (w : List Bool) (t : T) (g : ℕ → ℤ)
    (hτ : ∀ c n, n≤L → (trajectory τ w c n).work.pos t=c.work.pos t+g n)
    (c : NativeIO.Config T M) (n : ℕ) (hn : n≤N+L) :
    (trajectory (append σ τ N) w c n).work.pos t=
      (trajectory σ w c (min n N)).work.pos t+g (n-N) := by
  by_cases h : n≤N
  · have hz : g 0=0 := by
      have hh := hτ c 0 (Nat.zero_le _)
      change c.work.pos t=c.work.pos t+g 0 at hh
      omega
    rw [append_prefix _ _ _ _ _ _ h,Nat.min_eq_left h,Nat.sub_eq_zero_of_le h,hz,add_zero]
  · conv_lhs => rw [show n=N+(n-N) by omega,append_exact]
    rw [hτ _ _ (by omega),Nat.min_eq_right (by omega)]

end TransposeFollowup.ScheduledNativeIO

namespace TransposeFollowup.RawProgramShell
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open NativeIOModeProduct
open RawBankProgram (ioPath)
set_option autoImplicit false
variable {F : Type*}

theorem prepare_position (P : ℕ) (w : List Bool) (c : State F)
    (n : ℕ) (hn : n≤4*P) (t : Fin 2) :
    (trajectory (ScheduledModeRawIO.prepareSchedule (Equiv.refl (Mode F)) P) w c n).work.pos t=
      c.work.pos t+ioPath P 0 t n := by
  unfold ScheduledModeRawIO.prepareSchedule
  rw [trajectory_eq]
  have hr (d : MaskedStrideCell.State) (m : ℕ) :
      (trajectory (fun _ => action 0 ⟨none,.left⟩) w d m).work.pos t=
        d.work.pos t+(-(if t=0 then (m : ℤ) else 0)) := by
    by_cases ht : t=0 <;> simpa [rewind,ht,sub_eq_add_neg] using rewind_position 0 w d m t
  have h := append_position ScheduledRawInput.schedule (fun _ => action 0 ⟨none,.left⟩)
    (3*P) P w t (fun m => ((if t=0 then (m+1)/3 else 0 : ℕ) : ℤ))
    (fun m => -(if t=0 then (m : ℤ) else 0))
    (fun d m _ => ScheduledRawInput.schedule_position w d m t)
    (fun d m _ => hr d m) (project (Equiv.refl (Mode F)) c) n (by omega)
  have hload : (min n (3*P)+1)/3=min ((n+1)/3) P := by omega
  have hrewind : min (n-3*P) P=n-3*P := by omega
  have hout : n-4*P=0 := by omega
  fin_cases t <;>
    simpa [ioPath,hload,hrewind,hout,sub_eq_add_neg,attach,project] using h

theorem position_decomposition (f : F) (P N : ℕ) (σ : ℕ → NativeIO.Program (Fin 2) (Mode F))
    (w : List Bool) (n : ℕ) (hn : n≤ticks P N) (t : Fin 2) :
    (trajectory (schedule P N σ) w (initial f) n).work.pos t=
      (trajectory σ w (prepared f P w) (min (n-4*P) N)).work.pos t+ioPath P N t n := by
  have hp : ∀ t, (prepared f P w).work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl (Mode F)) f P w).1
  by_cases h : n≤4*P
  · have h0 : n-4*P=0 := by omega
    have hout : n-(4*P+N)=0 := by omega
    rw [schedule,append_prefix _ _ _ _ _ _ (by omega),h0,Nat.zero_min,trajectory,hp,zero_add]
    have he := prepare_position P w (initial f) n h t
    simpa [initial,ScheduledModeRawIO.initial,attach,RawMaskedStride.initial,
      NativeMicrocode.blankConfig,ioPath,h0,hout] using he
  · have hstart : 3*P+P=4*P := by omega
    have he : n=(3*P+P)+(n-(3*P+P)) := by omega
    rw [schedule,he,append_exact]
    rw [show initial f=ScheduledModeRawIO.initial (Equiv.refl (Mode F)) f from rfl,
      ScheduledModeRawIO.prepare_exact]
    have hm : n-(3*P+P)≤N+3*P := by unfold ticks at hn; omega
    have hx := append_position_right σ (ScheduledModeRawIO.outputSchedule (Equiv.refl (Mode F)))
      N (3*P) w t (fun m => ((if t=0 then m/3 else 0 : ℕ) : ℤ))
      (fun d m _ => ScheduledModeRawIO.output_position _ w d m t)
      (prepared f P w) (n-(3*P+P)) hm
    rw [show (3*P+P)+(n-(3*P+P))=n by omega]
    change (trajectory (append σ (ScheduledModeRawIO.outputSchedule (Equiv.refl (Mode F))) N)
      w (prepared f P w) (n-(3*P+P))).work.pos t=_
    rw [hx,hstart]
    have hload : min ((n+1)/3) P=P := by omega
    have hrewind : min (n-3*P) P=P := by omega
    have hout : min ((n-(4*P+N))/3) P=(n-4*P-N)/3 := by unfold ticks at hn; omega
    by_cases ht : t=0 <;> simp [ioPath,hload,hrewind,hout,ht]

theorem ioPath_after (P N : ℕ) (t : Fin 2) (n : ℕ) (hn : ticks P N≤n) :
    ioPath P N t n=if t=0 then (P : ℤ) else 0 := by
  have ht := ticks_eq P N
  have hload : min ((n+1)/3) P=P := by omega
  have hrewind : min (n-3*P) P=P := by omega
  have hout : min ((n-(4*P+N))/3) P=P := by omega
  simp only [ioPath,hload,hrewind,hout,sub_self,zero_add]

theorem ioPath_frozen (P N : ℕ) (t : Fin 2) (n : ℕ) :
    ioPath P N t (min n (ticks P N))=ioPath P N t n := by
  by_cases h : n≤ticks P N
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega),ioPath_after P N t _ le_rfl,ioPath_after P N t n (by omega)]

end TransposeFollowup.RawProgramShell
