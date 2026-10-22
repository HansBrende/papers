import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.NativeHeadDisplacement

/-! Reuse the same four-state rewind while preserving an unread suffix.
The pre length is used only in its proof and cost,not supplied to control. -/
namespace TransposeFollowup.NativePrefixRewind
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem rewind_trace (pre suffix : List (Sym Bool)) (h : ∀ s ∈ pre,s≠.blank) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*pre.length+3,
      OperationalTrace.Trace (NativeMicrocode.step NativeSpanRewind.program) (NativeMicrocode.Active NativeSpanRewind.program) t
        (NativeSpanRewind.cfg .left ⟨pre.reverse,suffix⟩ pos).denote
        (NativeSpanRewind.cfg .done ⟨[],pre++suffix⟩ (fun p => pos p-pre.length)).denote := by
  have hr : ∀ s ∈ pre.reverse,s≠.blank := by intro s hs;exact h s (List.mem_reverse.mp hs)
  obtain ⟨t,ht,htr⟩:=NativeZipper.trace_of_run NativeSpanRewind.program (NativeSpanRewind.rewind_run pre.reverse suffix hr pos)
  exact ⟨t,by simpa only [List.length_reverse] using ht,by
    simpa only [List.length_reverse,List.reverse_reverse,NativeSpanRewind.cfg_blank_left] using htr⟩

theorem work_trace_bounds {T L : Type*} (p : Microcode.Program T L) {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c d) (t : T) :
    c.pos t-(n : ℤ)≤d.pos t ∧ d.pos t≤c.pos t+(n : ℤ) := by
  induction h with
  | refl c => simp
  | @cons n c d ha h ih =>
    have hs:=NativeHeadDisplacement.work_step_bounds p c t
    simp only [Nat.cast_add,Nat.cast_one]
    omega

end TransposeFollowup.NativePrefixRewind
