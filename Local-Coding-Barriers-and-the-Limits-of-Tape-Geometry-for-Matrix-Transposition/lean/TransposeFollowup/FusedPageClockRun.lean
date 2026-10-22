import TransposeFollowup.FusedPageClockRewind
import TransposeFollowup.NativeReadFusionBehavior

namespace TransposeFollowup.FusedPageClock
open FixedTapeCompiler CopyMachine
open ReusablePageClock (Port Label program cfg)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

theorem rewind_tail (ops : Fin q → PageOpcode) (xs : List Bool) (s : Sym Bool) (hs : s≠.start) (hb : s≠.blank)
    (post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops (xs.length+2) (cfg (.inr .back) ⟨symbols xs++[.start],s::post⟩ pos)
      (cfg (.inr .done) ⟨[.start],(symbols xs).reverse++s::post⟩ (shiftClock pos (-(xs.length:ℤ)))) := by
  induction xs generalizing s post pos with
  | nil =>
    have ha:=rewind_trace ops s .start hs hb [] post pos
    have ht:=rewind_finish_trace ops [] (s::post) (shiftClock pos (-1))
    simpa only [List.length_nil,symbols,List.map_nil,List.reverse_nil,List.nil_append,Nat.cast_zero,
      neg_zero,shiftClock_add,neg_add_cancel,shiftClock_zero] using trace_trans ha ht
  | cons b xs ih =>
    have ha:=rewind_trace ops s (.data b) hs hb (symbols xs++[.start]) post pos
    have ht:=ih (.data b) (by simp) (by simp) (s::post) (shiftClock pos (-1))
    have hc:1+(xs.length+2)=(b::xs).length+2:=by simp;omega
    have hp:(-1:ℤ)+ -(xs.length:ℤ) = -((b::xs).length:ℤ):=by simp
    simpa only [symbols,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,shiftClock_add,hc,hp] using trace_trans ha ht

theorem rewind_complete (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (xs.length+2) (cfg (.inr .back) (RowStream.closedTape xs) pos)
      (cfg (.inr .done) (Counter.marked xs) (shiftClock pos (-(xs.length:ℤ)))) := by
  simpa only [List.length_reverse,symbols,List.map_reverse,List.reverse_reverse,RowStream.closedTape,Counter.marked]
    using rewind_tail ops xs.reverse .stop (by simp) (by simp) [] pos

theorem complete_trace (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (2*xs.length+3) (cfg (.inl .read) (Counter.marked xs) pos)
      (cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))) := by
  have ha:=scan_trace ops xs pos
  have hb:=rewind_complete ops xs (PageClock.advance ops pos xs.length (xs.count true))
  have hn:(xs.length+1)+(xs.length+2)=2*xs.length+3:=by omega
  have hp:shiftClock (PageClock.advance ops pos xs.length (xs.count true)) (-(xs.length:ℤ))=
      PageClock.advance ops pos 0 (xs.count true):=by
    funext p;cases p <;> simp [shiftClock,PageClock.advance]
  simpa only [hn,hp] using trace_trans ha hb

noncomputable def nativeMachine (ops : Fin q → PageOpcode) :=
  NativeReadFusion.machine (ReusablePageClock.nativeEncoding q) (program ops) selected

theorem native_complete (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (nativeMachine ops) input (2*xs.length+3)
      (NativeReadFusion.denote (ReusablePageClock.nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inl .read) (Counter.marked xs) pos))=
      some (NativeReadFusion.denote (ReusablePageClock.nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true)))) ∧
    Transpose.step (nativeMachine ops) input
      (NativeReadFusion.denote (ReusablePageClock.nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))))=none := by
  refine ⟨NativeReadFusion.trace_stepN _ _ _ input ip outRev (complete_trace ops xs pos),?_⟩
  apply (NativeReadFusion.step_none_iff _ _ _ input ip outRev _).mpr
  rw [NativeReadFusion.active_iff]
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,NativeSealBack.program]

theorem fixed_resources (ops : Fin q → PageOpcode) : (nativeMachine ops).k=q+1 ∧
    (nativeMachine ops).g+1=5 ∧ (nativeMachine ops).q+1=11 ∧ (ReusablePageClock.nativeEncoding q).label (.inl .read)=0 :=
  ReusablePageClock.fixed_resources ops

end TransposeFollowup.FusedPageClock
