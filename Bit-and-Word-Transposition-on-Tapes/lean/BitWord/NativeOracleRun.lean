import BitWord.NativeOracleSemantics
import Transpose.Tape.Encode

/-! Finite native execution of the captured oracle, from an explicitly prepared
input copy. Loading and erasing that preparation are separate native callers. -/
namespace BitWord.NativeOracle
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false

/-- Simulate exactly the active original transitions, retaining the actual
work tapes and the actual captured output. -/
theorem execution_trace (M : Transpose.TM) (w : List Bool) (t : ℕ)
    (state : State M) (tapes : Tapes M) (pos : Positions M) (outRev : List Bool)
    (hinput : InputRep M w tapes pos) (houtput : Captured M outRev tapes pos)
    (last : Transpose.Config (plane M))
    (hrun : Transpose.stepN (plane M) w t
      (observe M state tapes pos outRev)=some last) :
    ∃ tapes' pos',
      Trace M (t*(workCount M+2)) (cfg M (.input state) tapes pos)
        (cfg M (.input last.state) tapes' pos') ∧
      observe M last.state tapes' pos' last.outRev=last ∧
      InputRep M w tapes' pos' ∧ Captured M last.outRev tapes' pos' := by
  induction t generalizing state tapes pos outRev with
  | zero =>
    have he : observe M state tapes pos outRev=last := Option.some.inj hrun
    subst last
    exact ⟨tapes,pos,by simpa [observe] using (OperationalTrace.Trace.refl (cfg M (.input state) tapes pos)),
      rfl,hinput,houtput⟩
  | succ t ih =>
    cases hd : (plane M).δ state (inputSymbol (tapes .input).head)
      (scanned M tapes) with
    | none =>
      have hh := (halt_observe M state w tapes pos outRev hinput).mpr hd
      simp [Transpose.stepN,hh] at hrun
    | some tr =>
      have hs := transition_observe M state w tapes pos outRev hinput tr hd
      rw [Transpose.stepN,hs] at hrun
      obtain ⟨ts,ps,ht,ho,hi,hc⟩ := ih tr.1 (transitioned M tr tapes pos).core.tapes
        (transitioned M tr tapes pos).pos (nextOutput tr.2.2.2 outRev)
        (transition_input M w tapes pos hinput tr) (transition_captured M tapes pos outRev houtput tr) hrun
      have hm := macro_trace M state tapes pos
      dsimp only [plane] at hd
      simp only [macroResult,hd] at hm
      refine ⟨ts,ps,?_,ho,hi,hc⟩
      have h := NativeCountedLoop.trace_trans hm ht
      simpa only [Nat.succ_mul,Nat.add_comm] using h

theorem captured_call_trace (M : Transpose.TM) (w : List Bool) (t : ℕ)
    (state : State M) (tapes : Tapes M) (pos : Positions M) (outRev : List Bool)
    (hinput : InputRep M w tapes pos) (houtput : Captured M outRev tapes pos)
    (last : Transpose.Config (plane M))
    (hrun : Transpose.stepN (plane M) w t
      (observe M state tapes pos outRev)=some last)
    (hhalt : Transpose.step (plane M) w last=none) :
    ∃ tapes' pos', Trace M ((t+1)*(workCount M+2)) (cfg M (.input state) tapes pos)
      (cfg M .done tapes' pos') ∧ InputRep M w tapes' pos' ∧ Captured M last.outRev tapes' pos' := by
  obtain ⟨ts,ps,ht,ho,hi,hc⟩ := execution_trace M w t state tapes pos outRev hinput houtput last hrun
  have hh := (halt_observe M last.state w ts ps last.outRev hi).mp (by simpa [ho] using hhalt)
  have hm := macro_trace M last.state ts ps
  dsimp only [plane] at hh
  simp only [macroResult,hh] at hm
  refine ⟨ts,ps,?_,hi,?_⟩
  · simpa only [Nat.add_mul,Nat.one_mul] using NativeCountedLoop.trace_trans ht hm
  · simpa [Captured] using hc

def prepared (M : Transpose.TM) (w : List Bool) : Tapes M
  | .input => Turing.Tape.mk₂ [.start] (w.map Sym.data ++ [.stop])
  | .capture => Turing.Tape.mk₂ [.start] []
  | _ => AbsoluteTape.blank

@[simp] theorem inputSymbol_getI (w : List Bool) (n : ℕ) :
    inputSymbol ((w.map Sym.data).getI n)=Transpose.nth w n := by
  induction w generalizing n with
  | nil => simp [inputSymbol,Transpose.nth]
  | cons b bs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

@[simp] theorem inputSymbol_getI_stop (w : List Bool) (n : ℕ) :
    inputSymbol ((w.map Sym.data ++ [Sym.stop]).getI n)=Transpose.nth w n := by
  induction w generalizing n with
  | nil => cases n <;> simp [inputSymbol,Transpose.nth]
  | cons b bs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem prepared_input (M : Transpose.TM) (w : List Bool) :
    InputRep M w (prepared M w) (fun _ => 0) := by
  intro z
  cases z with
  | ofNat n => simp [InputRep,prepared,AbsoluteTape.cells,Turing.Tape.mk₂,Transpose.readInput,Int.natCast_nonneg]
  | negSucc n =>
    cases n <;> simp [prepared,AbsoluteTape.cells,Turing.Tape.mk₂,Turing.Tape.mk',Turing.Tape.nth,
      Turing.ListBlank.nth_mk,Transpose.readInput,inputSymbol] <;> rfl

theorem prepared_observe (M : Transpose.TM) (w : List Bool) :
    observe M 0 (prepared M w) (fun _ => 0) []=Transpose.init (plane M) := by
  unfold observe Transpose.init
  congr 1
  funext i z
  simp only [prepared,AbsoluteTape.blank_cells]
  rfl

@[simp] theorem prepared_captured (M : Transpose.TM) (w : List Bool) :
    Captured M [] (prepared M w) (fun _ => 0) := by
  exact ⟨rfl,rfl⟩

/-- A genuine native active trace, obtained from the given oracle's bounded
halting property. The interpreter program itself is independent of w and T. -/
theorem prepared_call (M : Transpose.TM) (w out : List Bool) (T : ℕ)
    (h : Transpose.ComputesWithin M w out T) :
    ∃ t ≤ (T+1)*(workCount M+2), ∃ tapes pos,
      Trace M t (cfg M (start M) (prepared M w) (fun _ => 0)) (cfg M .done tapes pos) ∧
      Captured M out.reverse tapes pos := by
  have hplane : Transpose.ComputesWithin (plane M) w out T := by
    rw [plane_eq]
    exact BitPlaneMachine.computesWithin M w out T h
  obtain ⟨t,ht,last,hrun,hhalt,hout⟩ := hplane
  rw [← prepared_observe M w] at hrun
  obtain ⟨ts,ps,htr,_,hc⟩ := captured_call_trace M w t 0 (prepared M w) (fun _ => 0) []
    (prepared_input M w) (prepared_captured M w) last hrun hhalt
  refine ⟨(t+1)*(workCount M+2),Nat.mul_le_mul_right _ (by omega),ts,ps,htr,?_⟩
  have he : last.outRev=out.reverse := by rw [← hout,List.reverse_reverse]
  simpa [he] using hc

end BitWord.NativeOracle
