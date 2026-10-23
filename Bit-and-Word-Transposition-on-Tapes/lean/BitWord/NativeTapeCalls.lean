import BitWord.NativeBankCalls
import TransposeFollowup.NativeSealBack
import TransposeFollowup.NativeBuffer
import TransposeFollowup.NativeErase

/-! Reusable paid one-tape calls inside any fixed literal caller. -/
namespace BitWord.NativeTapeCalls
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames
variable {U J L : Type*} [DecidableEq U]

abbrev Trace (p : Microcode.Program U J) :=
  OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p)

def Code (p : Microcode.Program U J) (t : U) (labels : L → J) (sub : Microcode.Program (Fin 1) L) :=
  ∀ pc, sub pc ≠ .halt → sub pc ≠ .reject →
    p (labels pc)=MicrocodeEmbedding.instruction (singleBinding t).ports labels (sub pc)

theorem initialize_call (p : Microcode.Program U J) (t : U) (lab : NativeBuffer.Label → J)
    (hc : Code p t lab NativeBuffer.program) (s : U → Tape Bool) (pos : U → ℤ)
    (hs : s t=⟨[],[]⟩) :
    ∃ n ≤ 2,Trace p n (workCfg (lab (.erase 0)) s pos)
      (workCfg (lab .done) (Function.update s t (NativeSealBack.openWord [])) pos) := by
  obtain ⟨n,hn,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos t)
  have hh := call_single t lab NativeBuffer.program p hc (.erase 0) .done s pos
    (NativeSealBack.openWord []) (pos t) n
  have hh' := hh (by simpa [workCfg,NativeBuffer.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols] using htr)
  exact ⟨n,hn,by simpa only [Function.update_eq_self] using hh'⟩

theorem seal_call (p : Microcode.Program U J) (t : U) (lab : NativeSealBack.Label → J)
    (hc : Code p t lab NativeSealBack.program) (s : U → Tape Bool) (pos : U → ℤ)
    (xs : List Bool) (hs : s t=NativeSealBack.openWord xs) :
    ∃ n ≤ 2*xs.length+5,Trace p n (workCfg (lab .seal) s pos)
      (workCfg (lab .done) (Function.update s t (Counter.marked xs))
        (Function.update pos t (pos t-xs.length))) := by
  obtain ⟨n,hn,htr⟩ := NativeSealBack.seal_trace xs (fun _ => pos t)
  refine ⟨n,hn,call_single t lab NativeSealBack.program p hc .seal .done s pos
    (Counter.marked xs) (pos t-xs.length) n ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

theorem rewind_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ n ≤ 2*xs.length+4,
      Trace NativeSealBack.program n
        (NativeSealBack.cfg .back ⟨(symbols xs).reverse++[.start],[.stop]⟩ pos).denote
        (NativeSealBack.cfg .done (Counter.marked xs) (fun i => pos i-xs.length)).denote := by
  have hr := NativeSealBack.seal_run xs pos
  rw [show 2*xs.length+5=1+(2*xs.length+4) by omega,NativeZipper.run_add] at hr
  have hf : NativeZipper.run NativeSealBack.program 1
      (NativeSealBack.cfg .seal (NativeSealBack.openWord xs) pos)=
      NativeSealBack.cfg .back ⟨(symbols xs).reverse++[.start],[.stop]⟩ pos := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
      NativeSealBack.program,NativeSealBack.cfg,NativeSealBack.openWord,Microcode.focus,
      Microcode.single,Microcode.Action.apply,Tape.write,NativeMicrocode.direction,Transpose.Dir.shift]
    constructor <;> funext i <;> fin_cases i <;> simp
  rw [hf] at hr
  exact NativeZipper.trace_of_run NativeSealBack.program hr

theorem rewind (p : Microcode.Program U J) (t : U) (lab : NativeSealBack.Label → J)
    (hc : Code p t lab NativeSealBack.program) (s : U → Tape Bool) (pos : U → ℤ)
    (xs : List Bool) (hs : s t=⟨(symbols xs).reverse++[.start],[.stop]⟩) :
    ∃ n ≤ 2*xs.length+4,Trace p n (workCfg (lab .back) s pos)
      (workCfg (lab .done) (Function.update s t (Counter.marked xs))
        (Function.update pos t (pos t-xs.length))) := by
  obtain ⟨n,hn,htr⟩ := rewind_trace xs (fun _ => pos t)
  refine ⟨n,hn,call_single t lab NativeSealBack.program p hc .back .done s pos
    (Counter.marked xs) (pos t-xs.length) n ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

theorem erase (p : Microcode.Program U J) (t : U) (lab : NativeErase.Label → J)
    (hc : Code p t lab NativeErase.program) (s : U → Tape Bool) (pos : U → ℤ)
    (xs : List Bool) (hs : s t=Counter.marked xs) :
    ∃ n ≤ 4*xs.length+4,Trace p n (workCfg (lab 2) s pos)
      (workCfg (lab 0) (Function.update s t ⟨[],[]⟩) pos) := by
  obtain ⟨n,hn,htr⟩ := NativeErase.erase_trace xs (fun _ => pos t)
  have hh := call_single t lab NativeErase.program p hc 2 0 s pos ⟨[],[]⟩ (pos t) n
  have hh' := hh (by simpa [workCfg,NativeErase.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨n,hn,by simpa only [Function.update_eq_self] using hh'⟩

/-- The rewind fragment is also safe when already positioned at a marked
word's first cell, including the empty word. -/
theorem rewind_start_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ n ≤ 4,Trace NativeSealBack.program n
      (NativeSealBack.cfg .back (Counter.marked xs) pos).denote
      (NativeSealBack.cfg .done (Counter.marked xs) pos).denote := by
  apply NativeZipper.trace_of_run NativeSealBack.program
  cases xs <;> simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    NativeSealBack.program,NativeSealBack.cfg,Microcode.focus,Counter.marked,symbols,
    Tape.read,Microcode.single,Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,
    NativeMicrocode.direction,Transpose.Dir.shift]
  all_goals constructor <;> funext i <;> fin_cases i <;> simp

theorem rewind_start (p : Microcode.Program U J) (t : U) (lab : NativeSealBack.Label → J)
    (hc : Code p t lab NativeSealBack.program) (s : U → Tape Bool) (pos : U → ℤ)
    (xs : List Bool) (hs : s t=Counter.marked xs) :
    ∃ n ≤ 4,Trace p n (workCfg (lab .back) s pos) (workCfg (lab .done) s pos) := by
  obtain ⟨n,hn,htr⟩ := rewind_start_trace xs (fun _ => pos t)
  have hh := call_single t lab NativeSealBack.program p hc .back .done s pos (s t) (pos t) n
  have hh' := hh (by simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨n,hn,by simpa only [Function.update_eq_self] using hh'⟩

end BitWord.NativeTapeCalls
