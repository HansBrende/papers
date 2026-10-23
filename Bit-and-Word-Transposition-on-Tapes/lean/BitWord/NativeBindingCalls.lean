import BitWord.NativeBankCalls

/-! Framed calls with any fixed finite wiring, including restoring-head calls. -/
namespace BitWord.NativeBindingCalls
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
set_option autoImplicit false
variable {T U L J : Type*}

theorem call (b : FinitePortBinding T U) (lab : L → J)
    (sub : Microcode.Program T L) (prog : Microcode.Program U J)
    (hc : ∀ pc,sub pc ≠ .halt → sub pc ≠ .reject →
      prog (lab pc)=MicrocodeEmbedding.instruction b.ports lab (sub pc))
    (pc qc : L) (bank : U → Tape Bool) (pos : U → ℤ)
    (out : T → Tape Bool) (endPos : T → ℤ) (n : ℕ)
    (ht : OperationalTrace.Trace (NativeMicrocode.step sub) (NativeMicrocode.Active sub) n
      (workCfg pc (fun t => bank (b.ports t)) (fun t => pos (b.ports t)))
      (workCfg qc out endPos)) :
    OperationalTrace.Trace (NativeMicrocode.step prog) (NativeMicrocode.Active prog) n
      (workCfg (lab pc) bank pos) (workCfg (lab qc) (b.values out bank) (b.values endPos pos)) := by
  have hh := MicrocodeEmbedding.trace_embed b.ports lab sub prog (frame bank pos) hc ht
  simpa only [embed_work,b.values_project] using hh

theorem restoring_call (b : FinitePortBinding T U) (lab : L → J)
    (sub : Microcode.Program T L) (prog : Microcode.Program U J)
    (hc : ∀ pc,sub pc ≠ .halt → sub pc ≠ .reject →
      prog (lab pc)=MicrocodeEmbedding.instruction b.ports lab (sub pc))
    (pc qc : L) (bank : U → Tape Bool) (pos : U → ℤ) (out : T → Tape Bool) (n : ℕ)
    (ht : OperationalTrace.Trace (NativeMicrocode.step sub) (NativeMicrocode.Active sub) n
      (workCfg pc (fun t => bank (b.ports t)) (fun t => pos (b.ports t)))
      (workCfg qc out (fun t => pos (b.ports t)))) :
    OperationalTrace.Trace (NativeMicrocode.step prog) (NativeMicrocode.Active prog) n
      (workCfg (lab pc) bank pos) (workCfg (lab qc) (b.values out bank) pos) := by
  simpa only [b.values_project] using call b lab sub prog hc pc qc bank pos out _ n ht

end BitWord.NativeBindingCalls
