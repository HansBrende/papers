import TransposeFollowup.NativeReadFusionCore
import TransposeFollowup.MicrocodeEmbedding

/-! Fusion-aware subroutine embedding. Besides the current instruction,
a selected read needs the instruction at its chosen successor preserved.
A source return label outside these read successors remains customizable. -/
namespace TransposeFollowup.NativeReadFusionEmbedding
open FixedTapeCompiler
open MicrocodeEmbedding (instruction embed Frame)
set_option autoImplicit false
variable {T U L J : Type*}

theorem instruction_embed (ports : T ↪ U) (labels : L → J)
    (source : Microcode.Program T L) (target : Microcode.Program U J)
    (ss : L → Bool) (ts : J → Bool) (sh : T → CopyMachine.Sym Bool) (th : U → CopyMachine.Sym Bool)
    (hheads : ∀ t,th (ports t)=sh t) (pc : L) (hsel : ts (labels pc)=ss pc)
    (hc : target (labels pc)=instruction ports labels (source pc))
    (hr : ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      target (labels (next s))=instruction ports labels (source (next s))) :
    NativeReadFusion.effective target ts th (labels pc)=
      instruction ports labels (NativeReadFusion.effective source ss sh pc) := by
  by_cases hs : ss pc=true
  · cases hp : source pc with
    | read t next =>
      have hn:=hr hs t next hp (sh t)
      cases hh : source (next (sh t)) <;>
        simp [NativeReadFusion.effective,NativeReadFusion.instruction,hsel,hs,hc,hp,instruction,hheads,hn,hh]
    | _ => simp [NativeReadFusion.effective,NativeReadFusion.instruction,hsel,hs,hc,hp,instruction]
  · simp [NativeReadFusion.effective,NativeReadFusion.instruction,hsel,hs,hc]

theorem step_embed (ports : T ↪ U) (labels : L → J)
    (source : Microcode.Program T L) (target : Microcode.Program U J)
    (ss : L → Bool) (ts : J → Bool) (c : NativeMicrocode.Config T L) (frame : Frame U)
    (hsel : ts (labels c.core.pc)=ss c.core.pc)
    (hc : target (labels c.core.pc)=instruction ports labels (source c.core.pc))
    (hr : ss c.core.pc=true → ∀ t next,source c.core.pc=.read t next → ∀ s,
      target (labels (next s))=instruction ports labels (source (next s))) :
    NativeReadFusion.step target ts (embed ports labels c frame)=
      embed ports labels (NativeReadFusion.step source ss c) frame := by
  apply MicrocodeEmbedding.step_embed
  apply instruction_embed ports labels source target ss ts _ _ _ c.core.pc hsel hc hr
  intro t
  simp only [embed,MicrocodeEmbedding.extend_at]

theorem active_embed (ports : T ↪ U) (labels : L → J)
    (source : Microcode.Program T L) (target : Microcode.Program U J)
    (ss : L → Bool) (ts : J → Bool) (c : NativeMicrocode.Config T L) (frame : Frame U)
    (hc : target (labels c.core.pc)=instruction ports labels (source c.core.pc))
    (ha : NativeReadFusion.Active source ss c) :
    NativeReadFusion.Active target ts (embed ports labels c frame) := by
  rw [NativeReadFusion.active_iff] at ha ⊢
  exact MicrocodeEmbedding.active_embed ports labels source target c frame hc ha

theorem trace_embed (ports : T ↪ U) (labels : L → J)
    (source : Microcode.Program T L) (target : Microcode.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject → target (labels pc)=instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      target (labels (next s))=instruction ports labels (source (next s)))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step source ss) (NativeReadFusion.Active source ss) n c d) :
    OperationalTrace.Trace (NativeReadFusion.step target ts) (NativeReadFusion.Active target ts) n
      (embed ports labels c frame) (embed ports labels d frame) := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d ha tr ih =>
    have hh:=(NativeReadFusion.active_iff source ss c).mp ha
    have hcode:=hc c.core.pc hh.1 hh.2
    refine .cons (active_embed ports labels source target ss ts c frame hcode ha) ?_
    rw [step_embed ports labels source target ss ts c frame (hsel c.core.pc) hcode (hr c.core.pc)]
    exact ih

theorem native_call {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : T ↪ U) (labels : L → J) (source : Microcode.Program T L) (target : Microcode.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject → target (labels pc)=instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      target (labels (next s))=instruction ports labels (source (next s)))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step source ss) (NativeReadFusion.Active source ss) n c d) :
    Transpose.stepN (NativeReadFusion.machine encoding target ts) w n
      (NativeReadFusion.denote encoding target ts ip outRev (embed ports labels c frame))=
      some (NativeReadFusion.denote encoding target ts ip outRev (embed ports labels d frame)) :=
  NativeReadFusion.trace_stepN encoding target ts w ip outRev (trace_embed ports labels source target ss ts frame hsel hc hr h)

end TransposeFollowup.NativeReadFusionEmbedding
