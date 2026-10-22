import TransposeFollowup.NativeInputRewind

namespace TransposeFollowup.NativeInputRewind
open FixedTapeCompiler
set_option autoImplicit false
variable {T J : Type*}

def atLabel (pc : J) (frame : MicrocodeEmbedding.Frame T) (ip : ℤ) (outRev : List Bool) : NativeIO.Config T J :=
  ⟨⟨⟨pc,frame.tapes⟩,frame.pos⟩,ip,outRev⟩

theorem embed_cfg (labels : Label → J) (pc : Label) (frame base : MicrocodeEmbedding.Frame T)
    (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed (Function.Embedding.refl T) labels (cfg pc frame ip outRev) base=
      atLabel (labels pc) frame ip outRev := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed cfg atLabel
  congr 2
  · congr 1
    funext t
    exact MicrocodeEmbedding.extend_at (Function.Embedding.refl T) t _ _
  · funext t
    exact MicrocodeEmbedding.extend_at (Function.Embedding.refl T) t _ _

theorem framed_trace (labels : Label → J) (target : NativeIO.Program T J) (selected : J → Bool)
    (frame : MicrocodeEmbedding.Frame T) (w outRev : List Bool)
    (hsel : ∀ pc,selected (labels pc)=false)
    (hc : ∀ pc,program T pc≠.work .halt → program T pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction (Function.Embedding.refl T) labels (program T pc)) :
    OperationalTrace.Trace (NativeIOFusion.step target selected w) (NativeIOFusion.Active target selected)
      (2*w.length+3) (atLabel (labels .left) frame w.length outRev) (atLabel (labels .done) frame 0 outRev) := by
  have h:=NativeIOFusionCalls.unselected_trace (Function.Embedding.refl T) labels (program T) target selected frame w
    hsel hc (complete_trace w frame outRev)
  simpa only [embed_cfg] using h

theorem native_call {k q : ℕ} (encoding : NativeMicrocode.Encoding T J k q)
    (labels : Label → J) (target : NativeIO.Program T J) (selected : J → Bool)
    (frame : MicrocodeEmbedding.Frame T) (w outRev : List Bool)
    (hsel : ∀ pc,selected (labels pc)=false)
    (hc : ∀ pc,program T pc≠.work .halt → program T pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction (Function.Embedding.refl T) labels (program T pc)) :
    Transpose.stepN (NativeIOFusion.machine encoding target selected) w (2*w.length+3)
      (NativeIOFusion.denote encoding target selected (atLabel (labels .left) frame w.length outRev))=
      some (NativeIOFusion.denote encoding target selected (atLabel (labels .done) frame 0 outRev)) :=
  NativeIOFusion.trace_stepN encoding target selected w (framed_trace labels target selected frame w outRev hsel hc)

end TransposeFollowup.NativeInputRewind
