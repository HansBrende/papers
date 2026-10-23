import TransposeFollowup.NativeIOEmbedding
import TransposeFollowup.PortBindingFrame

/-! Tape-configuration identities for the fixed native shear caller. -/
namespace TransposeFollowup.NativeExpanderShearFrames
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {T U L J : Type*}

def workCfg (pc : L) (s : T → Tape Bool) (pos : T → ℤ) : NativeMicrocode.Config T L :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg (pc : L) (s : T → Tape Bool) (pos : T → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config T L :=
  ⟨workCfg pc s pos,ip,outRev⟩
def frame (s : T → Tape Bool) (pos : T → ℤ) : MicrocodeEmbedding.Frame T :=
  ⟨fun p => (s p).denote,pos⟩

theorem embed_work (b : FinitePortBinding T U) (labels : L → J) (pc : L)
    (s : T → Tape Bool) (base : U → Tape Bool) (pos : U → ℤ) (rpos : T → ℤ) :
    MicrocodeEmbedding.embed b.ports labels (workCfg pc s rpos) (frame base pos)=
      workCfg (labels pc) (b.values s base) (b.values rpos pos) := by
  unfold MicrocodeEmbedding.embed workCfg frame
  simp only [← b.values_eq_extend,b.map_values]

theorem embed_io (b : FinitePortBinding T U) (labels : L → J) (pc : L)
    (s : T → Tape Bool) (base : U → Tape Bool) (pos : U → ℤ) (rpos : T → ℤ)
    (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed b.ports labels (cfg pc s rpos ip outRev) (frame base pos)=
      cfg (labels pc) (b.values s base) (b.values rpos pos) ip outRev := by
  unfold NativeIOEmbedding.embed cfg
  rw [embed_work]

/-- Projecting the caller's absolute heads needs no separate port enumeration. -/
theorem embed_io_project (b : FinitePortBinding T U) (labels : L → J) (pc : L)
    (s : T → Tape Bool) (base : U → Tape Bool) (pos : U → ℤ)
    (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed b.ports labels
      (cfg pc s (fun p => pos (b.ports p)) ip outRev) (frame base pos)=
      cfg (labels pc) (b.values s base) pos ip outRev := by
  rw [embed_io,b.values_project]

end TransposeFollowup.NativeExpanderShearFrames
