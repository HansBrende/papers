import BitWord.NativeLoggedRun
import TransposeFollowup.NativeIOEmbedding

/-! Paid initialization of the finite history tracks. Source tapes are framed
unchanged; the two setup transitions create the literal history sentinel. -/
namespace BitWord.NativeLoggedInit
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

abbrev Port := NativeLogged.Port T L
abbrev Label := Option (Option (NativeLogged.Label T L))

def label (pc : NativeLogged.Label T L) : Label (T := T) (L := L) := some (some pc)

def markActions : Port (T := T) (L := L) → Microcode.Action
  | .data _ => NativeLogged.idle
  | .log _ => ⟨some .start,.right⟩

noncomputable def program (p : Microcode.Program T L) (keep : T → Bool) (initial : L) :
    Microcode.Program (Port (T := T) (L := L)) (Label (T := T) (L := L))
  | none => .act NativeLogged.backActions (some none)
  | some none => .act markActions (label (NativeLogged.start initial))
  | some (some pc) => MicrocodeEmbedding.instruction (Function.Embedding.refl _) label
      (NativeLogged.program p keep initial pc)

def mapConfig (c : NativeLogged.LoggedConfig (T := T) (L := L)) :
    NativeMicrocode.Config (Port (T := T) (L := L)) (Label (T := T) (L := L)) :=
  ⟨⟨label c.core.pc,c.core.tapes⟩,c.pos⟩

def initialConfig (c : NativeLogged.SourceConfig (T := T) (L := L)) :
    NativeMicrocode.Config (Port (T := T) (L := L)) (Label (T := T) (L := L)) :=
  ⟨⟨none,fun z => match z with
      | .data t => c.core.tapes t | .log _ => Turing.Tape.mk₂ [] []⟩,
    fun z => match z with | .data t => c.pos t | .log _ => 0⟩

abbrev Trace (p : Microcode.Program T L) (keep : T → Bool) (initial : L) :=
  OperationalTrace.Trace (NativeMicrocode.step (program p keep initial))
    (NativeMicrocode.Active (program p keep initial))

theorem initialize_trace (p : Microcode.Program T L) (keep : T → Bool)
    (c : NativeLogged.SourceConfig (T := T) (L := L)) :
    Trace p keep c.core.pc 2 (initialConfig c) (mapConfig (NativeLogged.forward c [])) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,initialConfig,program]
  · apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,NativeMicrocode.step,Microcode.actualStep,initialConfig,program]
    · have he : NativeMicrocode.step (program p keep c.core.pc)
          (NativeMicrocode.step (program p keep c.core.pc) (initialConfig c)) =
          mapConfig (NativeLogged.forward c []) := by
        simp only [NativeMicrocode.step,Microcode.actualStep,initialConfig,program]
        congr 1
        · congr 1
          funext z; cases z <;>
            simp [NativeLogged.backActions,markActions,NativeLogged.idle,Microcode.Action.actual,
              mapConfig,NativeLogged.forward,NativeLogged.loaded,NativeLogged.bank,
              NativeLogged.logSymbols,Turing.Tape.mk₂,Turing.Tape.write_mk']
        · funext z; cases z <;>
            simp [NativeLogged.backActions,markActions,NativeLogged.idle,NativeMicrocode.direction,
              Transpose.Dir.shift,mapConfig,NativeLogged.forward,NativeLogged.loaded,NativeLogged.positions]
      rw [he]; exact .refl _

theorem map_trace (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    {n c d} (h : NativeLogged.Trace p keep initial n c d) :
    Trace p keep initial n (mapConfig c) (mapConfig d) := by
  have hh := MicrocodeEmbedding.trace_embed (Function.Embedding.refl (Port (T := T) (L := L)))
    label (NativeLogged.program p keep initial) (program p keep initial)
    (⟨c.core.tapes,c.pos⟩ : MicrocodeEmbedding.Frame _) (by intro pc _ _; rfl) h
  have he (x : NativeLogged.LoggedConfig (T := T) (L := L)) :
      MicrocodeEmbedding.embed (Function.Embedding.refl (Port (T := T) (L := L))) label x
        (⟨c.core.tapes,c.pos⟩ : MicrocodeEmbedding.Frame _)=mapConfig x := by
    unfold MicrocodeEmbedding.embed mapConfig
    congr 2 <;> funext t <;> exact MicrocodeEmbedding.extend_at (Function.Embedding.refl _) t _ _
  simpa only [he] using hh

end BitWord.NativeLoggedInit
