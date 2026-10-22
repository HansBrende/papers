import TransposeFollowup.NativeIOCore
import TransposeFollowup.NativeZipper

/-! An executable zipper interpreter for the same input/output instructions.
It refines the native I/O semantics, including every input-head movement and
output bit. Tests use this interpreter, not a separate algorithm. -/
namespace TransposeFollowup.NativeIOZipper
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

structure Config (T L : Type*) where
  work : NativeZipper.Config T L
  inputPos : ℤ
  outRev : List Bool

def Config.denote (c : Config T L) : NativeIO.Config T L := ⟨c.work.denote,c.inputPos,c.outRev⟩

def setLabel (c : Config T L) (next : L) : Config T L :=
  {c with work:={c.work with core:={c.work.core with pc:=next}}}

def step (p : NativeIO.Program T L) (w : List Bool) (c : Config T L) : Config T L :=
  match p c.work.core.pc with
  | .work _ => {c with work:=NativeZipper.step (NativeIO.workProgram p) c.work}
  | .readInput next => setLabel c (next (Transpose.readInput w c.inputPos))
  | .moveInput dir next => {setLabel c next with inputPos:=dir.shift c.inputPos}
  | .output bit next => {setLabel c next with outRev:=bit::c.outRev}

theorem step_denote (p : NativeIO.Program T L) (w : List Bool) (c : Config T L) :
    (step p w c).denote=NativeIO.step p w c.denote := by
  cases hp : p c.work.core.pc with
  | work i =>
    simp only [step,hp,Config.denote,NativeIO.step,NativeZipper.Config.denote,Microcode.Config.denote]
    exact congrArg (fun s => (⟨s,c.inputPos,c.outRev⟩ : NativeIO.Config T L)) (NativeZipper.step_denote _ _)
  | _ => simp [step,Config.denote,NativeIO.step,NativeZipper.Config.denote,Microcode.Config.denote,
      hp,setLabel,NativeIO.setLabel]

abbrev run (p : NativeIO.Program T L) (w : List Bool) := OperationalTrace.run (step p w)

theorem run_denote (p : NativeIO.Program T L) (w : List Bool) (n : ℕ) (c : Config T L) :
    (run p w n c).denote=OperationalTrace.run (NativeIO.step p w) n c.denote := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simpa only [run,OperationalTrace.run,step_denote] using ih (step p w c)

theorem inactive_fixed (p : NativeIO.Program T L) (w : List Bool) (c : NativeIO.Config T L)
    (ha : ¬NativeIO.Active p c) : NativeIO.step p w c=c := by
  cases hp : p c.work.core.pc with
  | work i =>
    have hn : ¬NativeMicrocode.Active (NativeIO.workProgram p) c.work := by
      simpa [NativeMicrocode.Active,NativeIO.workProgram,NativeIO.Active,hp] using ha
    simp only [NativeIO.step,hp,NativeMicrocode.inactive_fixed _ _ hn]
  | _ => simp [NativeIO.Active,hp] at ha

theorem trace_of_run (p : NativeIO.Program T L) (w : List Bool) {n : ℕ} {c d : Config T L}
    (h : run p w n c=d) : ∃ t ≤ n,
    OperationalTrace.Trace (NativeIO.step p w) (NativeIO.Active p) t c.denote d.denote := by
  have hr : OperationalTrace.run (NativeIO.step p w) n c.denote=d.denote := by rw [← run_denote,h]
  obtain ⟨t,ht,htr⟩ := OperationalTrace.prune (NativeIO.step p w) (NativeIO.Active p) (inactive_fixed p w) n c.denote
  rw [hr] at htr
  exact ⟨t,ht,htr⟩

end TransposeFollowup.NativeIOZipper
