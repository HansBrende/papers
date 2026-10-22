import TransposeFollowup.NativeIOCore
import TransposeFollowup.NativeReadFusionCore

/-! Selective fusion for work instructions in the existing input/output
language. Input reads, input moves, and output writes retain their original
one-transition behavior. A read never fuses an IO instruction. -/
namespace TransposeFollowup.NativeIOFusion
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
open NativeIO (Program Config workProgram)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

def delta (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (s : Fin (q+1)) (input : Option Bool) (scanned : Fin k → Fin 5) :
    Option (Fin (q+1) × Transpose.Dir × (Fin k → Fin 5 × Transpose.Dir) × Option Bool) :=
  match p (e.label.symm s) with
  | .work _ => NativeReadFusion.delta e (workProgram p) selected s input scanned
  | _ => NativeIO.delta e p s input scanned

abbrev machine (e : Encoding T L k q) (p : Program T L) (selected : L → Bool) : Transpose.TM where
  k:=k;g:=4;q:=q;δ:=delta e p selected

def denote (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (c : Config T L) : Transpose.Config (machine e p selected) where
  state:=e.label c.work.core.pc
  inPos:=c.inputPos
  work:=fun i z => symbolCode (AbsoluteTape.cells (c.work.core.tapes (e.port.symm i)) (c.work.pos (e.port.symm i)) z)
  workPos:=fun i => c.work.pos (e.port.symm i)
  outRev:=c.outRev

def step (p : Program T L) (selected : L → Bool) (w : List Bool) (c : Config T L) : Config T L :=
  match p c.work.core.pc with
  | .work _ => {c with work:=NativeReadFusion.step (workProgram p) selected c.work}
  | _ => NativeIO.step p w c

def Active (p : Program T L) (selected : L → Bool) (c : Config T L) : Prop :=
  match p c.work.core.pc with
  | .work _ => NativeReadFusion.Active (workProgram p) selected c.work
  | _ => True

abbrev run (p : Program T L) (selected : L → Bool) (w : List Bool) := OperationalTrace.run (step p selected w)

theorem active_iff (p : Program T L) (selected : L → Bool) (c : Config T L) :
    Active p selected c ↔ NativeIO.Active p c := by
  cases hp : p c.work.core.pc with
  | work i => simp only [Active,NativeIO.Active,hp,NativeReadFusion.active_iff,NativeMicrocode.Active,workProgram]
  | _ => simp [Active,NativeIO.Active,hp]

theorem step_unselected (p : Program T L) (selected : L → Bool) (w : List Bool) (c : Config T L)
    (hs : selected c.work.core.pc=false) : step p selected w c=NativeIO.step p w c := by
  cases hp : p c.work.core.pc with
  | work i => simp only [step,NativeIO.step,hp,NativeReadFusion.step_unselected _ _ _ hs]
  | _ => simp only [step,hp]

theorem step_denote_core (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) (c : Config T L) :
    NativeMicrocode.totalStep (machine e p selected) w (denote e p selected c)=
      denote e p selected (step p selected w c) := by
  cases hp : p c.work.core.pc with
  | work i =>
    let lift : Transpose.Config (NativeReadFusion.machine e (workProgram p) selected) →
        Transpose.Config (machine e p selected) :=
      fun d => ⟨d.state, d.inPos, d.work, d.workPos, d.outRev⟩
    have hh := congrArg lift
      (NativeReadFusion.step_denote_core e (workProgram p) selected w c.inputPos c.outRev c.work)
    convert hh using 1
    · simp only [NativeMicrocode.totalStep, Transpose.step, denote,
        NativeReadFusion.denote, machine, NativeReadFusion.machine, delta,
        Equiv.symm_apply_apply, hp, lift]
      split <;> rfl
    · simp only [step, hp, denote, lift, NativeReadFusion.denote]
  | _ =>
    let lift : Transpose.Config (NativeIO.machine e p) →
        Transpose.Config (machine e p selected) :=
      fun d => ⟨d.state, d.inPos, d.work, d.workPos, d.outRev⟩
    have hh := congrArg lift (NativeIO.step_denote_core e p w c)
    convert hh using 1
    · simp only [NativeMicrocode.totalStep, Transpose.step, denote,
        NativeIO.Config.denote, machine, NativeIO.machine, delta,
        Equiv.symm_apply_apply, hp, lift]
      split <;> rfl
    · simp only [step, hp, denote, lift, NativeIO.Config.denote]

theorem step_none_iff (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) (c : Config T L) :
    Transpose.step (machine e p selected) w (denote e p selected c)=none ↔ ¬Active p selected c := by
  cases hp : p c.work.core.pc with
  | work i =>
    cases he : NativeReadFusion.effective (workProgram p) selected (fun t => (c.work.core.tapes t).head) c.work.core.pc <;>
      simp [Transpose.step,denote,machine,delta,NativeReadFusion.delta,NativeMicrocode.delta,
        AbsoluteTape.scanned,hp,he,Active,NativeReadFusion.Active,NativeMicrocode.Active]
  | _ => simp [Transpose.step,denote,machine,delta,NativeIO.delta,hp,Active]

end TransposeFollowup.NativeIOFusion
