import TransposeFollowup.NativeMicrocodeRunCore

/-! Add physical access to the original read-only input and write-only
output. Existing work-tape microcode remains reusable without changing its
instructions or paying an unbounded oracle. Every new instruction is one
original TM transition. -/
namespace TransposeFollowup.NativeIO
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

inductive Instruction (T L : Type*)
  | work (i : Microcode.Instruction T L)
  | readInput (next : Option Bool → L)
  | moveInput (dir : Transpose.Dir) (next : L)
  | output (bit : Bool) (next : L)

abbrev Program (T L : Type*) := L → Instruction T L

def workProgram (p : Program T L) : Microcode.Program T L :=
  fun pc => match p pc with | .work i => i | _ => .reject

def delta (e : Encoding T L k q) (p : Program T L)
    (s : Fin (q+1)) (input : Option Bool) (scanned : Fin k → Fin 5) :
    Option (Fin (q+1) × Transpose.Dir × (Fin k → Fin 5 × Transpose.Dir) × Option Bool) :=
  match p (e.label.symm s) with
  | .work _ => NativeMicrocode.delta e (workProgram p) s input scanned
  | .readInput next => some (e.label (next input),.stay,fun i => (scanned i,.stay),none)
  | .moveInput dir next => some (e.label next,dir,fun i => (scanned i,.stay),none)
  | .output bit next => some (e.label next,.stay,fun i => (scanned i,.stay),some bit)

abbrev machine (e : Encoding T L k q) (p : Program T L) : Transpose.TM where
  k:=k; g:=4; q:=q; δ:=delta e p

structure Config (T L : Type*) where
  work : NativeMicrocode.Config T L
  inputPos : ℤ
  outRev : List Bool

def Config.denote (e : Encoding T L k q) (p : Program T L) (c : Config T L) : Transpose.Config (machine e p) where
  state:=e.label c.work.core.pc
  inPos:=c.inputPos
  work:=fun i z => symbolCode (AbsoluteTape.cells (c.work.core.tapes (e.port.symm i))
    (c.work.pos (e.port.symm i)) z)
  workPos:=fun i => c.work.pos (e.port.symm i)
  outRev:=c.outRev

def setLabel (c : Config T L) (next : L) : Config T L :=
  {c with work:={c.work with core:={c.work.core with pc:=next}}}

def step (p : Program T L) (w : List Bool) (c : Config T L) : Config T L :=
  match p c.work.core.pc with
  | .work _ => {c with work:=NativeMicrocode.step (workProgram p) c.work}
  | .readInput next => setLabel c (next (Transpose.readInput w c.inputPos))
  | .moveInput dir next => {setLabel c next with inputPos:=dir.shift c.inputPos}
  | .output bit next => {setLabel c next with outRev:=bit::c.outRev}

def Active (p : Program T L) (c : Config T L) : Prop :=
  match p c.work.core.pc with | .work i => i≠.halt ∧ i≠.reject | _ => True

/-- The same one-step jump rule includes unchanged input and output state. -/
theorem jump_trace (p : Program T L) (w : List Bool) (c : Config T L) (next : L)
    (h : p c.work.core.pc = .work (.jump next)) :
    OperationalTrace.Trace (step p w) (Active p) 1 c (setLabel c next) := by
  apply OperationalTrace.Trace.cons
  · simp [Active, h]
  · have hs : step p w c = setLabel c next := by
      simp [step, workProgram, NativeMicrocode.step, Microcode.actualStep, setLabel, h]
    rw [hs]
    exact .refl _

theorem step_none_iff (e : Encoding T L k q) (p : Program T L) (w : List Bool) (c : Config T L) :
    Transpose.step (machine e p) w (c.denote e p)=none ↔ ¬Active p c := by
  cases hp : p c.work.core.pc with
  | work i => cases i <;> simp [Transpose.step,Config.denote,machine,delta,NativeMicrocode.delta,workProgram,hp,Active]
  | _ => simp [Transpose.step,Config.denote,machine,delta,hp,Active]

theorem step_denote_core (e : Encoding T L k q) (p : Program T L) (w : List Bool) (c : Config T L) :
    NativeMicrocode.totalStep (machine e p) w (c.denote e p)=(step p w c).denote e p := by
  cases hp : p c.work.core.pc with
  | work i =>
    let lift : Transpose.Config (NativeMicrocode.machine e (workProgram p)) →
        Transpose.Config (machine e p) :=
      fun d => ⟨d.state, d.inPos, d.work, d.workPos, d.outRev⟩
    have hh := congrArg lift
      (NativeMicrocode.step_denote_core e (workProgram p) w c.inputPos c.outRev c.work)
    convert hh using 1
    · simp only [NativeMicrocode.totalStep, Transpose.step, Config.denote,
        NativeMicrocode.Config.denote, machine, NativeMicrocode.machine, delta,
        Equiv.symm_apply_apply, hp, lift]
      split <;> rfl
    · simp only [step, hp, Config.denote, lift, NativeMicrocode.Config.denote]
  | _ =>
    simp only [NativeMicrocode.totalStep,Transpose.step,Config.denote,machine,delta,
      Equiv.symm_apply_apply,hp,AbsoluteTape.scanned,Option.getD_some,step,setLabel,Transpose.Dir.shift]
    congr 1
    funext i z
    split_ifs with hz
    · subst z; simp [AbsoluteTape.scanned]
    · simp [hz]

theorem step_some_of_active (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (c : Config T L) (ha : Active p c) :
    Transpose.step (machine e p) w (c.denote e p)=some ((step p w c).denote e p) := by
  cases hs : Transpose.step (machine e p) w (c.denote e p) with
  | none => exact False.elim ((step_none_iff e p w c).mp hs ha)
  | some d =>
    have hd : d=(step p w c).denote e p := by
      simpa [NativeMicrocode.totalStep,hs] using step_denote_core e p w c
    exact congrArg some hd

theorem trace_stepN (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    {n : ℕ} {c d : Config T L} (h : OperationalTrace.Trace (step p w) (Active p) n c d) :
    Transpose.stepN (machine e p) w n (c.denote e p)=some (d.denote e p) := by
  induction h with
  | refl c => rfl
  | cons ha tr ih => rw [Transpose.stepN,step_some_of_active e p w _ ha]; exact ih

theorem work_step (p : Program T L) (w : List Bool) (c : NativeMicrocode.Config T L)
    (ha : NativeMicrocode.Active (workProgram p) c) (inputPos : ℤ) (outRev : List Bool) :
    step p w ⟨c,inputPos,outRev⟩=⟨NativeMicrocode.step (workProgram p) c,inputPos,outRev⟩ ∧
      Active p ⟨c,inputPos,outRev⟩ := by
  cases hp : p c.core.pc with
  | work i => exact ⟨by simp [step,hp],by simpa only [Active,hp,NativeMicrocode.Active,workProgram] using ha⟩
  | _ => simp [NativeMicrocode.Active,workProgram,hp] at ha

theorem lift_work_trace (p : Program T L) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeMicrocode.step (workProgram p)) (NativeMicrocode.Active (workProgram p)) n c d) :
    OperationalTrace.Trace (step p w) (Active p) n ⟨c,inputPos,outRev⟩ ⟨d,inputPos,outRev⟩ := by
  induction h with
  | refl c => exact .refl _
  | cons ha tr ih =>
    apply OperationalTrace.Trace.cons (work_step p w _ ha inputPos outRev).2
    rw [(work_step p w _ ha inputPos outRev).1]
    exact ih

theorem blank_denote (e : Encoding T L k q) (p : Program T L) (start : L) (hs : e.label start=0) :
    (⟨NativeMicrocode.blankConfig start,0,[]⟩ : Config T L).denote e p=Transpose.init (machine e p) := by
  unfold Config.denote NativeMicrocode.blankConfig Transpose.init
  rw [hs]
  congr 1
  funext i z
  rw [AbsoluteTape.blank_cells]
  rfl

end TransposeFollowup.NativeIO
