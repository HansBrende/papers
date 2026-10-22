import TransposeFollowup.NativeMicrocodeRunCore

/-! Fuse a selected local work-tape read with its chosen action or jump.
The selected label set is fixed. The decision uses only the currently
scanned symbol. Every effective instruction is one original TM transition;
all unselected labels retain their previous transition semantics. -/
namespace TransposeFollowup.NativeReadFusion
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

def instruction (p : Microcode.Program T L) (selected : L → Bool) (heads : T → CopyMachine.Sym Bool)
    (pc : L) : Microcode.Instruction T L :=
  if selected pc then match p pc with
    | .read t next => match p (next (heads t)) with
      | .act acts dest => .act acts dest
      | .jump dest => .jump dest
      | _ => .jump (next (heads t))
    | i => i
  else p pc

def effective (p : Microcode.Program T L) (selected : L → Bool) (heads : T → CopyMachine.Sym Bool) :
    Microcode.Program T L := instruction p selected heads

def step (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L) : NativeMicrocode.Config T L :=
  NativeMicrocode.step (effective p selected (fun t => (c.core.tapes t).head)) c

def Active (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L) : Prop :=
  NativeMicrocode.Active (effective p selected (fun t => (c.core.tapes t).head)) c

abbrev run (p : Microcode.Program T L) (selected : L → Bool) := OperationalTrace.run (step p selected)

def delta (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (s : Fin (q+1)) (input : Option Bool) (scanned : Fin k → Fin 5) :
    Option (Fin (q+1) × Transpose.Dir × (Fin k → Fin 5 × Transpose.Dir) × Option Bool) :=
  NativeMicrocode.delta e (effective p selected (fun t => symbolDecode (scanned (e.port t)))) s input scanned

abbrev machine (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool) : Transpose.TM where
  k:=k;g:=4;q:=q;δ:=delta e p selected

def denote (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (ip : ℤ) (outRev : List Bool) (c : NativeMicrocode.Config T L) : Transpose.Config (machine e p selected) where
  state:=e.label c.core.pc
  inPos:=ip
  work:=fun i z => symbolCode (AbsoluteTape.cells (c.core.tapes (e.port.symm i)) (c.pos (e.port.symm i)) z)
  workPos:=fun i => c.pos (e.port.symm i)
  outRev:=outRev

theorem instruction_unselected (p : Microcode.Program T L) (selected : L → Bool) (heads : T → CopyMachine.Sym Bool)
    (pc : L) (h:selected pc=false) : instruction p selected heads pc=p pc := by simp [instruction,h]

theorem step_unselected (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L)
    (h:selected c.core.pc=false) : step p selected c=NativeMicrocode.step p c := by
  simp [step,NativeMicrocode.step,Microcode.actualStep,effective,instruction,h]

theorem active_iff (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L) :
    Active p selected c ↔ NativeMicrocode.Active p c := by
  unfold Active NativeMicrocode.Active effective instruction
  by_cases hs : selected c.core.pc = true
  · simp only [hs, ite_true]
    cases hp : p c.core.pc with
    | read t next => cases h : p (next ((c.core.tapes t).head)) <;> simp [h]
    | _ => simp
  · simp [hs]


theorem step_read_act (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L)
    (t : T) (next : CopyMachine.Sym Bool → L) (acts : T → Microcode.Action) (dest : L)
    (hs:selected c.core.pc=true) (hp:p c.core.pc=.read t next) (hn:p (next ((c.core.tapes t).head))=.act acts dest) :
    step p selected c=NativeMicrocode.step p (NativeMicrocode.step p c) := by
  simp [step,NativeMicrocode.step,Microcode.actualStep,effective,instruction,hs,hp,hn]

theorem step_read_jump (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L)
    (t : T) (next : CopyMachine.Sym Bool → L) (dest : L)
    (hs:selected c.core.pc=true) (hp:p c.core.pc=.read t next) (hn:p (next ((c.core.tapes t).head))=.jump dest) :
    step p selected c=NativeMicrocode.step p (NativeMicrocode.step p c) := by
  simp [step,NativeMicrocode.step,Microcode.actualStep,effective,instruction,hs,hp,hn]

theorem step_denote_core (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (c : NativeMicrocode.Config T L) :
    NativeMicrocode.totalStep (machine e p selected) w (denote e p selected ip outRev c)=
      denote e p selected ip outRev (step p selected c) := by
  let ep := effective p selected (fun t => (c.core.tapes t).head)
  let lift : Transpose.Config (NativeMicrocode.machine e ep) →
      Transpose.Config (machine e p selected) :=
    fun d => ⟨d.state, d.inPos, d.work, d.workPos, d.outRev⟩
  have hh := congrArg lift (NativeMicrocode.step_denote_core e ep w ip outRev c)
  convert hh using 1
  · simp only [NativeMicrocode.totalStep, Transpose.step, denote,
      NativeMicrocode.Config.denote, machine, NativeMicrocode.machine, delta,
      Equiv.symm_apply_apply, AbsoluteTape.scanned, NativeMicrocode.symbolDecode_code, ep, lift]
    split <;> rfl
  · rfl

theorem step_none_iff (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (c : NativeMicrocode.Config T L) :
    Transpose.step (machine e p selected) w (denote e p selected ip outRev c) = none ↔
      ¬ Active p selected c := by
  cases hp : effective p selected (fun t => (c.core.tapes t).head) c.core.pc <;>
    simp [Transpose.step, denote, machine, delta, NativeMicrocode.delta,
      AbsoluteTape.scanned, hp, Active, NativeMicrocode.Active]

theorem step_some_of_active (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (c : NativeMicrocode.Config T L)
    (ha : Active p selected c) :
    Transpose.step (machine e p selected) w (denote e p selected ip outRev c) =
      some (denote e p selected ip outRev (step p selected c)) := by
  cases hs : Transpose.step (machine e p selected) w (denote e p selected ip outRev c) with
  | none => exact False.elim ((step_none_iff e p selected w ip outRev c).mp hs ha)
  | some d =>
    have hd : d = denote e p selected ip outRev (step p selected c) := by
      simpa [NativeMicrocode.totalStep, hs] using step_denote_core e p selected w ip outRev c
    exact congrArg some hd

theorem run_denote_core (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (n : ℕ) (c : NativeMicrocode.Config T L) :
    OperationalTrace.run (NativeMicrocode.totalStep (machine e p selected) w) n
      (denote e p selected ip outRev c) = denote e p selected ip outRev (run p selected n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simpa only [OperationalTrace.run, step_denote_core] using ih (step p selected c)

theorem trace_stepN (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (step p selected) (Active p selected) n c d) :
    Transpose.stepN (machine e p selected) w n (denote e p selected ip outRev c) =
      some (denote e p selected ip outRev d) := by
  induction h with
  | refl c => rfl
  | cons ha tr ih =>
    rw [Transpose.stepN, step_some_of_active e p selected w ip outRev _ ha]
    exact ih

theorem inactive_fixed (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L)
    (ha : ¬ Active p selected c) : step p selected c = c :=
  NativeMicrocode.inactive_fixed _ c ha

end TransposeFollowup.NativeReadFusion
