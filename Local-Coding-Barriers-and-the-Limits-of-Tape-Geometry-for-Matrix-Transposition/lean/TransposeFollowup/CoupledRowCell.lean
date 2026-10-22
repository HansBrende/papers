import TransposeFollowup.ScheduledWord

/-! Four actual instructions update a pair of cells while scanning left.
The finite truth table retains a parameterized carry and writes arbitrary
work symbols. Boolean carry remains the default for existing clients. -/
namespace TransposeFollowup.CoupledRowCell
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym Tape)
set_option autoImplicit false

abbrev Mode (C : Type := Bool) := C × Sym Bool × Sym Bool
abbrev State (C : Type := Bool) := NativeIO.Config (Fin 2) (Mode C)

variable {C : Type}

def schedule (f : (Mode C) → (Mode C)) : ℕ → NativeIO.Program (Fin 2) (Mode C)
  | 0 => fun m => .work (.act (fun _ => ⟨none,.left⟩) m)
  | 1 => fun m => .work (.read 0 (fun a => (m.1,a,.blank)))
  | 2 => fun m => .work (.read 1 (fun b => f (m.1,m.2.1,b)))
  | _+3 => fun m => .work (.act
      (fun t => ⟨some (if t=0 then m.2.1 else m.2.2),.stay⟩) (m.1,.blank,.blank))

def result (f : (Mode C) → (Mode C)) (c : (State C)) : (State C) :=
  let ts := fun t => (c.work.core.tapes t).move .left
  let m := f (c.work.core.pc.1,(ts 0).head,(ts 1).head)
  ⟨⟨⟨(m.1,.blank,.blank),fun t => (ts t).write (if t=0 then m.2.1 else m.2.2)⟩,
    fun t => c.work.pos t-1⟩,c.inputPos,c.outRev⟩

theorem cell_exact (f : (Mode C) → (Mode C)) (w : List Bool) (c : (State C)) :
    trajectory (schedule f) w c 4=result f c := rfl

theorem cell_active (f : (Mode C) → (Mode C)) (i : ℕ) (c : (State C)) :
    NativeIO.Active (schedule f i) c := by
  cases i with
  | zero => simp [schedule,NativeIO.Active]
  | succ i => cases i with
    | zero => simp [schedule,NativeIO.Active]
    | succ i => cases i <;> simp [schedule,NativeIO.Active]

def cfg (m : (Mode C)) (ts : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ)
    (ip : ℤ) (out : List Bool) : (State C) :=
  ⟨⟨⟨m,fun t => (ts t).denote⟩,pos⟩,ip,out⟩

theorem result_cfg (f : (Mode C) → (Mode C)) (m : (Mode C)) (ts : Fin 2 → Tape Bool)
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) :
    result f (cfg m ts pos ip out)=
      let u := f (m.1,(ts 0).moveLeft.read,(ts 1).moveLeft.read)
      cfg (u.1,.blank,.blank)
        (fun t => (ts t).moveLeft.write (if t=0 then u.2.1 else u.2.2))
        (fun t => pos t-1) ip out := by
  simp only [result,cfg,← CopyMachine.denote_left,CopyMachine.denote_read,
    ← CopyMachine.denote_write]

theorem result_pair (f : (Mode C) → (Mode C)) (m : (Mode C)) (a b : Sym Bool)
    (as bs pa pb : List (Sym Bool)) (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) :
    result f (cfg m ![⟨a::as,pa⟩,⟨b::bs,pb⟩] pos ip out)=
      cfg ((f (m.1,a,b)).1,.blank,.blank)
        ![⟨as,(f (m.1,a,b)).2.1::pa⟩,⟨bs,(f (m.1,a,b)).2.2::pb⟩]
        (fun t => pos t-1) ip out := by
  rw [result_cfg]
  dsimp only [Tape.moveLeft,Tape.read,List.headD_cons]
  congr 2
  funext t
  fin_cases t <;> rfl

theorem cell_positions (f : (Mode C) → (Mode C)) (c : (State C)) (t : Fin 2) :
    (result f c).work.pos t=c.work.pos t-1 := rfl

end TransposeFollowup.CoupledRowCell
