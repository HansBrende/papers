import TransposeFollowup.ScheduledTapeAction

/-! A paid two-instruction transfer between distinct work tapes. The
source can move in either direction and may be cleared after reading.
The finite local mode and symbol codec are parameters, so the same cell
supports binary and later finite-alphabet bank operations. -/
namespace TransposeFollowup.ScheduledTransfer
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}

def source (fromScratch : Bool) : Fin 2 := if fromScratch then 1 else 0
def target (fromScratch : Bool) : Fin 2 := if fromScratch then 0 else 1
def offset (left : Bool) (n : ℕ) : ℤ := if left then -(n : ℤ) else n

theorem offset_succ (left : Bool) (n : ℕ) : offset left (n+1) = offset left n+offset left 1 := by
  cases left <;> simp [offset,add_comm]

theorem offset_injective (left : Bool) : Function.Injective (offset left) := by
  intro a b h
  cases left <;> simp only [offset,Bool.false_eq_true,ite_false,ite_true,neg_inj,Int.natCast_inj] at h <;> exact h

def actions (fromScratch clear left : Bool) (a : Sym Bool) (t : Fin 2) : Microcode.Action :=
  if t=source fromScratch then ⟨if clear then some .blank else none,if left then .left else .right⟩
  else ⟨some a,.right⟩

def cellSchedule (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M) :
    ℕ → NativeIO.Program (Fin 2) M
  | 0 => fun _ => .work (.read (source fromScratch) read)
  | _+1 => fun m => .work (.act (actions fromScratch clear left (write m)) reset)

def cellResult (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (c : NativeIO.Config (Fin 2) M) : NativeIO.Config (Fin 2) M :=
  let acts := actions fromScratch clear left (write (read (c.work.core.tapes (source fromScratch)).head))
  ⟨⟨⟨reset,fun t => (acts t).actual (c.work.core.tapes t)⟩,
    fun t => (NativeMicrocode.direction (acts t).move).shift (c.work.pos t)⟩,c.inputPos,c.outRev⟩

theorem cell_exact (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (cellSchedule fromScratch clear left read write reset) w c 2 =
      cellResult fromScratch clear left read write reset c := rfl

theorem cell_active (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (n : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (cellSchedule fromScratch clear left read write reset n) c := by
  cases n <;> simp [cellSchedule,NativeIO.Active]

theorem cell_positions (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (c : NativeIO.Config (Fin 2) M) :
    (cellResult fromScratch clear left read write reset c).work.pos (source fromScratch) =
      c.work.pos (source fromScratch)+offset left 1 ∧
    (cellResult fromScratch clear left read write reset c).work.pos (target fromScratch) =
      c.work.pos (target fromScratch)+1 := by
  cases fromScratch <;> cases left <;>
    simp [cellResult,actions,source,target,offset,NativeMicrocode.direction,Transpose.Dir.shift]
  all_goals omega

theorem cell_cells (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (c : NativeIO.Config (Fin 2) M) (t : Fin 2) (z : ℤ) :
    cells (cellResult fromScratch clear left read write reset c) t z =
      if z=c.work.pos t then
        (actions fromScratch clear left (write (read (cells c (source fromScratch) (c.work.pos (source fromScratch))))) t).write.getD
          (cells c t z)
      else cells c t z := by
  have he := NativeMicrocode.action_cells
      (actions fromScratch clear left (write (read (c.work.core.tapes (source fromScratch)).head)) t)
      (c.work.core.tapes t) (c.work.pos t) z
  apply he.trans
  by_cases hz : z=c.work.pos t <;> simp [hz,cells,AbsoluteTape.scanned]

theorem cell_source (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (c : NativeIO.Config (Fin 2) M) (z : ℤ) :
    cells (cellResult fromScratch clear left read write reset c) (source fromScratch) z =
      if clear=true ∧ z=c.work.pos (source fromScratch) then .blank else cells c (source fromScratch) z := by
  rw [cell_cells]
  by_cases hz : z=c.work.pos (source fromScratch) <;>
    cases clear <;> simp [actions,hz]

theorem cell_target (fromScratch clear left : Bool) (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (c : NativeIO.Config (Fin 2) M) (z : ℤ) :
    cells (cellResult fromScratch clear left read write reset c) (target fromScratch) z =
      if z=c.work.pos (target fromScratch) then
        write (read (cells c (source fromScratch) (c.work.pos (source fromScratch))))
      else cells c (target fromScratch) z := by
  rw [cell_cells]
  cases fromScratch <;> simp [actions,source,target]

end TransposeFollowup.ScheduledTransfer
