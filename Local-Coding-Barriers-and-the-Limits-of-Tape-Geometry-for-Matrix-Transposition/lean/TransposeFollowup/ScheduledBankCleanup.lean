import TransposeFollowup.ScheduledTapeAction
import TransposeFollowup.ScheduledSegments

/-! Shared cleanup for a bank at its end and a retained buffer at its start.
All three passes are existing paid native actions. -/
namespace TransposeFollowup.ScheduledBankCleanup
open FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
set_option autoImplicit false
variable {M : Type*}

def ticks (P W : ℕ) : ℕ := W+(W+P)

def schedule (_P W : ℕ) : ℕ → NativeIO.Program (Fin 2) M :=
  append (fun _ => action 1 ⟨some .blank,.right⟩)
    (append (fun _ => action 1 ⟨none,.left⟩)
      (fun _ => action 0 ⟨none,.left⟩) W) W

def run (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :=
  rewind 0 w (rewind 1 w (erase 1 w c W) W) P

theorem schedule_active (P W i : ℕ) (c : NativeIO.Config (Fin 2) M) :
    NativeIO.Active (schedule P W i) c := by
  apply append_active
  · intro _; exact active _ _ _
  · intro _; apply append_active <;> intro _ <;> exact active _ _ _

theorem schedule_exact (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    trajectory (schedule P W) w c (ticks P W)=run P W w c := by
  simp only [schedule,ticks,append_exact,run,erase,rewind]

theorem run_position (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    (run P W w c).work.pos t=c.work.pos t-if t=0 then P else 0 := by
  simp only [run,rewind_position,erase_position,add_sub_cancel_right]

theorem run_cells (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (t : Fin 2) (z : ℤ) :
    cells (run P W w c) t z=
      if t=1 ∧ c.work.pos 1≤z ∧ z<c.work.pos 1+W then .blank else cells c t z := by
  simp only [run,rewind_cells,erase_cells]
  by_cases h : t=1
  · subst t; rfl
  · simp [h]

theorem run_io (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M) :
    (run P W w c).inputPos=c.inputPos ∧ (run P W w c).outRev=c.outRev := by
  simp only [run,rewind_io,erase_io,and_self]

theorem run_clean (P W : ℕ) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (hc : ∀ z, ¬(c.work.pos 1≤z ∧ z<c.work.pos 1+W) → cells c 1 z=.blank) :
    ∀ z, cells (run P W w c) 1 z=.blank := by
  intro z
  rw [run_cells]
  by_cases h : c.work.pos 1≤z ∧ z<c.work.pos 1+W <;> simp [h,hc z]

end TransposeFollowup.ScheduledBankCleanup
