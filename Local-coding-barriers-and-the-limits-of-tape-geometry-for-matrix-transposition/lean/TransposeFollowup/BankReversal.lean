import TransposeFollowup.ScheduledTransfer
import TransposeFollowup.MaskedStrideCell
import TransposeFollowup.ScheduledMotion

/-! Reversing a raw bit bank by two paid transfers. The scratch bank is
read backwards and erased during the return transfer. Both work heads
return to their original coordinates, so the operation composes with
other internal-bank stages. -/
namespace TransposeFollowup.BankReversal
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

abbrev read (a : CopyMachine.Sym Bool) : Mode := (bit a,false)
abbrev write (m : Mode) : CopyMachine.Sym Bool := .data m.1

def prepared (P : ℕ) (w : List Bool) (c : State) : State :=
  NativeIO.step (action 1 ⟨none,.left⟩) w
    (rewind 0 w (ScheduledTransfer.copied false false false read write (false,false) c P) P)

def returned (P : ℕ) (w : List Bool) (c : State) : State :=
  ScheduledTransfer.copied true true true read write (false,false) (prepared P w c) P

def result (P : ℕ) (w : List Bool) (c : State) : State :=
  NativeIO.step (action 1 ⟨none,.right⟩) w (rewind 0 w (returned P w c) P)

def ticks (P : ℕ) : ℕ := 2*P+(P+(1+(2*P+(P+1))))

def schedule (P : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append (ScheduledTransfer.schedule false false false read write (false,false))
    (append (fun _ => action 0 ⟨none,.left⟩)
      (append (fun _ => action 1 ⟨none,.left⟩)
        (append (ScheduledTransfer.schedule true true true read write (false,false))
          (append (fun _ => action 0 ⟨none,.left⟩) (fun _ => action 1 ⟨none,.right⟩) P)
          (2*P)) 1) P) (2*P)

theorem ticks_eq (P : ℕ) : ticks P=6*P+2 := by unfold ticks; omega

theorem schedule_active (P i : ℕ) (c : State) : NativeIO.Active (schedule P i) c := by
  unfold schedule
  apply append_active
  · intro _; exact ScheduledTransfer.schedule_active _ _ _ _ _ _ _ _
  · intro _
    apply append_active
    · intro _; exact ScheduledTapeAction.active _ _ _
    · intro _
      apply append_active
      · intro _; exact ScheduledTapeAction.active _ _ _
      · intro _
        apply append_active
        · intro _; exact ScheduledTransfer.schedule_active _ _ _ _ _ _ _ _
        · intro _
          apply append_active <;> intro _ <;> exact ScheduledTapeAction.active _ _ _

theorem schedule_exact (P : ℕ) (w : List Bool) (c : State) :
    trajectory (schedule P) w c (ticks P)=result P w c := by
  simp only [schedule,ticks,append_exact,ScheduledTransfer.schedule_exact]
  rfl

theorem prepared_positions (P : ℕ) (w : List Bool) (c : State) :
    (prepared P w c).work.pos 0=c.work.pos 0 ∧
    (prepared P w c).work.pos 1=c.work.pos 1+P-1 := by
  have h := ScheduledTransfer.copied_positions false false false read write (false,false) c P
  simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,
    Bool.false_eq_true,ite_false] at h
  simp [prepared,step_position,rewind_position,h.1,h.2,NativeMicrocode.direction,Transpose.Dir.shift]

theorem prepared_cells (P : ℕ) (w : List Bool) (c : State) (t : Fin 2) (z : ℤ) :
    cells (prepared P w c) t z=
      cells (ScheduledTransfer.copied false false false read write (false,false) c P) t z := by
  simp only [prepared,step_cells,Option.getD_none,ite_self,rewind_cells]

theorem result_cells (P : ℕ) (w : List Bool) (c : State) (t : Fin 2) (z : ℤ) :
    cells (result P w c) t z=cells (returned P w c) t z := by
  simp only [result,step_cells,Option.getD_none,ite_self,rewind_cells]

theorem result_bank_outside (P : ℕ) (w : List Bool) (c : State) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+P≤z) :
    cells (result P w c) 0 z=cells c 0 z := by
  rw [result_cells]
  have h := ScheduledTransfer.copied_target_outside true true true read write (false,false)
    (prepared P w c) P z (by simpa only [ScheduledTransfer.target,ite_true,(prepared_positions P w c).1] using hz)
  change cells (returned P w c) 0 z=cells (prepared P w c) 0 z at h
  rw [h,prepared_cells]
  exact ScheduledTransfer.copied_source_preserved false false read write (false,false) c P z

/-- Every output bit comes from the reflected input position. This also
asserts the complete scratch and head interface needed by the next stage. -/
theorem result_spec (P : ℕ) (w : List Bool) (c : State)
    (hblank : ∀ z, cells c 1 z=.blank) :
    (∀ t, (result P w c).work.pos t=c.work.pos t) ∧
    (∀ j<P, cells (result P w c) 0 (c.work.pos 0+j)=
      .data (bit (cells c 0 (c.work.pos 0+(P-1-j : ℕ))))) ∧
    (∀ z, cells (result P w c) 1 z=.blank) ∧
    (result P w c).inputPos=c.inputPos ∧ (result P w c).outRev=c.outRev := by
  have hp := prepared_positions P w c
  have hr := ScheduledTransfer.copied_positions true true true read write (false,false) (prepared P w c) P
  simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,ite_true] at hr
  have hret : (returned P w c).work.pos 0=c.work.pos 0+P ∧
      (returned P w c).work.pos 1=c.work.pos 1-1 := by
    constructor
    · exact hr.2.trans (congrArg (fun p : ℤ => p+P) hp.1)
    · change (ScheduledTransfer.copied true true true read write (false,false) (prepared P w c) P).work.pos 1=_
      rw [hr.1,hp.2]; omega
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    fin_cases t <;>
      simp [result,step_position,rewind_position,hret.1,hret.2,NativeMicrocode.direction,Transpose.Dir.shift]
  · intro j hj
    rw [result_cells]
    have h := ScheduledTransfer.copied_target true true true read write (false,false) (prepared P w c) P j hj
    simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,ite_true,hp.1,hp.2] at h
    change cells (returned P w c) 0 (c.work.pos 0+j)=_ at h
    rw [h,prepared_cells]
    have he : c.work.pos 1+P-1+(-(j : ℤ))=c.work.pos 1+(P-1-j : ℕ) := by omega
    rw [he]
    have hc := ScheduledTransfer.copied_target false false false read write (false,false) c P (P-1-j) (by omega)
    simp only [ScheduledTransfer.source,ScheduledTransfer.target,ScheduledTransfer.offset,
      Bool.false_eq_true,ite_false] at hc
    rw [hc]
    rfl
  · intro z
    rw [result_cells]
    by_cases hz : c.work.pos 1≤z ∧ z<c.work.pos 1+P
    · let j := (c.work.pos 1+P-1-z).toNat
      have hj : j<P := by dsimp [j]; omega
      have he : (prepared P w c).work.pos 1+ScheduledTransfer.offset true j=z := by
        rw [hp.2]; simp only [ScheduledTransfer.offset,ite_true]; dsimp [j]; omega
      have h := ScheduledTransfer.copied_source_cleared true true read write (false,false) (prepared P w c) P j hj
      simpa only [returned,ScheduledTransfer.source,ite_true,he] using h
    · have h := ScheduledTransfer.copied_source_away true true true read write (false,false)
        (prepared P w c) P z (by
          intro j hj
          simp only [ScheduledTransfer.source,ScheduledTransfer.offset,ite_true,hp.2]
          omega)
      change cells (returned P w c) 1 z=cells (prepared P w c) 1 z at h
      rw [h,prepared_cells]
      have hc := ScheduledTransfer.copied_target_outside false false false read write (false,false) c P z (by
        simp only [ScheduledTransfer.target,Bool.false_eq_true,ite_false]; omega)
      exact hc.trans (hblank z)
  · have ha := ScheduledTransfer.copied_io false false false read write (false,false) c P
    have hb := rewind_io 0 w (ScheduledTransfer.copied false false false read write (false,false) c P) P
    have hc := step_io 1 ⟨none,.left⟩ w
      (rewind 0 w (ScheduledTransfer.copied false false false read write (false,false) c P) P)
    have hd := ScheduledTransfer.copied_io true true true read write (false,false) (prepared P w c) P
    have he := rewind_io 0 w (returned P w c) P
    have hf := step_io 1 ⟨none,.right⟩ w (rewind 0 w (returned P w c) P)
    exact ⟨hf.1.trans (he.1.trans (hd.1.trans (hc.1.trans (hb.1.trans ha.1)))),
      hf.2.trans (he.2.trans (hd.2.trans (hc.2.trans (hb.2.trans ha.2))))⟩

end TransposeFollowup.BankReversal
