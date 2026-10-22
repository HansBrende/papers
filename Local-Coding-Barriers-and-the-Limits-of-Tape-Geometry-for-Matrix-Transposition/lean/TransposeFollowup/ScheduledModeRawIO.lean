import TransposeFollowup.NativeIOModeProduct
import TransposeFollowup.ScheduledRawIOMotion
import TransposeFollowup.RawMaskedStrideCorrectness

/-! The existing raw loader and emitter inside any product controller.
All data, IO and intermediate head-position statements are transported
from the original routines. The auxiliary mode is preserved throughout. -/
namespace TransposeFollowup.ScheduledModeRawIO
open FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction NativeIOModeProduct
open MaskedStrideCell (Mode bit)
set_option autoImplicit false
variable {F J : Type*}

noncomputable def inputSchedule (e : J ≃ Mode × F) (i : ℕ) :=
  NativeIOModeProduct.program e (ScheduledRawInput.schedule i)

noncomputable def outputSchedule (e : J ≃ Mode × F) (i : ℕ) :=
  NativeIOModeProduct.program e (ScheduledRawOutput.schedule i)

def loaded (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J) (n : ℕ) :=
  attach e (e c.work.core.pc).2 (ScheduledRawInput.loaded w (project e c) n)

def emitted (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J) (n : ℕ) :=
  attach e (e c.work.core.pc).2 (ScheduledRawOutput.emitted w (project e c) n)

theorem input_active (e : J ≃ Mode × F) (i : ℕ) (c : NativeIO.Config (Fin 2) J) :
    NativeIO.Active (inputSchedule e i) c :=
  NativeIOModeProduct.active e _ (ScheduledRawInput.cell_active _) c

theorem output_active (e : J ≃ Mode × F) (i : ℕ) (c : NativeIO.Config (Fin 2) J) :
    NativeIO.Active (outputSchedule e i) c :=
  NativeIOModeProduct.active e _ (ScheduledRawOutput.cell_active _) c

theorem input_exact (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J) (n : ℕ) :
    trajectory (inputSchedule e) w c (3*n)=loaded e w c n := by
  unfold inputSchedule
  rw [trajectory_eq,ScheduledRawInput.schedule_exact]
  rfl

theorem output_exact (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J) (n : ℕ) :
    trajectory (outputSchedule e) w c (3*n)=emitted e w c n := by
  unfold outputSchedule
  rw [trajectory_eq,ScheduledRawOutput.schedule_exact]
  rfl

theorem loaded_spec (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J) (n : ℕ) :
    (∀ t, (loaded e w c n).work.pos t=c.work.pos t+if t=0 then n else 0) ∧
    (∀ j < n, cells (loaded e w c n) 0 (c.work.pos 0+j)=
      .data (ScheduledRawInput.inputBit w (c.inputPos+j))) ∧
    (∀ t z, t≠0 ∨ z<c.work.pos t ∨ c.work.pos t+n ≤ z →
      cells (loaded e w c n) t z=cells c t z) ∧
    (loaded e w c n).inputPos=c.inputPos+n ∧ (loaded e w c n).outRev=c.outRev ∧
    (e (loaded e w c n).work.core.pc).2=(e c.work.core.pc).2 := by
  refine ⟨ScheduledRawInput.loaded_position w (project e c) n,
    ScheduledRawInput.loaded_written w (project e c) n,
    ScheduledRawInput.loaded_outside w (project e c) n,
    (ScheduledRawInput.loaded_io w (project e c) n).1,
    (ScheduledRawInput.loaded_io w (project e c) n).2,?_⟩
  simp only [loaded,attach,Equiv.apply_symm_apply]

theorem emitted_spec (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J) (n : ℕ) :
    (∀ t, (emitted e w c n).work.pos t=c.work.pos t+if t=0 then n else 0) ∧
    (∀ t z, cells (emitted e w c n) t z=cells c t z) ∧
    (emitted e w c n).inputPos=c.inputPos ∧
    (emitted e w c n).outRev=
      ((List.range n).map (fun j : ℕ => bit (cells c 0 (c.work.pos 0+j)))).reverse++c.outRev ∧
    (e (emitted e w c n).work.core.pc).2=(e c.work.core.pc).2 := by
  refine ⟨ScheduledRawOutput.emitted_position w (project e c) n,
    ScheduledRawOutput.emitted_cells w (project e c) n,
    ScheduledRawOutput.emitted_input w (project e c) n,
    ScheduledRawOutput.emitted_output w (project e c) n,?_⟩
  simp only [emitted,attach,Equiv.apply_symm_apply]

theorem input_position (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J)
    (n : ℕ) (t : Fin 2) :
    (trajectory (inputSchedule e) w c n).work.pos t=c.work.pos t+if t=0 then (n+1)/3 else 0 := by
  unfold inputSchedule
  rw [trajectory_eq]
  exact ScheduledRawInput.schedule_position w (project e c) n t

theorem output_position (e : J ≃ Mode × F) (w : List Bool) (c : NativeIO.Config (Fin 2) J)
    (n : ℕ) (t : Fin 2) :
    (trajectory (outputSchedule e) w c n).work.pos t=c.work.pos t+if t=0 then n/3 else 0 := by
  unfold outputSchedule
  rw [trajectory_eq]
  exact ScheduledRawOutput.schedule_position w (project e c) n t

def initial (e : J ≃ Mode × F) (f : F) := attach e f RawMaskedStride.initial

def prepared (e : J ≃ Mode × F) (f : F) (P : ℕ) (w : List Bool) :=
  attach e f (RawMaskedStride.prepared P w)

noncomputable def prepareSchedule (e : J ≃ Mode × F) (P i : ℕ) :=
  NativeIOModeProduct.program e
    (append ScheduledRawInput.schedule (fun _ => action 0 ⟨none,.left⟩) (3*P) i)

theorem prepare_active (e : J ≃ Mode × F) (P i : ℕ) (c : NativeIO.Config (Fin 2) J) :
    NativeIO.Active (prepareSchedule e P i) c := by
  apply NativeIOModeProduct.active
  intro d
  apply append_active
  · intro _; exact ScheduledRawInput.cell_active _ _
  · intro _; exact ScheduledTapeAction.active _ _ _

theorem prepare_exact (e : J ≃ Mode × F) (f : F) (P : ℕ) (w : List Bool) :
    trajectory (prepareSchedule e P) w (initial e f) (3*P+P)=prepared e f P w := by
  unfold prepareSchedule
  rw [initial,trajectory_attach,append_exact,ScheduledRawInput.schedule_exact]
  rfl

theorem prepared_spec (e : J ≃ Mode × F) (f : F) (P : ℕ) (w : List Bool) :
    (∀ t, (prepared e f P w).work.pos t=0) ∧
    (∀ j < P, bit (cells (prepared e f P w) 0 j)=ScheduledRawInput.inputBit w j) ∧
    (∀ z, cells (prepared e f P w) 1 z=.blank) ∧
    (prepared e f P w).inputPos=P ∧ (prepared e f P w).outRev=[] ∧
    (e (prepared e f P w).work.core.pc).2=f := by
  refine ⟨RawMaskedStride.prepared_position P w,?_,RawMaskedStride.prepared_scratch P w,
    (RawMaskedStride.prepared_io P w).1,(RawMaskedStride.prepared_io P w).2,?_⟩
  · intro j hj
    have h := RawMaskedStride.prepared_input P w j hj
    change bit (cells (RawMaskedStride.prepared P w) 0
      ((RawMaskedStride.prepared P w).work.pos 0+j))=_ at h
    rw [RawMaskedStride.prepared_position,zero_add] at h
    exact h
  · simp only [prepared,attach,Equiv.apply_symm_apply]

end TransposeFollowup.ScheduledModeRawIO
