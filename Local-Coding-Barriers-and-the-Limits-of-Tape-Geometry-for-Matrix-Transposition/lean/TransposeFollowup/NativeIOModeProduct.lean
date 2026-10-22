import TransposeFollowup.ScheduledNativeIO

/-! Share a finite controller between subroutines without copying their
semantics. A subroutine updates one component and preserves the other.
Every instruction is transported by the existing native embedding theorem;
there are no extra instructions or uncharged changes of state. -/
namespace TransposeFollowup.NativeIOModeProduct
open FixedTapeCompiler
set_option autoImplicit false
variable {T L F J : Type*}

def attach (e : J ≃ L × F) (f : F) (c : NativeIO.Config T L) : NativeIO.Config T J :=
  ⟨⟨⟨e.symm (c.work.core.pc,f),c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩

def project (e : J ≃ L × F) (c : NativeIO.Config T J) : NativeIO.Config T L :=
  ⟨⟨⟨(e c.work.core.pc).1,c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩

@[simp] theorem project_attach (e : J ≃ L × F) (f : F) (c : NativeIO.Config T L) :
    project e (attach e f c)=c := by
  simp [project,attach]

@[simp] theorem attach_project (e : J ≃ L × F) (c : NativeIO.Config T J) :
    attach e (e c.work.core.pc).2 (project e c)=c := by
  simp [project,attach]

theorem embed_refl (labels : L → J) (c : NativeIO.Config T L)
    (frame : MicrocodeEmbedding.Frame T) :
    NativeIOEmbedding.embed (Function.Embedding.refl T) labels c frame=
      ⟨⟨⟨labels c.work.core.pc,c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩ := by
  have ht : Function.extend (Function.Embedding.refl T) c.work.core.tapes frame.tapes=
      c.work.core.tapes := by
    funext t
    exact MicrocodeEmbedding.extend_at (Function.Embedding.refl T) t _ _
  have hp : Function.extend (Function.Embedding.refl T) c.work.pos frame.pos=c.work.pos := by
    funext t
    exact MicrocodeEmbedding.extend_at (Function.Embedding.refl T) t _ _
  simp only [NativeIOEmbedding.embed,MicrocodeEmbedding.embed,ht,hp]

noncomputable def program (e : J ≃ L × F) (p : NativeIO.Program T L) : NativeIO.Program T J :=
  fun j => NativeIOEmbedding.instruction (Function.Embedding.refl T)
    (fun l => e.symm (l,(e j).2)) (p (e j).1)

theorem program_attach (e : J ≃ L × F) (p : NativeIO.Program T L) (l : L) (f : F) :
    program e p (e.symm (l,f))=NativeIOEmbedding.instruction (Function.Embedding.refl T)
      (fun l' => e.symm (l',f)) (p l) := by
  simp only [program,Equiv.apply_symm_apply]

theorem step_attach (e : J ≃ L × F) (p : NativeIO.Program T L) (f : F)
    (w : List Bool) (c : NativeIO.Config T L) :
    NativeIO.step (program e p) w (attach e f c)=attach e f (NativeIO.step p w c) := by
  have h := NativeIOEmbedding.step_embed (Function.Embedding.refl T)
    (fun l => e.symm (l,f)) p (program e p) w c
    ⟨c.work.core.tapes,c.work.pos⟩ (program_attach e p _ f)
  simpa only [embed_refl,attach] using h

theorem active_attach (e : J ≃ L × F) (p : NativeIO.Program T L) (f : F)
    (c : NativeIO.Config T L) (h : NativeIO.Active p c) :
    NativeIO.Active (program e p) (attach e f c) := by
  have h' := NativeIOEmbedding.active_embed (Function.Embedding.refl T)
    (fun l => e.symm (l,f)) p (program e p) c
    ⟨c.work.core.tapes,c.work.pos⟩ (program_attach e p _ f) h
  simpa only [embed_refl,attach] using h'

theorem active (e : J ≃ L × F) (p : NativeIO.Program T L)
    (h : ∀ c, NativeIO.Active p c) (c : NativeIO.Config T J) :
    NativeIO.Active (program e p) c := by
  simpa only [attach_project] using active_attach e p (e c.work.core.pc).2 (project e c) (h _)

theorem trajectory_attach (e : J ≃ L × F) (σ : ℕ → NativeIO.Program T L)
    (f : F) (w : List Bool) (c : NativeIO.Config T L) (n : ℕ) :
    ScheduledNativeIO.trajectory (fun i => program e (σ i)) w (attach e f c) n=
      attach e f (ScheduledNativeIO.trajectory σ w c n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ScheduledNativeIO.trajectory,ih,step_attach,ScheduledNativeIO.trajectory]

theorem trajectory_eq (e : J ≃ L × F) (σ : ℕ → NativeIO.Program T L)
    (w : List Bool) (c : NativeIO.Config T J) (n : ℕ) :
    ScheduledNativeIO.trajectory (fun i => program e (σ i)) w c n=
      attach e (e c.work.core.pc).2 (ScheduledNativeIO.trajectory σ w (project e c) n) := by
  conv_lhs => rw [← attach_project e c]
  exact trajectory_attach e σ _ w _ n

end TransposeFollowup.NativeIOModeProduct
