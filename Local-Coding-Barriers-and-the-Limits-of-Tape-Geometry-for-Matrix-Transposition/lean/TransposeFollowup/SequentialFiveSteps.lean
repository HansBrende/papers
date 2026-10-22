import TransposeFollowup.SequentialFiveMachine

namespace TransposeFollowup.SequentialFive
set_option autoImplicit false

theorem step_left (A B : Program) (w : List Bool) (c d : Transpose.Config A.tm) (frame : Frame B)
    (h : Transpose.step A.tm w c=some d) :
    Transpose.step (machine A B) w (embedLeft A B c frame)=some (embedLeft A B d frame) := by
  cases hd : A.delta c.state (Transpose.readInput w c.inPos) (fun p => c.work p (c.workPos p)) with
  | none => simp [Transpose.step,Program.tm,hd] at h
  | some tr =>
    rcases tr with ⟨s,move,acts,out⟩
    simp only [Transpose.step,Program.tm,hd,Option.some.injEq] at h
    rw [← h]
    simp only [Transpose.step,machine,delta,embedLeft,Equiv.symm_apply_apply,Sum.elim_inl,hd,liftLeft]
    congr 2
    · funext t z
      obtain ⟨p,rfl⟩:=(ports A B).surjective t
      cases p <;> simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
      exact hold_cell _ _ _
    · funext t
      cases (ports A B).symm t <;> rfl

theorem step_right (A B : Program) (w : List Bool) (frame : Frame A) (c : Transpose.Config B.tm) :
    Transpose.step (machine A B) w (embedRight A B frame c)=
      (Transpose.step B.tm w c).map (embedRight A B frame) := by
  simp only [Transpose.step,machine,delta,embedRight,Equiv.symm_apply_apply,Sum.elim_inr,Program.tm]
  cases hd : B.delta c.state (Transpose.readInput w c.inPos) (fun p => c.work p (c.workPos p)) with
  | none => rfl
  | some tr =>
    rcases tr with ⟨s,move,acts,out⟩
    simp only [Option.map_some,liftRight,embedRight]
    congr 2
    · funext t z
      obtain ⟨p,rfl⟩:=(ports A B).surjective t
      cases p <;> simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
      exact hold_cell _ _ _
    · funext t
      cases (ports A B).symm t <;> rfl

theorem transfer (A B : Program) (w : List Bool) (c : Transpose.Config A.tm)
    (hh : Transpose.step A.tm w c=none) (hi : c.inPos=0) (ho : c.outRev=[]) :
    Transpose.step (machine A B) w (embedLeft A B c (blankFrame B))=
      some (embedRight A B (frameOf A c) (Transpose.init B.tm)) := by
  have hd : A.delta c.state (Transpose.readInput w c.inPos) (fun p => c.work p (c.workPos p))=none := by
    cases h : A.delta c.state (Transpose.readInput w c.inPos) (fun p => c.work p (c.workPos p)) with
    | none => rfl
    | some tr => simp [Transpose.step,Program.tm,h] at hh
  rw [hi] at hd
  simp only [Transpose.step,machine,delta,embedLeft,Equiv.symm_apply_apply,Sum.elim_inl,hd,
    embedRight,frameOf,Transpose.init,blankFrame,Transpose.Dir.shift,hi,ho]
  congr 2
  funext t z
  exact hold_cell _ _ _

end TransposeFollowup.SequentialFive
