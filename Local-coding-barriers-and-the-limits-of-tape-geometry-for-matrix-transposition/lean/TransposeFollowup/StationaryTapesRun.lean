import TransposeFollowup.StationaryTapes
import Transpose.Tape.Defs

namespace TransposeFollowup.StationaryTapes
set_option autoImplicit false

theorem stepN_embed (M : Transpose.TM) (extra : ℕ) (w : List Bool) (n : ℕ)
    (c : Transpose.Config M) :
    Transpose.stepN (machine M extra) w n (embed M extra c)=
      (Transpose.stepN M w n c).map (embed M extra) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Transpose.stepN,step_embed,Transpose.stepN]
    cases h : Transpose.step M w c with
    | none => rfl
    | some d => exact ih d

theorem halts_iff (M : Transpose.TM) (extra : ℕ) (w : List Bool) (c : Transpose.Config M) :
    Transpose.step (machine M extra) w (embed M extra c)=none ↔ Transpose.step M w c=none := by
  rw [step_embed]
  simp

theorem run_embed (M : Transpose.TM) (extra : ℕ) (w : List Bool) (n : ℕ) :
    Transpose.Tape.run (machine M extra) w n=embed M extra (Transpose.Tape.run M w n) := by
  induction n with
  | zero => exact (initial_embed M extra).symm
  | succ n ih =>
    simp only [Transpose.Tape.run,ih,step_embed]
    cases h : Transpose.step M w (Transpose.Tape.run M w n) <;> rfl

theorem observations (M : Transpose.TM) (extra : ℕ) (w : List Bool) (n : ℕ) :
    (Transpose.Tape.run (machine M extra) w n).state=(Transpose.Tape.run M w n).state ∧
    (Transpose.Tape.run (machine M extra) w n).inPos=(Transpose.Tape.run M w n).inPos ∧
    (Transpose.Tape.run (machine M extra) w n).outRev=(Transpose.Tape.run M w n).outRev ∧
    (∀ p,(Transpose.Tape.run (machine M extra) w n).workPos (ports M extra (.inl p))=
      (Transpose.Tape.run M w n).workPos p) ∧
    (∀ p,(Transpose.Tape.run (machine M extra) w n).workPos (ports M extra (.inr p))=0) ∧
    (∀ p z,(Transpose.Tape.run (machine M extra) w n).work (ports M extra (.inr p)) z=0) := by
  rw [run_embed]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩ <;>
    simp only [embed,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,implies_true]

theorem computesWithin (M : Transpose.TM) (extra : ℕ) (w out : List Bool) (t : ℕ)
    (h : Transpose.ComputesWithin M w out t) :
    Transpose.ComputesWithin (machine M extra) w out t := by
  obtain ⟨s,hs,c,hc,hh,ho⟩:=h
  refine ⟨s,hs,embed M extra c,?_,(halts_iff M extra w c).mpr hh,ho⟩
  rw [← initial_embed,stepN_embed,hc]
  rfl

theorem computesWithin_iff (M : Transpose.TM) (extra : ℕ) (w out : List Bool) (t : ℕ) :
    Transpose.ComputesWithin (machine M extra) w out t ↔ Transpose.ComputesWithin M w out t := by
  constructor
  · rintro ⟨s,hs,c,hc,hh,ho⟩
    rw [← initial_embed,stepN_embed] at hc
    obtain ⟨d,hd,he⟩:=Option.map_eq_some_iff.mp hc
    rw [← he] at hh ho
    exact ⟨s,hs,d,hd,(halts_iff M extra w d).mp hh,ho⟩
  · exact computesWithin M extra w out t

theorem transposesWithin (M : Transpose.TM) (extra : ℕ) (T : ℕ → ℕ)
    (h : Transpose.TransposesWithin M T) : Transpose.TransposesWithin (machine M extra) T := by
  intro n hn A
  exact computesWithin M extra _ _ _ (h n hn A)

end TransposeFollowup.StationaryTapes
