import TransposeFollowup.BitPlaneMachine
import Transpose.Tape.Defs

/-! Exact execution, halting, output and time preservation for every source
machine, input and configuration; no validity promise on the input. -/
namespace TransposeFollowup.BitPlaneMachine
set_option autoImplicit false

theorem stepN_embed (M : Transpose.TM) (w : List Bool) (n : ℕ) (c : Transpose.Config M) :
    Transpose.stepN (machine M) w n (embed M c)=(Transpose.stepN M w n c).map (embed M) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Transpose.stepN,step_embed,Transpose.stepN]
    cases h : Transpose.step M w c with
    | none => rfl
    | some d => exact ih d

theorem halts_iff (M : Transpose.TM) (w : List Bool) (c : Transpose.Config M) :
    Transpose.step (machine M) w (embed M c)=none ↔ Transpose.step M w c=none := by
  rw [step_embed]
  simp

theorem run_embed (M : Transpose.TM) (w : List Bool) (n : ℕ) :
    Transpose.Tape.run (machine M) w n=embed M (Transpose.Tape.run M w n) := by
  induction n with
  | zero => exact (initial_embed M).symm
  | succ n ih =>
    simp only [Transpose.Tape.run,ih,step_embed]
    cases h : Transpose.step M w (Transpose.Tape.run M w n) <;> rfl

theorem observations (M : Transpose.TM) (w : List Bool) (n : ℕ) :
    (Transpose.Tape.run (machine M) w n).state=(Transpose.Tape.run M w n).state ∧
    (Transpose.Tape.run (machine M) w n).inPos=(Transpose.Tape.run M w n).inPos ∧
    (Transpose.Tape.run (machine M) w n).outRev=(Transpose.Tape.run M w n).outRev ∧
    ∀ p i,(Transpose.Tape.run (machine M) w n).workPos (ports M (p,i))=(Transpose.Tape.run M w n).workPos p := by
  rw [run_embed]
  refine ⟨rfl,rfl,rfl,?_⟩
  intro p i
  simp only [embed,Equiv.symm_apply_apply]

theorem computesWithin (M : Transpose.TM) (w out : List Bool) (t : ℕ)
    (h : Transpose.ComputesWithin M w out t) : Transpose.ComputesWithin (machine M) w out t := by
  obtain ⟨s,hs,c,hc,hh,ho⟩:=h
  refine ⟨s,hs,embed M c,?_,(halts_iff M w c).mpr hh,ho⟩
  rw [← initial_embed,stepN_embed,hc]
  rfl

theorem computesWithin_iff (M : Transpose.TM) (w out : List Bool) (t : ℕ) :
    Transpose.ComputesWithin (machine M) w out t ↔ Transpose.ComputesWithin M w out t := by
  constructor
  · rintro ⟨s,hs,c,hc,hh,ho⟩
    rw [← initial_embed,stepN_embed] at hc
    obtain ⟨d,hd,he⟩:=Option.map_eq_some_iff.mp hc
    rw [← he] at hh ho
    exact ⟨s,hs,d,hd,(halts_iff M w d).mp hh,ho⟩
  · exact computesWithin M w out t

theorem transposesWithin (M : Transpose.TM) (T : ℕ → ℕ) (h : Transpose.TransposesWithin M T) :
    Transpose.TransposesWithin (machine M) T := by
  intro n hn A
  exact computesWithin M _ _ _ (h n hn A)

end TransposeFollowup.BitPlaneMachine
