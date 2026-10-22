import TransposeFollowup.SequentialFiveSteps
import Transpose.Tape.Run

namespace TransposeFollowup.SequentialFive
set_option autoImplicit false

theorem stepN_add (M : Transpose.TM) (w : List Bool) (a b : ℕ) (c : Transpose.Config M) :
    Transpose.stepN M w (a+b) c=(Transpose.stepN M w a c).bind (Transpose.stepN M w b) := by
  induction a generalizing c with
  | zero => rw [Nat.zero_add];rfl
  | succ a ih =>
    simp only [Nat.succ_add,Transpose.stepN]
    cases h : Transpose.step M w c with
    | none => rfl
    | some d => exact ih d

theorem stepN_left (A B : Program) (w : List Bool) (n : ℕ) (c d : Transpose.Config A.tm) (frame : Frame B)
    (h : Transpose.stepN A.tm w n c=some d) :
    Transpose.stepN (machine A B) w n (embedLeft A B c frame)=some (embedLeft A B d frame) := by
  induction n generalizing c with
  | zero =>
    have hd : c=d := Option.some.inj h
    subst d
    rfl
  | succ n ih =>
    rw [Transpose.stepN] at h
    cases hs : Transpose.step A.tm w c with
    | none => simp [hs] at h
    | some e =>
      rw [hs] at h
      rw [Transpose.stepN,step_left A B w c e frame hs]
      exact ih e h

theorem stepN_right (A B : Program) (w : List Bool) (n : ℕ) (frame : Frame A) (c : Transpose.Config B.tm) :
    Transpose.stepN (machine A B) w n (embedRight A B frame c)=
      (Transpose.stepN B.tm w n c).map (embedRight A B frame) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Transpose.stepN,step_right,Transpose.stepN]
    cases h : Transpose.step B.tm w c with
    | none => rfl
    | some d => exact ih d

theorem execute (A B : Program) (w : List Bool) (a b : ℕ)
    (ca : Transpose.Config A.tm) (cb : Transpose.Config B.tm)
    (ha : Transpose.stepN A.tm w a (Transpose.init A.tm)=some ca)
    (hh : Transpose.step A.tm w ca=none) (hi : ca.inPos=0) (ho : ca.outRev=[])
    (hb : Transpose.stepN B.tm w b (Transpose.init B.tm)=some cb) :
    Transpose.stepN (machine A B) w (a+1+b) (Transpose.init (machine A B))=
      some (embedRight A B (frameOf A ca) cb) := by
  have hp:=stepN_left A B w a (Transpose.init A.tm) ca (blankFrame B) ha
  rw [initial_embed] at hp
  have hs : Transpose.stepN (machine A B) w (b+1) (embedLeft A B ca (blankFrame B))=
      some (embedRight A B (frameOf A ca) cb) := by
    rw [Transpose.stepN,transfer A B w ca hh hi ho]
    dsimp only
    rw [stepN_right,hb]
    rfl
  have ht:=stepN_add (machine A B) w a (b+1) (Transpose.init (machine A B))
  rw [hp,Option.bind_some,hs] at ht
  simpa only [show a+(b+1)=a+1+b by omega] using ht

theorem computesWithin (A B : Program) (w out : List Bool) (a t : ℕ) (ca : Transpose.Config A.tm)
    (ha : Transpose.stepN A.tm w a (Transpose.init A.tm)=some ca)
    (hh : Transpose.step A.tm w ca=none) (hi : ca.inPos=0) (ho : ca.outRev=[])
    (hb : Transpose.ComputesWithin B.tm w out t) :
    Transpose.ComputesWithin (machine A B) w out (a+1+t) := by
  obtain ⟨b,hb,cb,hstep,hhalt,hout⟩:=hb
  refine ⟨a+1+b,by omega,embedRight A B (frameOf A ca) cb,execute A B w a b ca cb ha hh hi ho hstep,?_,hout⟩
  rw [step_right,hhalt]
  rfl

theorem source_prefix (M : Transpose.TM) (w : List Bool) (t s : ℕ) (c d : Transpose.Config M)
    (h : Transpose.stepN M w t c=some d) (hs : s ≤ t) : ∃ e,Transpose.stepN M w s c=some e := by
  rw [show t=s+(t-s) by omega,stepN_add] at h
  cases he : Transpose.stepN M w s c with
  | none => simp [he] at h
  | some e => exact ⟨e,rfl⟩

theorem prefix_run (A B : Program) (w : List Bool) (t s : ℕ) (d : Transpose.Config A.tm)
    (ht : Transpose.stepN A.tm w t (Transpose.init A.tm)=some d) (hs : s ≤ t) :
    Transpose.Tape.run (machine A B) w s=embedLeft A B (Transpose.Tape.run A.tm w s) (blankFrame B) := by
  obtain ⟨c,hc⟩:=source_prefix A.tm w t s (Transpose.init A.tm) d ht hs
  have hp:=stepN_left A B w s (Transpose.init A.tm) c (blankFrame B) hc
  rw [initial_embed] at hp
  have ha:=((Transpose.Tape.Impl.stepN_init_eq_some_iff s c).mp hc).2
  have hb:=((Transpose.Tape.Impl.stepN_init_eq_some_iff s (embedLeft A B c (blankFrame B))).mp hp).2
  rw [ha,hb]

end TransposeFollowup.SequentialFive
