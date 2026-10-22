import TransposeFollowup.GeneratorRowsPreparedGeometry
import TransposeFollowup.TimedMatchingSchedule

namespace TransposeFollowup.TimedRowWalk
open FixedTapeCompiler
open scoped BigOperators
set_option autoImplicit false
variable {q v : ℕ}

def walk (R stride delay : ℕ) : ℕ → List (OpcodeDecoder.Ops q) → Fin q → ℕ → ℤ
  | _,[],_,_ => 0
  | offset,ops::rows,p,t => (ops p).direction*cappedRamp (4*R) (offset+delay+R) t+
      walk R stride delay (offset+stride) rows p t

def displacement (R : ℕ) (rows : List (OpcodeDecoder.Ops q)) (p : Fin q) : ℤ :=
  (rows.map (fun ops => (ops p).direction*((4*R:ℕ):ℤ))).sum

theorem ofFn_eq_sum (R stride delay offset : ℕ) (ops : Fin v → OpcodeDecoder.Ops q) (p : Fin q) (t : ℕ) :
    walk R stride delay offset (List.ofFn ops) p t=
      ∑ i : Fin v,(ops i p).direction*cappedRamp (4*R) (offset+stride*i.val+delay+R) t := by
  induction v generalizing offset with
  | zero => simp [walk]
  | succ v ih =>
    rw [List.ofFn_succ,walk,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,mul_zero,add_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show offset+stride+stride*i.val+delay+R=offset+stride*(i.val+1)+delay+R by ring]

theorem before (R stride delay offset : ℕ) (rows : List (OpcodeDecoder.Ops q)) (p : Fin q) (t : ℕ) (ht : t ≤ offset) :
    walk R stride delay offset rows p t=0 := by
  induction rows generalizing offset with
  | nil => rfl
  | cons ops rows ih =>
    rw [walk,ih (offset+stride) (by omega)]
    have h : cappedRamp (4*R) (offset+delay+R) t=0:=by unfold cappedRamp;omega
    rw [h,mul_zero,add_zero]

theorem append (R stride delay offset : ℕ) (front tail : List (OpcodeDecoder.Ops q)) (p : Fin q) (t : ℕ) :
    walk R stride delay offset (front++tail) p t=
      walk R stride delay offset front p t+walk R stride delay (offset+stride*front.length) tail p t := by
  induction front generalizing offset with
  | nil => simp [walk]
  | cons ops front ih =>
    rw [List.cons_append,walk,walk,ih]
    simp only [List.length_cons]
    rw [show offset+stride+stride*front.length=offset+stride*(front.length+1) by ring]
    ring

theorem after (R stride delay offset : ℕ) (hs : delay+5*R ≤ stride) (rows : List (OpcodeDecoder.Ops q))
    (p : Fin q) (t : ℕ) (ht : offset+stride*rows.length ≤ t) :
    walk R stride delay offset rows p t=displacement R rows p := by
  induction rows generalizing offset with
  | nil => simp [walk,displacement]
  | cons ops rows ih =>
    have htail : offset+stride+stride*rows.length ≤ t := by
      simp only [List.length_cons] at ht
      nlinarith
    have hhead : offset+delay+R+4*R ≤ t := by nlinarith [Nat.zero_le (stride*rows.length)]
    have hc : cappedRamp (4*R) (offset+delay+R) t=(4*R:ℕ):=by unfold cappedRamp;omega
    rw [walk,hc,ih (offset+stride) htail]
    rfl

theorem finishPos_eq (R : ℕ) (rows : List (OpcodeDecoder.Ops q)) (pos : ReusablePageClock.Port q → ℤ) (p : Fin q) :
    RowLoop.finishPos rows (SevenPhaseClock.word R) pos (some p)=pos (some p)+displacement R rows p := by
  induction rows generalizing pos with
  | nil => simp [RowLoop.finishPos,displacement]
  | cons ops rows ih =>
    change RowLoop.finishPos rows (SevenPhaseClock.word R)
      (PageClock.advance ops pos 0 ((SevenPhaseClock.word R).count true)) (some p)=_
    rw [ih]
    simp only [PageClock.advance,SevenPhaseClock.word_count,displacement,List.map_cons,List.sum_cons]
    ring

theorem at_row (R stride delay offset : ℕ) (hs : delay+5*R ≤ stride)
    (front tail : List (OpcodeDecoder.Ops q)) (ops : OpcodeDecoder.Ops q) (p : Fin q)
    (s : ℕ) (ht : s ≤ stride) :
    walk R stride delay offset (front++ops::tail) p (offset+stride*front.length+s)=
      displacement R front p+(ops p).direction*cappedRamp (4*R) R (s-delay) := by
  rw [append,after R stride delay offset hs front p _ (by omega),walk]
  have hb : walk R stride delay (offset+stride*front.length+stride) tail p (offset+stride*front.length+s)=0:=
    before R stride delay _ tail p _ (by omega)
  rw [hb,add_zero]
  have hr : cappedRamp (4*R) (offset+stride*front.length+delay+R) (offset+stride*front.length+s)=
      cappedRamp (4*R) R (s-delay) := by unfold cappedRamp;omega
  rw [hr]

end TransposeFollowup.TimedRowWalk
