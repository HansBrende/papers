import Mathlib
import Transpose.Statement

/-! Sequential composition in the original model, using disjoint tape banks.
Program merely packages the parameters of a five-symbol Transpose.TM; all
execution statements use the original step/stepN definitions. -/
namespace TransposeFollowup.SequentialFive
set_option autoImplicit false

structure Program where
  k : ℕ
  q : ℕ
  delta : Fin (q+1) → Option Bool → (Fin k → Fin 5) →
    Option (Fin (q+1) × Transpose.Dir × (Fin k → Fin 5 × Transpose.Dir) × Option Bool)

abbrev Program.tm (A : Program) : Transpose.TM := ⟨A.k,4,A.q,A.delta⟩
abbrev Transition (A : Program) :=
  Fin (A.q+1) × Transpose.Dir × (Fin A.k → Fin 5 × Transpose.Dir) × Option Bool
abbrev JoinedTransition (A B : Program) :=
  Fin (A.q+B.q+1+1) × Transpose.Dir × (Fin (A.k+B.k) → Fin 5 × Transpose.Dir) × Option Bool

structure Frame (A : Program) where
  work : Fin A.k → ℤ → Fin 5
  pos : Fin A.k → ℤ

def blankFrame (A : Program) : Frame A := ⟨fun _ _ => 0,fun _ => 0⟩
def frameOf (A : Program) (c : Transpose.Config A.tm) : Frame A := ⟨c.work,c.workPos⟩
def ports (A B : Program) : Fin A.k ⊕ Fin B.k ≃ Fin (A.k+B.k) := finSumFinEquiv
def states (A B : Program) : Fin (A.q+1) ⊕ Fin (B.q+1) ≃ Fin (A.q+B.q+1+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def liftLeft (A B : Program) (scanned : Fin (A.k+B.k) → Fin 5) (tr : Transition A) : JoinedTransition A B :=
  let (s,d,acts,o):=tr
  (states A B (.inl s),d,fun t => Sum.elim acts (fun p => (scanned (ports A B (.inr p)),.stay)) ((ports A B).symm t),o)
def liftRight (A B : Program) (scanned : Fin (A.k+B.k) → Fin 5) (tr : Transition B) : JoinedTransition A B :=
  let (s,d,acts,o):=tr
  (states A B (.inr s),d,fun t => Sum.elim (fun p => (scanned (ports A B (.inl p)),.stay)) acts ((ports A B).symm t),o)

def delta (A B : Program) (s : Fin (A.q+B.q+1+1)) (input : Option Bool)
    (scanned : Fin (A.k+B.k) → Fin 5) : Option (JoinedTransition A B) :=
  match (states A B).symm s with
  | .inl pc => match A.delta pc input (fun p => scanned (ports A B (.inl p))) with
      | some tr => some (liftLeft A B scanned tr)
      | none => some (states A B (.inr 0),.stay,fun t => (scanned t,.stay),none)
  | .inr pc => (B.delta pc input (fun p => scanned (ports A B (.inr p)))).map (liftRight A B scanned)

abbrev machine (A B : Program) : Transpose.TM := ⟨A.k+B.k,4,A.q+B.q+1,delta A B⟩

def embedLeft (A B : Program) (c : Transpose.Config A.tm) (frame : Frame B) : Transpose.Config (machine A B) where
  state:=states A B (.inl c.state)
  inPos:=c.inPos
  work:=fun t => Sum.elim c.work frame.work ((ports A B).symm t)
  workPos:=fun t => Sum.elim c.workPos frame.pos ((ports A B).symm t)
  outRev:=c.outRev

def embedRight (A B : Program) (frame : Frame A) (c : Transpose.Config B.tm) : Transpose.Config (machine A B) where
  state:=states A B (.inr c.state)
  inPos:=c.inPos
  work:=fun t => Sum.elim frame.work c.work ((ports A B).symm t)
  workPos:=fun t => Sum.elim frame.pos c.workPos ((ports A B).symm t)
  outRev:=c.outRev

theorem states_zero (A B : Program) : states A B (.inl 0)=0 := by
  apply Fin.ext
  simp [states,finSumFinEquiv]

theorem initial_embed (A B : Program) :
    embedLeft A B (Transpose.init A.tm) (blankFrame B)=Transpose.init (machine A B) := by
  unfold embedLeft blankFrame Transpose.init
  rw [states_zero]
  congr 1
  · funext t z
    cases (ports A B).symm t <;> rfl
  · funext t
    cases (ports A B).symm t <;> rfl

theorem hold_cell (f : ℤ → Fin 5) (p z : ℤ) : (if z=p then f p else f z)=f z := by
  split_ifs with h
  · rw [h]
  · rfl

theorem fixed_resources (A B : Program) :
    (machine A B).k=A.k+B.k ∧ (machine A B).g+1=5 ∧ (machine A B).q+1=(A.q+1)+(B.q+1) := by
  refine ⟨rfl,rfl,?_⟩
  change A.q+B.q+1+1=(A.q+1)+(B.q+1)
  omega

end TransposeFollowup.SequentialFive
