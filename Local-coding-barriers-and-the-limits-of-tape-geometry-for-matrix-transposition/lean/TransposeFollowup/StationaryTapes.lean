import Mathlib
import Transpose.Statement

/-! Add a fixed bank of stationary tapes in the original machine model.
Source states, alphabet, input/output and charged steps are unchanged. -/
namespace TransposeFollowup.StationaryTapes
set_option autoImplicit false

def ports (M : Transpose.TM) (extra : ℕ) : Fin M.k ⊕ Fin extra ≃ Fin (M.k+extra) :=
  finSumFinEquiv

abbrev Transition (M : Transpose.TM) :=
  Fin (M.q+1) × Transpose.Dir × (Fin M.k → Fin (M.g+1) × Transpose.Dir) × Option Bool

def liftTransition (M : Transpose.TM) (extra : ℕ) (scanned : Fin (M.k+extra) → Fin (M.g+1))
    (tr : Transition M) :
    Fin (M.q+1) × Transpose.Dir × (Fin (M.k+extra) → Fin (M.g+1) × Transpose.Dir) × Option Bool :=
  let (s,d,acts,o):=tr
  (s,d,fun t => Sum.elim acts (fun p => (scanned (ports M extra (.inr p)),.stay))
    ((ports M extra).symm t),o)

def delta (M : Transpose.TM) (extra : ℕ) (s : Fin (M.q+1)) (input : Option Bool)
    (scanned : Fin (M.k+extra) → Fin (M.g+1)) :=
  (M.δ s input (fun p => scanned (ports M extra (.inl p)))).map (liftTransition M extra scanned)

abbrev machine (M : Transpose.TM) (extra : ℕ) : Transpose.TM :=
  ⟨M.k+extra,M.g,M.q,delta M extra⟩

def embed (M : Transpose.TM) (extra : ℕ) (c : Transpose.Config M) :
    Transpose.Config (machine M extra) where
  state:=c.state
  inPos:=c.inPos
  work:=fun t => Sum.elim c.work (fun _ _ => 0) ((ports M extra).symm t)
  workPos:=fun t => Sum.elim c.workPos (fun _ => 0) ((ports M extra).symm t)
  outRev:=c.outRev

theorem initial_embed (M : Transpose.TM) (extra : ℕ) :
    embed M extra (Transpose.init M)=Transpose.init (machine M extra) := by
  unfold embed Transpose.init
  congr 1
  · funext t z
    cases (ports M extra).symm t <;> rfl
  · funext t
    cases (ports M extra).symm t <;> rfl

theorem step_embed (M : Transpose.TM) (extra : ℕ) (w : List Bool) (c : Transpose.Config M) :
    Transpose.step (machine M extra) w (embed M extra c)=
      (Transpose.step M w c).map (embed M extra) := by
  simp only [Transpose.step,machine,delta,embed,Equiv.symm_apply_apply,Sum.elim_inl]
  cases hd : M.δ c.state (Transpose.readInput w c.inPos) (fun p => c.work p (c.workPos p)) with
  | none => rfl
  | some tr =>
    rcases tr with ⟨s,move,acts,out⟩
    simp only [Option.map_some,liftTransition,embed]
    congr 2
    · funext t z
      obtain ⟨p,rfl⟩:=(ports M extra).surjective t
      cases p <;> simp only [Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,ite_self]
    · funext t
      cases (ports M extra).symm t <;> rfl

theorem fixed_resources (M : Transpose.TM) (extra : ℕ) :
    (machine M extra).k=M.k+extra ∧ (machine M extra).g=M.g ∧ (machine M extra).q=M.q :=
  ⟨rfl,rfl,rfl⟩

end TransposeFollowup.StationaryTapes
