import TransposeFollowup.BitPlaneAlphabet

/-! An arbitrary machine in the original model simulated over five symbols.
All bit planes of one source tape have synchronized heads. A single original
transition reads and updates all of the fixed planes simultaneously. -/
namespace TransposeFollowup.BitPlaneMachine
open BitPlaneAlphabet
set_option autoImplicit false

abbrev Port (M : Transpose.TM) := Fin M.k × Fin (width M.g)
abbrev Transition (M : Transpose.TM) :=
  Fin (M.q+1) × Transpose.Dir × (Fin M.k → Fin (M.g+1) × Transpose.Dir) × Option Bool
abbrev PlaneTransition (M : Transpose.TM) :=
  Fin (M.q+1) × Transpose.Dir × (Fin (M.k*width M.g) → Fin 5 × Transpose.Dir) × Option Bool

def ports (M : Transpose.TM) : Port M ≃ Fin (M.k*width M.g) := finProdFinEquiv

def liftTransition (M : Transpose.TM) (tr : Transition M) : PlaneTransition M :=
  let (s,d,acts,o):=tr
  (s,d,fun t => (encode M.g (acts ((ports M).symm t).1).1 ((ports M).symm t).2,
    (acts ((ports M).symm t).1).2),o)

def delta (M : Transpose.TM) (s : Fin (M.q+1)) (input : Option Bool)
    (scanned : Fin (M.k*width M.g) → Fin 5) : Option (PlaneTransition M) :=
  (M.δ s input (fun p => decode M.g (fun i => scanned (ports M (p,i))))).map (liftTransition M)

def machine (M : Transpose.TM) : Transpose.TM where
  k:=M.k*width M.g
  g:=4
  q:=M.q
  δ:=delta M

def embed (M : Transpose.TM) (c : Transpose.Config M) : Transpose.Config (machine M) where
  state:=c.state
  inPos:=c.inPos
  work:=fun t z => encode M.g (c.work ((ports M).symm t).1 z) ((ports M).symm t).2
  workPos:=fun t => c.workPos ((ports M).symm t).1
  outRev:=c.outRev

theorem scanned_decode (M : Transpose.TM) (c : Transpose.Config M) (p : Fin M.k) :
    decode M.g (fun i => (embed M c).work (ports M (p,i)) ((embed M c).workPos (ports M (p,i))))=
      c.work p (c.workPos p) := by
  simp only [embed,Equiv.symm_apply_apply,decode_encode]

theorem delta_embed (M : Transpose.TM) (c : Transpose.Config M) (input : Option Bool) :
    (machine M).δ (embed M c).state input (fun t => (embed M c).work t ((embed M c).workPos t))=
      (M.δ c.state input (fun p => c.work p (c.workPos p))).map (liftTransition M) := by
  simp only [machine,delta,embed,Equiv.symm_apply_apply,decode_encode]

theorem step_embed (M : Transpose.TM) (w : List Bool) (c : Transpose.Config M) :
    Transpose.step (machine M) w (embed M c)=(Transpose.step M w c).map (embed M) := by
  rw [Transpose.step,delta_embed]
  rw [Transpose.step]
  simp only [embed]
  cases h : M.δ c.state (Transpose.readInput w c.inPos) (fun p => c.work p (c.workPos p)) with
  | none => rfl
  | some tr =>
    rcases tr with ⟨s,d,acts,o⟩
    simp only [Option.map_some,liftTransition,embed]
    congr 2
    funext i z
    exact (apply_ite (fun a => encode M.g a ((ports M).symm i).2)
      (z=c.workPos ((ports M).symm i).1) (acts ((ports M).symm i).1).1 (c.work ((ports M).symm i).1 z)).symm

theorem initial_embed (M : Transpose.TM) : embed M (Transpose.init M)=Transpose.init (machine M) := by
  unfold embed Transpose.init
  simp only [encode_zero]
  rfl

theorem fixed_resources (M : Transpose.TM) :
    (machine M).k=M.k*max 1 M.g.size ∧ (machine M).g+1=5 ∧ (machine M).q=M.q := ⟨rfl,rfl,rfl⟩

end TransposeFollowup.BitPlaneMachine
