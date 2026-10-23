import BitWord.NativeOracleScan

/-! The captured interpreter preserves the original oracle's semantics.
The source machine may branch on arbitrary tape contents. -/
namespace BitWord.NativeOracle
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false

def observe (M : Transpose.TM) (state : State M) (tapes : Tapes M) (pos : Positions M)
    (outRev : List Bool) : Transpose.Config (plane M) where
  state := state
  inPos := pos .input
  work := fun i z => NativeMicrocode.symbolCode (AbsoluteTape.cells (tapes (.work i)) (pos (.work i)) z)
  workPos := fun i => pos (.work i)
  outRev := outRev

def InputRep (M : Transpose.TM) (w : List Bool) (tapes : Tapes M) (pos : Positions M) : Prop :=
  ∀ z, inputSymbol (AbsoluteTape.cells (tapes .input) (pos .input) z)=Transpose.readInput w z

def nextOutput (tr : Option Bool) (outRev : List Bool) :=
  match tr with | none => outRev | some b => b::outRev

theorem readInput_observe (M : Transpose.TM) (w : List Bool) (tapes : Tapes M)
    (pos : Positions M) (h : InputRep M w tapes pos) :
    Transpose.readInput w (pos .input)=inputSymbol (tapes .input).head := by
  simpa [AbsoluteTape.scanned] using (h (pos .input)).symm

theorem observed_scanned (M : Transpose.TM) (state : State M) (tapes : Tapes M)
    (pos : Positions M) (outRev : List Bool) :
    (fun i => (observe M state tapes pos outRev).work i
      ((observe M state tapes pos outRev).workPos i))=scanned M tapes := by
  funext i; simp only [observe,AbsoluteTape.scanned]; rfl

theorem transition_observe (M : Transpose.TM) (state : State M) (w : List Bool)
    (tapes : Tapes M) (pos : Positions M) (outRev : List Bool) (hinput : InputRep M w tapes pos)
    (tr : Transition M)
    (htr : (plane M).δ state (inputSymbol (tapes .input).head)
      (scanned M tapes)=some tr) :
    Transpose.step (plane M) w (observe M state tapes pos outRev)=
      some (observe M tr.1 (transitioned M tr tapes pos).core.tapes
        (transitioned M tr tapes pos).pos (nextOutput tr.2.2.2 outRev)) := by
  have hd : (plane M).δ (observe M state tapes pos outRev).state
      (Transpose.readInput w (observe M state tapes pos outRev).inPos)
      (fun i => (observe M state tapes pos outRev).work i
        ((observe M state tapes pos outRev).workPos i))=some tr := by
    rw [observed_scanned]
    change (plane M).δ state (Transpose.readInput w (pos .input)) (scanned M tapes)=some tr
    rw [readInput_observe M w tapes pos hinput,htr]
  rw [Transpose.step,hd]
  rcases tr with ⟨s,d,a,o⟩
  apply congrArg some
  have hw : (fun i z => if z=pos (.work i) then (a i).1 else
      NativeMicrocode.symbolCode (AbsoluteTape.cells (tapes (.work i)) (pos (.work i)) z)) =
    (observe M s (transitioned M (s,d,a,o) tapes pos).core.tapes
      (transitioned M (s,d,a,o) tapes pos).pos (nextOutput o outRev)).work := by
    funext i z
    change (if z=pos (.work i) then (a i).1 else
      NativeMicrocode.symbolCode (AbsoluteTape.cells (tapes (.work i)) (pos (.work i)) z)) =
      NativeMicrocode.symbolCode (AbsoluteTape.cells
        ((actions M (s,d,a,o) (.work i)).actual (tapes (.work i)))
        ((NativeMicrocode.direction (actions M (s,d,a,o) (.work i)).move).shift (pos (.work i))) z)
    rw [NativeMicrocode.action_cells]
    simp only [actions,Option.getD_some,apply_ite,NativeMicrocode.symbolCode_decode]
    split_ifs <;> simp_all
  have hw' : (fun i z => if z=(observe M state tapes pos outRev).workPos i then (a i).1 else
      (observe M state tapes pos outRev).work i z) =
    (observe M s (transitioned M (s,d,a,o) tapes pos).core.tapes
      (transitioned M (s,d,a,o) tapes pos).pos (nextOutput o outRev)).work := hw
  rw [hw']
  congr 1 <;> simp [observe,transitioned,cfg,actions,direction_move,nextOutput]

theorem transition_input (M : Transpose.TM) (w : List Bool) (tapes : Tapes M)
    (pos : Positions M) (hinput : InputRep M w tapes pos) (tr : Transition M) :
    InputRep M w (transitioned M tr tapes pos).core.tapes (transitioned M tr tapes pos).pos := by
  intro z
  change inputSymbol (AbsoluteTape.cells ((actions M tr .input).actual (tapes .input))
    ((NativeMicrocode.direction (actions M tr .input).move).shift (pos .input)) z)=_
  rw [NativeMicrocode.action_cells]
  simp only [actions,Option.getD_none]
  split_ifs with hz
  · subst z; simpa [AbsoluteTape.scanned] using hinput (pos .input)
  · exact hinput z

theorem halt_observe (M : Transpose.TM) (state : State M) (w : List Bool)
    (tapes : Tapes M) (pos : Positions M) (outRev : List Bool) (hinput : InputRep M w tapes pos) :
    Transpose.step (plane M) w (observe M state tapes pos outRev)=none ↔
      (plane M).δ state (inputSymbol (tapes .input).head) (scanned M tapes)=none := by
  have hi := readInput_observe M w tapes pos hinput
  rw [Transpose.step,observed_scanned]
  dsimp only [observe,plane]
  rw [hi]
  cases hd : BitPlaneMachine.delta M state (inputSymbol (tapes .input).head) (scanned M tapes) <;>
    simp only [hd,Option.some_ne_none,not_false_eq_true]

/-- Output is a literal finite tape, with its head immediately after the emitted word. -/
def Captured (M : Transpose.TM) (outRev : List Bool) (tapes : Tapes M) (pos : Positions M) : Prop :=
  tapes .capture=Turing.Tape.mk₂ (outRev.map Sym.data ++ [.start]) [] ∧ pos .capture=outRev.length

theorem transition_captured (M : Transpose.TM) (tapes : Tapes M) (pos : Positions M)
    (outRev : List Bool) (h : Captured M outRev tapes pos) (tr : Transition M) :
    Captured M (nextOutput tr.2.2.2 outRev) (transitioned M tr tapes pos).core.tapes
      (transitioned M tr tapes pos).pos := by
  rcases h with ⟨ht,hp⟩
  unfold Captured transitioned cfg
  simp only [actions,ht,hp]
  cases ho : tr.2.2.2 with
  | none => simp [ho,nextOutput,Microcode.Action.actual,NativeMicrocode.direction,Transpose.Dir.shift]
  | some b =>
    simp [ho,nextOutput,Microcode.Action.actual,NativeMicrocode.direction,Transpose.Dir.shift,
      Turing.Tape.mk₂,Turing.Tape.write_mk',Turing.Tape.move_right_mk']

end BitWord.NativeOracle
