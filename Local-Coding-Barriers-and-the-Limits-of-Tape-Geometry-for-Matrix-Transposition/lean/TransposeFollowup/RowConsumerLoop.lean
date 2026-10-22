import TransposeFollowup.RowConsumerCalls
import TransposeFollowup.RowConsumerData

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def cursor (before todo : List Bool) : Tape Bool :=
  ⟨(symbols before).reverse++[.start],symbols todo++[.stop]⟩

def work (before todo index : List Bool) (pre : List (Sym Bool)) : Work :=
  ⟨cursor before todo,Counter.marked index,pre⟩

def emitted (b : Bool) (row index : List Bool) : List Bool := if b then row++index else []

def positions (pos : Port → ℤ) (r o : ℤ) : Port → ℤ :=
  fun p => pos p + if p=.stream then r else if p=.output then o else 0

theorem positions_zero (pos : Port → ℤ) : positions pos 0 0=pos := by
  funext p; cases p <;> simp [positions]

theorem positions_add (pos : Port → ℤ) (r o r' o' : ℤ) :
    positions (positions pos r o) r' o'=positions pos (r+r') (o+o') := by
  funext p; cases p <;> simp [positions,add_assoc]

theorem positions_output (pos : Port → ℤ) (o : ℤ) :
    Function.update pos .output (pos .output+o)=positions pos 0 o := by
  funext p; cases p <;> simp [positions]

theorem cursor_initial (xs : List Bool) : cursor [] xs=Counter.marked xs := rfl

theorem cursor_final (xs : List Bool) : cursor xs []=RowStream.closedTape xs := by
  simp [cursor,RowStream.closedTape,symbols,List.map_reverse]

theorem cursor_advance (before todo : List Bool) (b : Bool) :
    (cursor before (b::todo)).moveRight=cursor (before++[b]) todo := by
  simp [cursor,Tape.moveRight,Tape.read,symbols,List.reverse_append]

theorem encoded_cons (row unit index bs : List Bool) (b : Bool) :
    encoded row unit (b::bs) index = emitted b row index ++
      encoded row unit bs (RepeatedAdd.addWord index unit) := by
  cases b <;> simp [encoded,records,emitted]

theorem after_cons (unit index bs : List Bool) (b : Bool) :
    after unit (b::bs) index=after unit bs (RepeatedAdd.addWord index unit) := rfl

theorem one_step (pc next : Label) (row unit : List Bool) (s z : Work)
    (pos pos' : Port → ℤ) (ha : program pc≠.halt ∧ program pc≠.reject)
    (he : NativeZipper.step program (zipperCfg pc row unit s pos)=zipperCfg next row unit z pos') :
    Trace 1 (cfg pc row unit s pos) (cfg next row unit z pos') := by
  have h := congrArg NativeZipper.Config.denote he
  rw [NativeZipper.step_denote] at h
  change NativeMicrocode.step program (cfg pc row unit s pos)=cfg next row unit z pos' at h
  apply OperationalTrace.Trace.cons
  · exact ha
  · rw [h]; exact .refl _

theorem read_flag (row unit before todo index : List Bool) (b : Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    Trace 1 (cfg .scan row unit (work before (b::todo) index pre) pos)
      (cfg (if b then .append false 0 else .increment (.counter 0)) row unit
        (work before (b::todo) index pre) pos) := by
  apply one_step
  · exact ⟨by simp [program],by simp [program]⟩
  · cases b <;> simp [NativeZipper.step,Microcode.step,program,zipperCfg,bank,work,cursor,Tape.read,symbols]

theorem read_stop (row unit before index : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    Trace 1 (cfg .scan row unit (work before [] index pre) pos)
      (cfg (.erase false 4) row unit (work before [] index pre) pos) := by
  apply one_step
  · exact ⟨by simp [program],by simp [program]⟩
  · simp [NativeZipper.step,Microcode.step,program,zipperCfg,bank,work,cursor,Tape.read,symbols]

theorem advance_tapes (row unit before todo index : List Bool) (b : Bool) (pre : List (Sym Bool)) :
    (fun p => (Microcode.single Port.stream ⟨none,.right⟩ p).apply
      (bank row unit (work before (b::todo) index pre) p))=
      bank row unit (work (before++[b]) todo index pre) := by
  funext p; cases p <;> try rfl
  exact cursor_advance before todo b

theorem advance_positions (pos : Port → ℤ) :
    (fun p => (NativeMicrocode.direction (Microcode.single Port.stream ⟨none,.right⟩ p).move).shift (pos p))=
      positions pos 1 0 := by
  funext p; cases p <;> simp [positions,Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift]

theorem advance_trace (row unit before todo index : List Bool) (b : Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    Trace 1 (cfg .advance row unit (work before (b::todo) index pre) pos)
      (cfg .scan row unit (work (before++[b]) todo index pre) (positions pos 1 0)) := by
  apply one_step
  · exact ⟨by simp [program],by simp [program]⟩
  · simp only [NativeZipper.step,Microcode.step,program,zipperCfg,advance_tapes,advance_positions]

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem append_pair (row unit index : List Bool) (hr : row.length=unit.length)
    (hj : index.length=unit.length) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 8*unit.length+12, Trace t
      (cfg (.append false 0) row unit {s with index:=Counter.marked index} pos)
      (cfg (.increment (.counter 0)) row unit
        {s with index:=Counter.marked index,pre:=(symbols (row++index)).reverse++s.pre}
        (positions pos 0 (row.length+index.length))) := by
  obtain ⟨a,ha,ta⟩ := append_call false row unit index s pos
  simp only [sourceWord,Bool.false_eq_true,↓reduceIte,positions_output] at ha ta
  let s1 : Work := {s with index:=Counter.marked index,pre:=(symbols row).reverse++s.pre}
  let p1 := positions pos 0 row.length
  have ja := jump_trace (.append false 7) (.append true 0) row unit s1 p1 rfl
  obtain ⟨b,hb,tb⟩ := append_call true row unit index s1 p1
  simp only [sourceWord,↓reduceIte,positions_output] at hb tb
  let s2 : Work := {s1 with index:=Counter.marked index,pre:=(symbols index).reverse++s1.pre}
  let p2 := positions p1 0 index.length
  have jb := jump_trace (.append true 7) (.increment (.counter 0)) row unit s2 p2 rfl
  have whole := trace_trans (trace_trans (trace_trans ta ja) tb) jb
  refine ⟨a+1+b+1,by omega,?_⟩
  simpa only [s1,s2,p1,p2,positions_add,add_zero,symbols,List.map_append,List.reverse_append,List.append_assoc] using whole

theorem flag_trace (row unit before todo index : List Bool) (b : Bool)
    (hr : row.length=unit.length) (hj : index.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 18*unit.length+54+(if b then 8*unit.length+12 else 0), Trace t
      (cfg .scan row unit (work before (b::todo) index pre) pos)
      (cfg .scan row unit (work (before++[b]) todo (RepeatedAdd.addWord index unit)
        ((symbols (emitted b row index)).reverse++pre))
        (positions pos 1 (emitted b row index).length)) := by
  let s := work before (b::todo) index pre
  have rd := read_flag row unit before todo index b pre pos
  cases b with
  | false =>
    obtain ⟨a,ha,ta⟩ := increment_call row unit index hj s pos
    let s1 := work before (false::todo) (RepeatedAdd.addWord index unit) pre
    have ja := jump_trace (.increment (.counter 12)) .advance row unit s1 pos rfl
    have mv := advance_trace row unit before todo (RepeatedAdd.addWord index unit) false pre pos
    have whole := trace_trans (trace_trans (trace_trans rd ta) ja) mv
    exact ⟨1+a+1+1,by simp; omega,by simpa only [emitted,Bool.false_eq_true,↓reduceIte,symbols,
      List.map_nil,List.reverse_nil,List.nil_append,List.length_nil,Nat.cast_zero] using whole⟩
  | true =>
    obtain ⟨a,ha,ta⟩ := append_pair row unit index hr hj s pos
    let pre1 := (symbols (row++index)).reverse++pre
    let s1 := work before (true::todo) index pre1
    let p1 := positions pos 0 (row.length+index.length)
    obtain ⟨c,hc,tc⟩ := increment_call row unit index hj s1 p1
    let s2 := work before (true::todo) (RepeatedAdd.addWord index unit) pre1
    have jc := jump_trace (.increment (.counter 12)) .advance row unit s2 p1 rfl
    have mv := advance_trace row unit before todo (RepeatedAdd.addWord index unit) true pre1 p1
    have whole := trace_trans (trace_trans (trace_trans (trace_trans rd ta) tc) jc) mv
    refine ⟨1+a+c+1+1,by simp; omega,?_⟩
    simpa only [emitted,↓reduceIte,pre1,p1,positions_add,zero_add,add_zero,List.length_append,Nat.cast_add] using whole

def loopBudget (m : ℕ) (flags : List Bool) : ℕ :=
  flags.length*(18*m+54)+flags.count true*(8*m+12)

theorem loop_trace (row unit before flags index : List Bool) (hr : row.length=unit.length)
    (hj : index.length=unit.length) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ loopBudget unit.length flags, Trace t
      (cfg .scan row unit (work before flags index pre) pos)
      (cfg .scan row unit (work (before++flags) [] (after unit flags index)
        ((symbols (encoded row unit flags index)).reverse++pre))
        (positions pos flags.length (encoded row unit flags index).length)) := by
  induction flags generalizing before index pre pos with
  | nil =>
    refine ⟨0,by simp [loopBudget],?_⟩
    simpa only [after,RepeatedAdd.repeatWord,encoded,records,List.flatMap_nil,symbols,List.map_nil,
      List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,Nat.cast_zero,positions_zero] using
      (OperationalTrace.Trace.refl (cfg .scan row unit (work before [] index pre) pos) : Trace 0 _ _)
  | cons b bs ih =>
    obtain ⟨a,ha,ta⟩ := flag_trace row unit before bs index b hr hj pre pos
    obtain ⟨c,hc,tc⟩ := ih (before++[b]) (RepeatedAdd.addWord index unit)
      (RepeatedAdd.addWord_length index unit hj) ((symbols (emitted b row index)).reverse++pre)
      (positions pos 1 (emitted b row index).length)
    refine ⟨a+c,?_,?_⟩
    · cases b <;> simp [loopBudget] at ha hc ⊢ <;> nlinarith
    · have whole := trace_trans ta tc
      simpa only [encoded_cons,after_cons,positions_add,List.length_cons,Nat.cast_add,Nat.cast_one,
        symbols,List.map_append,List.reverse_append,List.append_assoc,List.singleton_append,List.length_append,
        add_comm] using whole

end TransposeFollowup.RowConsumer
