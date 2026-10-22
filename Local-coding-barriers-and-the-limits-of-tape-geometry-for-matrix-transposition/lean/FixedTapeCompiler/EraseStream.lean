import FixedTapeCompiler.OperationalTrace
import FixedTapeCompiler.CopyMachine

/-! Single-tape local erasure from either stream endpoint. The machine
does not cross the START marker. Cells before that marker are preserved.
Every visited payload or marker cell is changed to blank by a real write. -/
namespace FixedTapeCompiler.EraseStream
open CopyMachine (Sym Tape symbols)

inductive Phase | scan | begin | back | done | reject
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.scan,.begin,.back,.done,.reject}
  complete := by intro x; cases x <;> simp

structure Config where
  phase : Phase
  tape : Tape Bool

def step (c : Config) : Config :=
  match c.phase with
  | .done | .reject => c
  | .begin => ⟨.back,(c.tape.write .blank).moveLeft⟩
  | .scan => match c.tape.read with
    | .data _ => ⟨.scan,c.tape.moveRight⟩
    | .stop => ⟨.back,(c.tape.write .blank).moveLeft⟩
    | _ => ⟨.reject,c.tape⟩
  | .back => match c.tape.read with
    | .start => ⟨.done,(c.tape.write .blank).moveRight⟩
    | .data _ => ⟨.back,(c.tape.write .blank).moveLeft⟩
    | _ => ⟨.reject,c.tape⟩

abbrev run := OperationalTrace.run step

theorem run_add (n k : ℕ) (c : Config) : run (n+k) c = run k (run n c) :=
  OperationalTrace.run_add step n k c

theorem erase_back (pre : List Bool) (ancestor suffix : List (Sym Bool)) :
    run (pre.length+1)
      ⟨.back,(⟨symbols pre++(.start::ancestor),suffix⟩ : Tape Bool).moveLeft⟩ =
      ⟨.done,⟨.blank::ancestor,List.replicate pre.length .blank++suffix⟩⟩ := by
  induction pre generalizing suffix with
  | nil => simp [run,OperationalTrace.run,step,symbols,Tape.moveLeft,Tape.moveRight,Tape.write,Tape.read]
  | cons a pre ih =>
    change run (pre.length+1) (step
      ⟨.back,(⟨symbols (a::pre)++(.start::ancestor),suffix⟩ : Tape Bool).moveLeft⟩) = _
    have hs : step
        ⟨.back,(⟨symbols (a::pre)++(.start::ancestor),suffix⟩ : Tape Bool).moveLeft⟩ =
        ⟨.back,(⟨symbols pre++(.start::ancestor),.blank::suffix⟩ : Tape Bool).moveLeft⟩ := by
      simp [step,symbols,Tape.moveLeft,Tape.write,Tape.read]
    rw [hs,ih]
    simp [List.replicate_succ',List.append_assoc]

def initialEnd (xs : List Bool) (ancestor : List (Sym Bool)) : Config :=
  ⟨.begin,⟨(symbols xs).reverse++(.start::ancestor),[.stop]⟩⟩

def initial (xs : List Bool) (ancestor : List (Sym Bool)) : Config :=
  ⟨.scan,⟨.start::ancestor,symbols xs++[.stop]⟩⟩

def finished (n : ℕ) (ancestor : List (Sym Bool)) : Config :=
  ⟨.done,⟨.blank::ancestor,List.replicate (n+1) .blank⟩⟩

theorem erase_end_exact (xs : List Bool) (ancestor : List (Sym Bool)) :
    run (xs.length+2) (initialEnd xs ancestor) = finished xs.length ancestor := by
  have he := erase_back xs.reverse ancestor [.blank]
  change run (xs.length+1) (step (initialEnd xs ancestor)) = _
  simpa [initialEnd,finished,step,Tape.write,symbols,List.map_reverse,List.replicate_succ'] using he

theorem scan_to_end (xs : List Bool) (pre : List (Sym Bool)) :
    run xs.length ⟨.scan,⟨pre,symbols xs++[.stop]⟩⟩ =
      ⟨.scan,⟨(symbols xs).reverse++pre,[.stop]⟩⟩ := by
  induction xs generalizing pre with
  | nil => simp [run,OperationalTrace.run,symbols]
  | cons a xs ih =>
    simpa [run,OperationalTrace.run,step,symbols,Tape.read,Tape.moveRight,
      List.reverse_cons,List.append_assoc] using ih (.data a::pre)

theorem erase_exact (xs : List Bool) (ancestor : List (Sym Bool)) :
    run (2*xs.length+2) (initial xs ancestor) = finished xs.length ancestor := by
  rw [show 2*xs.length+2 = xs.length+(xs.length+2) by omega,run_add]
  change run (xs.length+2)
    (run xs.length ⟨.scan,⟨.start::ancestor,symbols xs++[.stop]⟩⟩) = _
  rw [scan_to_end]
  change run (xs.length+1) (step (initialEnd xs ancestor)) = _
  exact erase_end_exact xs ancestor

structure ConcreteConfig where
  phase : Phase
  tape : Turing.Tape (Sym Bool)

def Config.denote (c : Config) : ConcreteConfig := ⟨c.phase,c.tape.denote⟩

def concreteStep (c : ConcreteConfig) : ConcreteConfig :=
  match c.phase with
  | .done | .reject => c
  | .begin => ⟨.back,(c.tape.write .blank).move .left⟩
  | .scan => match c.tape.head with
    | .data _ => ⟨.scan,c.tape.move .right⟩
    | .stop => ⟨.back,(c.tape.write .blank).move .left⟩
    | _ => ⟨.reject,c.tape⟩
  | .back => match c.tape.head with
    | .start => ⟨.done,(c.tape.write .blank).move .right⟩
    | .data _ => ⟨.back,(c.tape.write .blank).move .left⟩
    | _ => ⟨.reject,c.tape⟩

theorem step_refines (c : Config) : (step c).denote = concreteStep c.denote := by
  rcases c with ⟨phase,tape⟩
  cases phase with
  | done => rfl
  | reject => rfl
  | «begin» => simp [step,Config.denote,concreteStep]
  | scan => cases h : tape.read <;> simp [step,Config.denote,concreteStep,h]
  | back => cases h : tape.read <;> simp [step,Config.denote,concreteStep,h]

abbrev concreteRun := OperationalTrace.run concreteStep

theorem run_refines (n : ℕ) (c : Config) : (run n c).denote = concreteRun n c.denote := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (run n (step c)).denote = concreteRun n (concreteStep c.denote)
    rw [ih,step_refines]

theorem blanks_eq_nil (n : ℕ) :
    Turing.ListBlank.mk (List.replicate n (Sym.blank : Sym Bool)) = Turing.ListBlank.mk [] := by
  apply Quotient.sound
  right
  exact ⟨n,rfl⟩

theorem finished_denote (n : ℕ) (ancestor : List (Sym Bool)) :
    (finished n ancestor).denote =
      ⟨.done,(⟨.blank::ancestor,[]⟩ : Tape Bool).denote⟩ := by
  simp [finished,Config.denote,Tape.denote,Turing.Tape.mk₂,blanks_eq_nil]

theorem erase_end_actual_tape (xs : List Bool) (ancestor : List (Sym Bool)) :
    concreteRun (xs.length+2) (initialEnd xs ancestor).denote =
      ⟨.done,(⟨.blank::ancestor,[]⟩ : Tape Bool).denote⟩ := by
  rw [← run_refines,erase_end_exact,finished_denote]

theorem erase_actual_tape (xs : List Bool) (ancestor : List (Sym Bool)) :
    concreteRun (2*xs.length+2) (initial xs ancestor).denote =
      ⟨.done,(⟨.blank::ancestor,[]⟩ : Tape Bool).denote⟩ := by
  rw [← run_refines,erase_exact,finished_denote]

theorem blank_origin : (⟨[.blank],[]⟩ : Tape Bool).denote = (⟨[],[]⟩ : Tape Bool).denote := by
  have h := blanks_eq_nil 1
  simpa [Tape.denote,Turing.Tape.mk₂] using congrArg
    (fun l => Turing.Tape.mk' l (Turing.ListBlank.mk ([] : List (Sym Bool)))) h

theorem erase_to_blank (xs : List Bool) :
    concreteRun (2*xs.length+2) (initial xs []).denote =
      ⟨.done,(⟨[],[]⟩ : Tape Bool).denote⟩ := by
  rw [erase_actual_tape,blank_origin]

theorem fixed_resources : Fintype.card Phase = 5 ∧ Fintype.card (Sym Bool) = 5 := by decide

end FixedTapeCompiler.EraseStream
