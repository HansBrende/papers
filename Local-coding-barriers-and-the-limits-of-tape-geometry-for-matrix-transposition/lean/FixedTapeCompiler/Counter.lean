import FixedTapeCompiler.CopyMachine

/-! A single-tape binary decrementer with explicit head-return cost.
The alphabet and control are fixed; no integer is held in free control.
Words are little-endian between START and STOP, with arbitrary fixed width.
Zero wraps to all ones and reports underflow. -/
namespace FixedTapeCompiler.Counter
open CopyMachine (Sym Tape symbols)

inductive Phase
  | borrow | back (underflow : Bool) | done (underflow : Bool) | reject
  deriving DecidableEq, Fintype

structure Config where
  phase : Phase
  tape : Tape Bool
  deriving DecidableEq

def step (c : Config) : Config :=
  match c.phase with
  | .done _ | .reject => c
  | .borrow =>
    match c.tape.read with
    | .data false => ⟨.borrow, (c.tape.write (.data true)).moveRight⟩
    | .data true => ⟨.back false, (c.tape.write (.data false)).moveLeft⟩
    | .stop => ⟨.back true, c.tape.moveLeft⟩
    | _ => ⟨.reject, c.tape⟩
  | .back flag =>
    match c.tape.read with
    | .start => ⟨.done flag, c.tape.moveRight⟩
    | _ => ⟨.back flag, c.tape.moveLeft⟩

def run : ℕ → Config → Config
  | 0, c => c
  | n+1, c => run n (step c)

theorem run_add (n k : ℕ) (c : Config) : run (n+k) c = run k (run n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simp only [Nat.succ_add, run, ih]

def marked (xs : List Bool) : Tape Bool := ⟨[.start], symbols xs ++ [.stop]⟩
def initial (xs : List Bool) : Config := ⟨.borrow, marked xs⟩
def finished (flag : Bool) (xs : List Bool) : Config := ⟨.done flag, marked xs⟩

theorem rewind_left (pre : List Bool) (suffix : List (Sym Bool)) (flag : Bool) :
    run (pre.length+1)
      ⟨.back flag, (⟨symbols pre ++ [.start], suffix⟩ : Tape Bool).moveLeft⟩ =
    ⟨.done flag, ⟨[.start], symbols pre.reverse ++ suffix⟩⟩ := by
  induction pre generalizing suffix with
  | nil => simp [run, step, symbols, Tape.moveLeft, Tape.moveRight, Tape.read]
  | cons a ps ih =>
    change run (ps.length+1) (step
      ⟨.back flag, (⟨symbols (a::ps) ++ [.start], suffix⟩ : Tape Bool).moveLeft⟩) = _
    have hs : step
        ⟨.back flag, (⟨symbols (a::ps) ++ [.start], suffix⟩ : Tape Bool).moveLeft⟩ =
        ⟨.back flag, (⟨symbols ps ++ [.start], .data a :: suffix⟩ : Tape Bool).moveLeft⟩ := by
      simp [step, symbols, Tape.moveLeft, Tape.read]
    rw [hs]
    simpa [symbols, List.reverse_cons, List.map_append, List.append_assoc] using
      ih (.data a :: suffix)

theorem borrow_zeros (n : ℕ) (pre suffix : List (Sym Bool)) :
    run n ⟨.borrow, ⟨pre, List.replicate n (.data false) ++ suffix⟩⟩ =
      ⟨.borrow, ⟨List.replicate n (.data true) ++ pre, suffix⟩⟩ := by
  induction n generalizing pre with
  | zero => simp [run]
  | succ n ih =>
    change run n (step ⟨.borrow,
      ⟨pre, List.replicate (n+1) (.data false) ++ suffix⟩⟩) = _
    have hp : List.replicate n (Sym.data true) ++ .data true :: pre =
        Sym.data true :: (List.replicate n (Sym.data true) ++ pre) := by
      calc
        _ = (List.replicate n (Sym.data true) ++ [.data true]) ++ pre := by simp
        _ = List.replicate (n+1) (Sym.data true) ++ pre := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ]; rfl
    simpa [List.replicate_succ, step, Tape.read, Tape.write, Tape.moveRight, hp]
      using ih (.data true :: pre)

theorem nonzero_exact (n : ℕ) (xs : List Bool) :
    run (2*n+2) (initial (List.replicate n false ++ true::xs)) =
      finished false (List.replicate n true ++ false::xs) := by
  have hb := borrow_zeros n [Sym.start] (Sym.data true :: (symbols xs ++ [Sym.stop]))
  have hr := rewind_left (List.replicate n true)
    (Sym.data false :: (symbols xs ++ [Sym.stop])) false
  rw [show 2*n+2 = n+(1+(n+1)) by omega, run_add]
  have hf : run n (initial (List.replicate n false ++ true::xs)) =
      ⟨.borrow, ⟨List.replicate n (.data true) ++ [.start],
        .data true :: (symbols xs ++ [.stop])⟩⟩ := by
    simpa [initial, marked, symbols, List.map_append, List.map_replicate] using hb
  rw [hf, run_add]
  change run (n+1)
    ⟨.back false, (⟨List.replicate n (.data true) ++ [.start],
      .data false :: (symbols xs ++ [.stop])⟩ : Tape Bool).moveLeft⟩ = _
  simpa [finished, marked, symbols, List.map_append, List.map_replicate,
    List.reverse_replicate] using hr

theorem underflow_exact (n : ℕ) :
    run (2*n+2) (initial (List.replicate n false)) =
      finished true (List.replicate n true) := by
  have hb := borrow_zeros n [Sym.start] [Sym.stop]
  have hr := rewind_left (List.replicate n true) [Sym.stop] true
  rw [show 2*n+2 = n+(1+(n+1)) by omega, run_add]
  have hf : run n (initial (List.replicate n false)) =
      ⟨.borrow, ⟨List.replicate n (.data true) ++ [.start], [.stop]⟩⟩ := by
    simpa [initial, marked, symbols, List.map_replicate] using hb
  rw [hf, run_add]
  change run (n+1)
    ⟨.back true, (⟨List.replicate n (.data true) ++ [.start], [.stop]⟩ : Tape Bool).moveLeft⟩ = _
  simpa [finished, marked, symbols, List.map_replicate, List.reverse_replicate] using hr

def decrement : List Bool → List Bool
  | [] => []
  | false::xs => true::decrement xs
  | true::xs => false::xs

def trailingZeros : List Bool → ℕ
  | [] => 0
  | false::xs => trailingZeros xs+1
  | true::_ => 0

def isZero : List Bool → Bool
  | [] => true
  | false::xs => isZero xs
  | true::_ => false

def zeroCount : List Bool → ℕ
  | [] => 0
  | false::xs => zeroCount xs+1
  | true::xs => zeroCount xs

def value : List Bool → ℕ
  | [] => 0
  | false::xs => 2*value xs
  | true::xs => 2*value xs+1

def stepCost (xs : List Bool) : ℕ := 2*trailingZeros xs+2

theorem length_decrement (xs : List Bool) : (decrement xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [decrement, ih]

theorem zeroCount_le_length (xs : List Bool) : zeroCount xs ≤ xs.length := by
  induction xs with
  | nil => simp [zeroCount]
  | cons a xs ih => cases a <;> simp [zeroCount] <;> omega

theorem value_zero_iff (xs : List Bool) : value xs = 0 ↔ isZero xs = true := by
  induction xs with
  | nil => simp [value, isZero]
  | cons a xs ih => cases a <;> simp [value, isZero, ih]

theorem nonzero_prefix (xs : List Bool) (h : isZero xs = false) :
    ∃ n ys, xs = List.replicate n false ++ true::ys := by
  induction xs with
  | nil => simp [isZero] at h
  | cons a xs ih =>
    cases a with
    | true => exact ⟨0,xs,rfl⟩
    | false =>
      rcases ih h with ⟨n,ys,hn⟩
      exact ⟨n+1,ys,by simp [List.replicate_succ,hn]⟩

theorem zero_replicate (xs : List Bool) (h : isZero xs = true) :
    xs = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | true => simp [isZero] at h
    | false => simpa [List.replicate_succ] using congrArg (List.cons false) (ih h)

theorem prefix_functions (n : ℕ) (xs : List Bool) :
    decrement (List.replicate n false ++ true::xs) = List.replicate n true ++ false::xs ∧
    trailingZeros (List.replicate n false ++ true::xs) = n := by
  induction n with
  | zero => simp [decrement, trailingZeros]
  | succ n ih => simp [List.replicate_succ, decrement, trailingZeros, ih]

theorem zero_functions (n : ℕ) :
    decrement (List.replicate n false) = List.replicate n true ∧
    trailingZeros (List.replicate n false) = n := by
  induction n with
  | zero => simp [decrement, trailingZeros]
  | succ n ih => simp [List.replicate_succ, decrement, trailingZeros, ih]

theorem decrement_exact (xs : List Bool) :
    run (stepCost xs) (initial xs) = finished (isZero xs) (decrement xs) := by
  cases h : isZero xs with
  | false =>
    rcases nonzero_prefix xs h with ⟨n,ys,rfl⟩
    simpa only [h, stepCost, (prefix_functions n ys).1, (prefix_functions n ys).2]
      using nonzero_exact n ys
  | true =>
    have hz := zero_replicate xs h
    have hd : decrement xs = List.replicate xs.length true := by
      conv_lhs => rw [hz]
      exact (zero_functions xs.length).1
    have hc : trailingZeros xs = xs.length := by
      conv_lhs => rw [hz]
      exact (zero_functions xs.length).2
    rw [stepCost, hc, hd]
    conv_lhs => arg 2; rw [hz]
    exact underflow_exact xs.length

theorem decrement_value (xs : List Bool) (h : isZero xs = false) :
    value (decrement xs)+1 = value xs := by
  induction xs with
  | nil => simp [isZero] at h
  | cons a xs ih =>
    cases a with
    | true => simp [decrement, value]
    | false =>
      have hi := ih h
      simp only [decrement, value]
      omega

/-- Includes underflow: its amortized charge is smaller, not larger. -/
theorem amortized_step (xs : List Bool) :
    stepCost xs + 2*zeroCount (decrement xs) ≤ 4+2*zeroCount xs := by
  induction xs with
  | nil => simp [stepCost, trailingZeros, decrement, zeroCount]
  | cons a xs ih =>
    cases a <;> simp only [stepCost, trailingZeros, decrement, zeroCount] at * <;> omega

def wordAfter : ℕ → List Bool → List Bool
  | 0, xs => xs
  | n+1, xs => wordAfter n (decrement xs)

def totalCost : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n+1, xs => stepCost xs + totalCost n (decrement xs)

theorem amortized_sequence (n : ℕ) (xs : List Bool) :
    totalCost n xs + 2*zeroCount (wordAfter n xs) ≤ 4*n+2*zeroCount xs := by
  induction n generalizing xs with
  | zero => simp [totalCost, wordAfter]
  | succ n ih =>
    have hi := ih (decrement xs)
    have hs := amortized_step xs
    simp only [totalCost, wordAfter]
    omega

theorem sequence_cost (n : ℕ) (xs : List Bool) :
    totalCost n xs ≤ 4*n+2*xs.length := by
  have h := amortized_sequence n xs
  have hz := zeroCount_le_length xs
  omega

structure ConcreteConfig where
  phase : Phase
  tape : Turing.Tape (Sym Bool)

def Config.denote (c : Config) : ConcreteConfig := ⟨c.phase,c.tape.denote⟩

def concreteStep (c : ConcreteConfig) : ConcreteConfig :=
  match c.phase with
  | .done _ | .reject => c
  | .borrow =>
    match c.tape.head with
    | .data false => ⟨.borrow, (c.tape.write (.data true)).move .right⟩
    | .data true => ⟨.back false, (c.tape.write (.data false)).move .left⟩
    | .stop => ⟨.back true, c.tape.move .left⟩
    | _ => ⟨.reject, c.tape⟩
  | .back flag =>
    match c.tape.head with
    | .start => ⟨.done flag, c.tape.move .right⟩
    | _ => ⟨.back flag, c.tape.move .left⟩

theorem step_refines (c : Config) : (step c).denote = concreteStep c.denote := by
  cases c with
  | mk phase tape =>
    cases phase <;> cases h : tape.read <;>
      simp [step, Config.denote, concreteStep, h]
    case borrow.data a => cases a <;> simp

def concreteRun : ℕ → ConcreteConfig → ConcreteConfig
  | 0, c => c
  | n+1, c => concreteRun n (concreteStep c)

theorem run_refines (n : ℕ) (c : Config) :
    (run n c).denote = concreteRun n c.denote := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [run, concreteRun, ih, step_refines]

theorem decrement_actual_tape (xs : List Bool) :
    concreteRun (stepCost xs) (initial xs).denote =
      (finished (isZero xs) (decrement xs)).denote := by
  rw [← run_refines, decrement_exact]

theorem fixed_resources : Fintype.card Phase = 6 ∧ Fintype.card (Sym Bool) = 5 := by decide

end FixedTapeCompiler.Counter
