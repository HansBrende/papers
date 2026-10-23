import TransposeFollowup.NativeMatchingXorMaskRow

/-! A physical binary counter controls opcode-row demultiplexing. Neither
row count nor opcode contents occur in the control type. The counter's
final underflow, each row-call jump and the return jumps are paid. -/
namespace TransposeFollowup.NativeMatchingXorMasks
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
abbrev Port (q : ℕ) := Option (NativeMatchingXorMaskRow.Port q)
inductive Label (q : ℕ)
  | count (pc : Microcode.DecrementFamily.Label)
  | row (pc : NativeMatchingXorMaskRow.Label q)
  deriving DecidableEq, Fintype

def counterBinding : FinitePortBinding (Fin 1) (Port q) where
  ports := ⟨fun _ => none,by intro a b _; exact Subsingleton.elim _ _⟩
  decode := fun p => match p with | none => some 0 | some _ => none
  decode_spec := by intro p t; fin_cases t; cases p <;> simp <;> rfl

def rowBinding : FinitePortBinding (NativeMatchingXorMaskRow.Port q) (Port q) where
  ports := ⟨some,Option.some_injective _⟩
  decode := fun p => match p with | none => none | some p => some p
  decode_spec := by intro p t; cases p <;> simp [eq_comm]

def program (reverse : Bool) : Microcode.Program (Port q) (Label q)
  | .count pc => if pc=11 then .jump (.row (.read ⟨0,by omega⟩))
      else counterBinding.instruction Label.count (Microcode.DecrementFamily.program pc)
  | .row .done => .jump (.count 0)
  | .row pc => rowBinding.instruction Label.row (NativeMatchingXorMaskRow.program reverse pc)

theorem counter_code (reverse : Bool) (pc : Microcode.DecrementFamily.Label)
    (hh : Microcode.DecrementFamily.program pc≠.halt)
    (_ : Microcode.DecrementFamily.program pc≠.reject) :
    program (q:=q) reverse (.count pc)=MicrocodeEmbedding.instruction counterBinding.ports Label.count
      (Microcode.DecrementFamily.program pc) := by
  have hn : pc≠11 := fun h => by subst pc; exact hh rfl
  simp [program,hn,FinitePortBinding.instruction_eq]

theorem row_code (reverse : Bool) (pc : NativeMatchingXorMaskRow.Label q)
    (hh : NativeMatchingXorMaskRow.program reverse pc≠.halt)
    (_ : NativeMatchingXorMaskRow.program reverse pc≠.reject) :
    program reverse (.row pc)=MicrocodeEmbedding.instruction rowBinding.ports Label.row
      (NativeMatchingXorMaskRow.program reverse pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def bank (counter : List Bool) (input : Tape Bool) (out : Fin q → Tape Bool) : Port q → Tape Bool
  | none => Counter.marked counter
  | some p => NativeMatchingXorMaskRow.bank input out p

def cfg (pc : Label q) (counter : List Bool) (input : Tape Bool) (out : Fin q → Tape Bool)
    (pos : Port q → ℤ) : NativeZipper.Config (Port q) (Label q) := ⟨⟨pc,bank counter input out⟩,pos⟩
def frame (counter : List Bool) (input : Tape Bool) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    MicrocodeEmbedding.Frame (Port q) := ⟨fun p => (bank counter input out p).denote,pos⟩

def advance (reverse : Bool) (pos : Port q → ℤ) : Port q → ℤ
  | none => pos none
  | some p => NativeMatchingXorMaskRow.advanceMany reverse 0 q (fun a => pos (some a)) p

def encode (rows : List (List (Bool×Bool))) := rows.flatMap NativeMatchingXorMaskRow.encode

def writeMany (reverse : Bool) : List (List (Bool×Bool)) → (Fin q → Tape Bool) → (Fin q → Tape Bool)
  | [], out => out
  | xs::rows, out => writeMany reverse rows (NativeMatchingXorMaskRow.writeMany reverse 0 xs out)

def advanceMany (reverse : Bool) : ℕ → (Port q → ℤ) → (Port q → ℤ)
  | 0,pos => pos
  | n+1,pos => advanceMany reverse n (advance reverse pos)

abbrev Trace (reverse : Bool) := OperationalTrace.Trace (NativeMicrocode.step (program (q:=q) reverse))
  (NativeMicrocode.Active (program reverse))

theorem embed_counter (pc : Microcode.DecrementFamily.Label) (xs base : List Bool)
    (input : Tape Bool) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    MicrocodeEmbedding.embed counterBinding.ports Label.count
      (NativeCounter.cfg pc xs (fun _ => pos none)).denote (frame base input out pos)=
      (cfg (.count pc) xs input out pos).denote := by
  unfold MicrocodeEmbedding.embed NativeCounter.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← counterBinding.values_eq_extend]
  congr 2
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl

theorem decrement_call (reverse : Bool) (xs : List Bool) (input : Tape Bool)
    (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 2*Counter.stepCost xs, Trace reverse t (cfg (.count 0) xs input out pos).denote
      (cfg (.count (NativeCounter.returnLabel xs)) (Counter.decrement xs) input out pos).denote := by
  obtain ⟨t,ht,htr⟩ := NativeCounter.decrement_trace xs (fun _ => pos none)
  refine ⟨t,ht,?_⟩
  simpa only [embed_counter] using MicrocodeEmbedding.trace_embed counterBinding.ports
    Label.count Microcode.DecrementFamily.program (program reverse) (frame xs input out pos)
    (counter_code reverse) htr

theorem embed_row (pc : NativeMatchingXorMaskRow.Label q) (counter : List Bool)
    (input baseInput : Tape Bool) (out baseOut : Fin q → Tape Bool)
    (pos : Port q → ℤ) (rp : NativeMatchingXorMaskRow.Port q → ℤ) :
    MicrocodeEmbedding.embed rowBinding.ports Label.row
      (NativeMatchingXorMaskRow.cfg pc input out rp).denote (frame counter baseInput baseOut pos)=
      (cfg (.row pc) counter input out (rowBinding.values rp pos)).denote := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorMaskRow.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← rowBinding.values_eq_extend]
  congr 2
  funext p; cases p <;> rfl

theorem row_call (reverse : Bool) (xs : List (Bool×Bool)) (hx : xs.length=q)
    (counter : List Bool) (il ir : List (Sym Bool)) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 3*q+1, Trace reverse t
      (cfg (.row (.read ⟨0,by omega⟩)) counter ⟨il,symbols (NativeMatchingXorMaskRow.encode xs)++ir⟩ out pos).denote
      (cfg (.row .done) counter ⟨(symbols (NativeMatchingXorMaskRow.encode xs)).reverse++il,ir⟩
        (NativeMatchingXorMaskRow.writeMany reverse 0 xs out) (advance reverse pos)).denote := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorMaskRow.row_trace reverse xs hx il ir out (fun p => pos (some p))
  have hi : rowBinding.values (fun p => pos (some p)) pos=pos := by funext p; cases p <;> rfl
  have hf : rowBinding.values (NativeMatchingXorMaskRow.advanceMany reverse 0 q (fun p => pos (some p))) pos=
      advance reverse pos := by funext p; cases p <;> rfl
  refine ⟨t,ht,?_⟩
  simpa only [embed_row,hi,hf] using MicrocodeEmbedding.trace_embed rowBinding.ports Label.row
    (NativeMatchingXorMaskRow.program reverse) (program reverse)
    (frame counter ⟨il,symbols (NativeMatchingXorMaskRow.encode xs)++ir⟩ out pos) (row_code reverse) htr

theorem jump_trace (reverse : Bool) (a b : Label q) (counter : List Bool) (input : Tape Bool)
    (out : Fin q → Tape Bool) (pos : Port q → ℤ) (h : program reverse a=.jump b) :
    Trace reverse 1 (cfg a counter input out pos).denote (cfg b counter input out pos).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,h]
  · rw [← NativeZipper.step_denote]
    have hs : NativeZipper.step (program reverse) (cfg a counter input out pos)=cfg b counter input out pos := by
      simp [NativeZipper.step,Microcode.step,cfg,h]
    rw [hs]
    exact .refl _

theorem rows_trace (reverse : Bool) (rows : List (List (Bool×Bool)))
    (hr : ∀ xs∈rows,xs.length=q) (counter : List Bool) (hv : Counter.value counter=rows.length)
    (il ir : List (Sym Bool)) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 2*Counter.totalCost (rows.length+1) counter+rows.length*(3*q+3), Trace reverse t
      (cfg (.count 0) counter ⟨il,symbols (encode rows)++ir⟩ out pos).denote
      (cfg (.count 12) (Counter.wordAfter (rows.length+1) counter)
        ⟨(symbols (encode rows)).reverse++il,ir⟩ (writeMany reverse rows out)
        (advanceMany reverse rows.length pos)).denote := by
  induction rows generalizing counter il out pos with
  | nil =>
    have hz : Counter.isZero counter=true := (Counter.value_zero_iff counter).mp (by simpa using hv)
    obtain ⟨t,ht,htr⟩ := decrement_call reverse counter ⟨il,ir⟩ out pos
    refine ⟨t,?_,?_⟩
    · simpa [Counter.totalCost] using ht
    · simpa [NativeCounter.returnLabel,hz,encode,symbols,writeMany,advanceMany,Counter.wordAfter] using htr
  | cons xs rows ih =>
    have hx : xs.length=q := hr xs (by simp)
    have hr' : ∀x∈rows,x.length=q := by intro x h; exact hr x (by simp [h])
    have hz : Counter.isZero counter=false := by
      cases he : Counter.isZero counter
      · rfl
      · have hzero := (Counter.value_zero_iff counter).mpr he
        simp at hv; omega
    have hv' : Counter.value (Counter.decrement counter)=rows.length := by
      have hh := Counter.decrement_value counter hz
      simp at hv; omega
    obtain ⟨a,ha,ta⟩ := decrement_call reverse counter
      ⟨il,symbols (encode (xs::rows))++ir⟩ out pos
    have tj := jump_trace reverse (.count 11) (.row (.read ⟨0,by omega⟩)) (Counter.decrement counter)
      ⟨il,symbols (encode (xs::rows))++ir⟩ out pos (by simp [program])
    obtain ⟨b,hb,tb⟩ := row_call reverse xs hx (Counter.decrement counter) il
      (symbols (encode rows)++ir) out pos
    have tr := jump_trace reverse (.row .done) (.count 0) (Counter.decrement counter)
      ⟨(symbols (NativeMatchingXorMaskRow.encode xs)).reverse++il,symbols (encode rows)++ir⟩
      (NativeMatchingXorMaskRow.writeMany reverse 0 xs out) (advance reverse pos) rfl
    obtain ⟨c,hc,tc⟩ := ih hr' (Counter.decrement counter) hv'
      ((symbols (NativeMatchingXorMaskRow.encode xs)).reverse++il)
      (NativeMatchingXorMaskRow.writeMany reverse 0 xs out) (advance reverse pos)
    refine ⟨a+1+b+1+c,?_,?_⟩
    · change a+1+b+1+c ≤ 2*(Counter.stepCost counter + Counter.totalCost (rows.length+1) (Counter.decrement counter)) + (rows.length+1)*(3*q+3)
      nlinarith
    · have ta' : Trace reverse a (cfg (.count 0) counter ⟨il,symbols (encode (xs::rows))++ir⟩ out pos).denote
          (cfg (.count 11) (Counter.decrement counter) ⟨il,symbols (encode (xs::rows))++ir⟩ out pos).denote := by
        simpa [NativeCounter.returnLabel,hz] using ta
      have tb' : Trace reverse b
          (cfg (.row (.read ⟨0,by omega⟩)) (Counter.decrement counter) ⟨il,symbols (encode (xs::rows))++ir⟩ out pos).denote
          (cfg (.row .done) (Counter.decrement counter)
            ⟨(symbols (NativeMatchingXorMaskRow.encode xs)).reverse++il,symbols (encode rows)++ir⟩
            (NativeMatchingXorMaskRow.writeMany reverse 0 xs out) (advance reverse pos)).denote := by
        simpa [encode,symbols,List.flatMap_cons,List.map_append,List.append_assoc] using tb
      have ht := NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
        (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta' tj) tb') tr) tc
      simpa only [encode,symbols,List.flatMap_cons,List.map_append,List.reverse_append,List.append_assoc,
        writeMany,advanceMany,List.length_cons,Counter.wordAfter] using ht

theorem complete_trace (reverse : Bool) (rows : List (List (Bool×Bool)))
    (hr : ∀ xs∈rows,xs.length=q) (counter : List Bool) (hv : Counter.value counter=rows.length)
    (il ir : List (Sym Bool)) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    ∃ t ≤ rows.length*(3*q+3)+8*(rows.length+1)+4*counter.length, Trace reverse t
      (cfg (.count 0) counter ⟨il,symbols (encode rows)++ir⟩ out pos).denote
      (cfg (.count 12) (List.replicate counter.length true)
        ⟨(symbols (encode rows)).reverse++il,ir⟩ (writeMany reverse rows out)
        (advanceMany reverse rows.length pos)).denote := by
  obtain ⟨t,ht,htr⟩ := rows_trace reverse rows hr counter hv il ir out pos
  have hc := NativeCounter.native_sequence_budget (rows.length+1) counter
  refine ⟨t,by omega,?_⟩
  simpa only [NativeCountedLoop.terminal_word rows.length counter hv] using htr

end TransposeFollowup.NativeMatchingXorMasks
