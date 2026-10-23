import TransposeFollowup.NativeSealBack

/-! Literal words selected from a fixed finite family are emitted by fixed
microcode.  No output tape contains a preloaded table or ruler. -/
namespace BitWord.NativeLiteralBank
open FixedTapeCompiler CopyMachine TransposeFollowup

inductive Label (H : Type*) (M : ℕ)
  | start (h : H) | mark (h : H) | write (h : H) (i : Fin (M+1))
  | stop (h : H) | back (h : H) (i : Fin (M+1)) | done (h : H)
  deriving DecidableEq, Fintype

variable {T H : Type*} (M : ℕ) (word : H → T → List Bool)

def program : Microcode.Program T (Label H M)
  | .start h => .act (fun _ => ⟨none,.left⟩) (.mark h)
  | .mark h => .act (fun _ => ⟨some .start,.right⟩) (.write h 0)
  | .write h i => if hi : i.val < M then
      .act (fun p => if hp : i.val < (word h p).length then
        ⟨some (.data ((word h p)[i.val])),.right⟩ else ⟨none,.stay⟩)
        (.write h ⟨i.val+1,by omega⟩)
    else .jump (.stop h)
  | .stop h => .act (fun _ => ⟨some .stop,.stay⟩) (.back h ⟨M,by omega⟩)
  | .back h i => if hi : 0 < i.val then
      .act (fun p => if i.val ≤ (word h p).length then ⟨none,.left⟩ else ⟨none,.stay⟩)
        (.back h ⟨i.val-1,by omega⟩)
    else .jump (.done h)
  | .done _ => .halt

def cfg (pc : Label H M) (bank : T → Tape Bool) (pos : T → ℤ) : NativeZipper.Config T (Label H M) :=
  ⟨⟨pc,bank⟩,pos⟩

def opened (h : H) (i : ℕ) : T → Tape Bool := fun p => NativeSealBack.openWord ((word h p).take i)
def sealed (h : H) (i : ℕ) : T → Tape Bool := fun p =>
  ⟨(symbols ((word h p).take i)).reverse++[.start],symbols ((word h p).drop i)++[.stop]⟩
def positions (h : H) (i : ℕ) (pos : T → ℤ) : T → ℤ :=
  fun p => pos p+min i (word h p).length

 theorem initialize_run (h : H) (pos : T → ℤ) :
     NativeZipper.run (program M word) 2 (cfg M (.start h) (fun _ => ⟨[],[]⟩) pos)=
       cfg M (.write h 0) (opened word h 0) (positions word h 0 pos) := by
   simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
     program,cfg,Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,Tape.write]
   constructor  <;> funext p  <;> simp [NativeMicrocode.direction,Transpose.Dir.shift,positions,opened,NativeSealBack.openWord,symbols,Tape.read]

 theorem write_step (h : H) (i : ℕ) (hi : i < M) (pos : T → ℤ) :
     NativeZipper.run (program M word) 1
       (cfg M (.write h ⟨i,by omega⟩) (opened word h i) (positions word h i pos))=
       cfg M (.write h ⟨i+1,by omega⟩) (opened word h (i+1)) (positions word h (i+1) pos) := by
   simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,hi,↓reduceDIte]
   congr 1
   · congr 1
     funext p
     by_cases hp : i < (word h p).length
     · simp only [hp,↓reduceDIte,opened,NativeSealBack.openWord,Microcode.Action.apply,Tape.write,Tape.moveRight]
       rw [List.take_succ_eq_append_getElem hp]
       simp only [symbols,List.map_append,List.map_cons,List.map_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,Tape.read,List.nil_append,List.cons_append]
       rfl
     · have hle : (word h p).length ≤ i := by omega
       simp [hp,opened,Microcode.Action.apply,List.take_of_length_le hle,
         List.take_of_length_le (by omega : (word h p).length ≤ i+1)]
   · funext p
     by_cases hp : i < (word h p).length
     · simp [hp,positions,NativeMicrocode.direction,Transpose.Dir.shift,
         Nat.min_eq_left (by omega : i ≤ (word h p).length)]
       omega
     · simp [hp,positions,NativeMicrocode.direction,Transpose.Dir.shift,
         Nat.min_eq_right (by omega : (word h p).length ≤ i),Nat.min_eq_right (by omega : (word h p).length ≤ i+1)]

 theorem write_run (h : H) (i : ℕ) (hi : i ≤ M) (pos : T → ℤ) :
     NativeZipper.run (program M word) i
       (cfg M (.write h 0) (opened word h 0) (positions word h 0 pos))=
       cfg M (.write h ⟨i,by omega⟩) (opened word h i) (positions word h i pos) := by
   induction i with
   | zero => rfl
   | succ i ih =>
     rw [NativeZipper.run_add,ih (by omega)]
     exact write_step M word h i (by omega) pos

 theorem back_step (h : H) (i : ℕ) (hi : i < M) (pos : T → ℤ) :
     NativeZipper.run (program M word) 1
       (cfg M (.back h ⟨i+1,by omega⟩) (sealed word h (i+1)) (positions word h (i+1) pos))=
       cfg M (.back h ⟨i,by omega⟩) (sealed word h i) (positions word h i pos) := by
   simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
     Nat.zero_lt_succ,↓reduceDIte,Nat.add_sub_cancel]
   congr 1
   · congr 1
     funext p
     by_cases hp : i < (word h p).length
     · have hh : i+1 ≤ (word h p).length := by omega
       simp only [hh,↓reduceIte,sealed,Microcode.Action.apply,Tape.moveLeft]
       rw [List.take_succ_eq_append_getElem hp,List.drop_eq_getElem_cons hp]
       simp only [symbols,List.map_append,List.map_cons,List.map_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.tail_cons]
       rfl
     · have hh : ¬i+1 ≤ (word h p).length := by omega
       have hle : (word h p).length ≤ i := by omega
       simp [hh,sealed,Microcode.Action.apply,List.take_of_length_le hle,
         List.take_of_length_le (by omega : (word h p).length ≤ i+1),
         List.drop_eq_nil_of_le hle,List.drop_eq_nil_of_le (by omega : (word h p).length ≤ i+1)]
   · funext p
     by_cases hp : i < (word h p).length
     · have hh : i+1 ≤ (word h p).length := by omega
       simp [hh,positions,NativeMicrocode.direction,Transpose.Dir.shift,
         Nat.min_eq_left (by omega : i ≤ (word h p).length)]
       omega
     · have hh : ¬i+1 ≤ (word h p).length := by omega
       simp [hh,positions,NativeMicrocode.direction,Transpose.Dir.shift,
         Nat.min_eq_right (by omega : (word h p).length ≤ i),Nat.min_eq_right (by omega : (word h p).length ≤ i+1)]

 theorem back_run (h : H) (i : ℕ) (hi : i ≤ M) (pos : T → ℤ) :
     NativeZipper.run (program M word) i
       (cfg M (.back h ⟨i,by omega⟩) (sealed word h i) (positions word h i pos))=
       cfg M (.back h 0) (sealed word h 0) (positions word h 0 pos) := by
   induction i with
   | zero => rfl
   | succ i ih =>
     conv_lhs => arg 2; rw [Nat.add_comm]
     rw [NativeZipper.run_add,back_step M word h i (by omega),ih (by omega)]

end BitWord.NativeLiteralBank

namespace BitWord.NativeLiteralBank
open FixedTapeCompiler CopyMachine TransposeFollowup
variable {T H : Type*} (M : ℕ) (word : H → T → List Bool)

 theorem write_end (h : H) (pos : T → ℤ) :
     NativeZipper.run (program M word) 1
       (cfg M (.write h ⟨M,by omega⟩) (opened word h M) (positions word h M pos))=
       cfg M (.stop h) (opened word h M) (positions word h M pos) := by
   simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg]

 theorem stop_run (h : H) (hlen : ∀ p,(word h p).length ≤ M) (pos : T → ℤ) :
     NativeZipper.run (program M word) 1
       (cfg M (.stop h) (opened word h M) (positions word h M pos))=
       cfg M (.back h ⟨M,by omega⟩) (sealed word h M) (positions word h M pos) := by
   simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg]
   congr 1
   · congr 1
     funext p
     simp [opened,sealed,NativeSealBack.openWord,Microcode.Action.apply,Tape.write,
       List.take_of_length_le (hlen p),List.drop_eq_nil_of_le (hlen p),symbols]

 theorem back_end (h : H) (pos : T → ℤ) :
     NativeZipper.run (program M word) 1
       (cfg M (.back h 0) (sealed word h 0) (positions word h 0 pos))=
       cfg M (.done h) (fun p => Counter.marked (word h p)) pos := by
   simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Counter.marked,symbols]
   constructor <;> funext p <;> simp [sealed,positions,symbols]

/-- A finite table is part of the machine's fixed transition function. All
emitted bits, markers and head returns are actual charged transitions. -/
 theorem complete_run (h : H) (hlen : ∀ p,(word h p).length ≤ M) (pos : T → ℤ) :
     NativeZipper.run (program M word) (2*M+5)
       (cfg M (.start h) (fun _ => ⟨[],[]⟩) pos)=
       cfg M (.done h) (fun p => Counter.marked (word h p)) pos := by
   rw [show 2*M+5=2+M+1+1+M+1 by omega]
   rw [NativeZipper.run_add,NativeZipper.run_add,NativeZipper.run_add,
     NativeZipper.run_add,NativeZipper.run_add,initialize_run,write_run M word h M le_rfl,
     write_end,stop_run M word h hlen,back_run M word h M le_rfl,back_end]

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step (program M word))
  (NativeMicrocode.Active (program M word))

 theorem complete_trace (h : H) (hlen : ∀ p,(word h p).length ≤ M) (pos : T → ℤ) :
     ∃ t ≤ 2*M+5, Trace M word t
       (cfg M (.start h) (fun _ => ⟨[],[]⟩) pos).denote
       (cfg M (.done h) (fun p => Counter.marked (word h p)) pos).denote :=
   NativeZipper.trace_of_run (program M word) (complete_run M word h hlen pos)

end BitWord.NativeLiteralBank
