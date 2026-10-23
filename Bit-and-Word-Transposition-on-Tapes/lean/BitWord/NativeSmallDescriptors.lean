import BitWord.NativeLiteralBank
import BitWord.CanonicalGates
import TransposeFollowup.MeasuredWord

/-! The small branch has only 32 possible sizes. Its finite control emits every
opcode, parameter and retained arithmetic field from initially blank tapes. -/
namespace BitWord.NativeSmallDescriptors
open FixedTapeCompiler CopyMachine TransposeFollowup
open scoped BigOperators

inductive Port | u | w | n | r | opcode (slot : Fin 13) | parameter (slot : Fin 13)
  deriving DecidableEq, Fintype

def opcodeWord : Option Gate → List Bool
  | none => [false,false]
  | some .right => [true,false]
  | some .left => [false,true]
  | some (.suffix _) => [true,true]

def parameterValue : Option Gate → ℕ
  | some (.suffix k) => k
  | _ => 0

def word (h : Fin 32) : Port → List Bool
  | .u => MeasuredWord.result (laneBits h)
  | .w => MeasuredWord.result (tailBits h)
  | .n => MeasuredWord.result (halfAddress h)
  | .r => MeasuredWord.result (halfAddress h-tailBits h)
  | .opcode i => opcodeWord ((canonicalGates h)[i.val]?)
  | .parameter i => MeasuredWord.result (parameterValue ((canonicalGates h)[i.val]?))

theorem small_gate_parameter (h : Fin 32) (g : Gate) (hg : g ∈ canonicalGates h) :
    parameterValue (some g) ≤ h.val := by
  simp only [canonicalGates,h.isLt,↓reduceIte,rotationGates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_replicate] at hg
  rcases hg with (⟨_,rfl⟩ | rfl) | ⟨_,rfl⟩ <;> simp [parameterValue]

theorem parameter_bound (h : Fin 32) (i : Fin 13) :
    parameterValue ((canonicalGates h)[i.val]?) ≤ h.val := by
  cases he : (canonicalGates h)[i.val]? with
  | none => simp [parameterValue]
  | some g =>
    apply small_gate_parameter h g
    exact List.mem_of_getElem? he

/-- One fixed upper bound on every small-branch emitted word. -/
def bound : ℕ := 64

theorem word_length_le (h : Fin 32) (p : Port) : (word h p).length ≤ bound := by
  have hu : laneBits h ≤ 5 := Nat.clog_le_of_le_pow (by norm_num)
  have hw := tailBits_small h.isLt
  have hn : halfAddress h ≤ 34 := by unfold halfAddress; have:=h.isLt; omega
  cases p <;> simp only [word,MeasuredWord.result_length]
  · change laneBits h ≤ 64; omega
  · change tailBits h ≤ 64; omega
  · change halfAddress h ≤ 64; omega
  · change halfAddress h-tailBits h ≤ 64; omega
  · rename_i i
    cases (canonicalGates h)[i.val]? with
    | none => decide
    | some g => cases g <;> simp [opcodeWord,bound]
  · rename_i i
    have hp := parameter_bound h i
    change parameterValue ((canonicalGates h)[i.val]?) ≤ 64
    have:=h.isLt; omega

abbrev Label := NativeLiteralBank.Label (Fin 32) bound
def program := NativeLiteralBank.program bound word
abbrev cfg := NativeLiteralBank.cfg (T := Port) (H := Fin 32) bound
abbrev Trace := NativeLiteralBank.Trace bound word

def initial : Port → Tape Bool := fun _ => ⟨[],[]⟩
def final (h : Fin 32) : Port → Tape Bool := fun p => Counter.marked (word h p)

/-- Entry size is in the bounded classifier's finite control. No initialized
metadata tapes or free work are prerequisites of this writer. -/
theorem complete_trace (h : Fin 32) (pos : Port → ℤ) :
    ∃ t ≤ 2*bound+5, Trace t (cfg (.start h) initial pos).denote
      (cfg (.done h) (final h) pos).denote :=
  NativeLiteralBank.complete_trace bound word h (word_length_le h) pos

theorem fields (h : Fin 32) :
    Counter.value (word h .u)=laneBits h ∧ Counter.value (word h .w)=tailBits h ∧
    Counter.value (word h .n)=halfAddress h ∧
    Counter.value (word h .r)=halfAddress h-tailBits h := by
  simp [word,MeasuredWord.result_value]

theorem slot_parameter (h : Fin 32) (i : Fin 13) :
    Counter.value (word h (.parameter i))=parameterValue ((canonicalGates h)[i.val]?) :=
  MeasuredWord.result_value _

theorem slot_opcode (h : Fin 32) (i : Fin 13) :
    word h (.opcode i)=opcodeWord ((canonicalGates h)[i.val]?) := rfl

theorem opcode_length (h : Fin 32) (i : Fin 13) : (word h (.opcode i)).length=2 := by
  simp only [word]
  cases (canonicalGates h)[i.val]? with
  | none => rfl
  | some g => cases g <;> rfl

theorem slot_parameter_length_bound (h : Fin 32) (i : Fin 13) :
    (word h (.parameter i)).length ≤ h.val + laneBits h.val + 2 := by
  simpa only [word, MeasuredWord.result_length] using
    (parameter_bound h i).trans (by omega)

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) (L := Label) (.start (0 : Fin 32))
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=30 ∧ nativeMachine.g+1=5 := by
  constructor
  · change Fintype.card Port=30
    decide +kernel
  · rfl

theorem native_write (h : Fin 32) (pos : Port → ℤ) (input : List Bool)
    (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*bound+5, Transpose.stepN nativeMachine input t
      ((cfg (.start h) initial pos).denote.denote nativeEncoding program inputPos outRev)=
      some ((cfg (.done h) (final h) pos).denote.denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg (.done h) (final h) pos).denote.denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace h pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro hh
  exact hh.1 rfl

end BitWord.NativeSmallDescriptors
