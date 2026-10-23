import BitWord.NativeCanonicalGeneratorCalls
import BitWord.NativeLargeDescriptorRun

namespace BitWord.NativeCanonicalGenerator
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem large_call (h : ℕ) (hh : 32 ≤ h) (pos : Port → ℤ) :
    ∃ t ≤ NativeLargeDescriptors.budget h, Trace t
      (cfg (.large NativeLargeDescriptors.start) (initial h) pos)
      (cfg (.large .done) (NativeLargeDescriptors.final h) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeLargeDescriptors.complete_trace h hh pos
  have he := NativeBindingCalls.restoring_call largeBinding Label.large NativeLargeDescriptors.program
    program large_code NativeLargeDescriptors.start .done (initial h) pos _ t htr
  have hf : largeBinding.values (NativeLargeDescriptors.final h) (initial h)=NativeLargeDescriptors.final h := by
    funext p; rfl
  rw [hf] at he
  exact ⟨t,ht,he⟩

def budget (h : ℕ) := 300*(h+laneBits h+1)+1100

theorem complete_trace (h : ℕ) (pos : Port → ℤ) :
    ∃ t ≤ budget h, Trace t (cfg start (initial h) pos) (cfg .done (final h) pos) := by
  obtain ⟨a,ha,ta⟩ := classifier_call h pos
  by_cases hh : h < 32
  · let j : Fin 32 := ⟨h,hh⟩
    have tj := jump (.classifier (.done (NativeSmallClassifier.answer (hword h))))
      (.small (.start j)) (initial h) pos (by change Microcode.Instruction.jump (branch (NativeSmallClassifier.answer (hword j)))=_; rw [branch_small j])
    obtain ⟨b,hb,tb⟩ := small_call j pos
    have tk := jump (.small (.done j)) .done (smallFinal j) pos rfl
    refine ⟨a+(1+(b+1)),?_,?_⟩
    · unfold budget; omega
    · simpa only [final,hh,↓reduceDIte] using trace_trans ta (trace_trans tj (trace_trans tb tk))
  · have tj := jump (.classifier (.done (NativeSmallClassifier.answer (hword h))))
      (.large NativeLargeDescriptors.start) (initial h) pos (by
        simp only [program,branch_large h (by omega)])
    obtain ⟨b,hb,tb⟩ := large_call h (by omega) pos
    have tk := jump (.large .done) .done (NativeLargeDescriptors.final h) pos rfl
    refine ⟨a+(1+(b+1)),?_,?_⟩
    · unfold budget NativeLargeDescriptors.budget at *; omega
    · simpa only [final,hh,↓reduceDIte] using trace_trans ta (trace_trans tj (trace_trans tb tk))

theorem budget_linear (h : ℕ) : budget h ≤ 1700*(h+1) := by
  have hu : laneBits h ≤ h := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))
  unfold budget; omega

theorem field_values (h : ℕ) :
    Counter.value (fieldWord h .u)=laneBits h ∧ Counter.value (fieldWord h .w)=tailBits h ∧
    Counter.value (fieldWord h .n)=halfAddress h ∧
    Counter.value (fieldWord h .r)=halfAddress h-tailBits h := by
  by_cases hh : h < 32
  · simpa only [fieldWord,hh,↓reduceDIte] using NativeSmallDescriptors.fields ⟨h,hh⟩
  · simp [fieldWord,hh,W_value,N_value,R_value (by omega : 32 ≤ h)]

theorem slot_parameter (h : ℕ) (i : Fin 13) :
    Counter.value (fieldWord h (.parameter i))=
      NativeSmallDescriptors.parameterValue ((canonicalGates h)[i.val]?) := by
  by_cases hh : h < 32
  · simpa only [fieldWord,hh,↓reduceDIte] using NativeSmallDescriptors.slot_parameter ⟨h,hh⟩ i
  · simpa only [fieldWord,hh,↓reduceDIte] using NativeLargeDescriptors.slot_parameter (by omega : 32 ≤ h) i

theorem slot_opcode (h : ℕ) (i : Fin 13) :
    fieldWord h (.opcode i)=NativeSmallDescriptors.opcodeWord ((canonicalGates h)[i.val]?) := by
  by_cases hh : h < 32
  · simpa only [fieldWord,hh,↓reduceDIte] using NativeSmallDescriptors.slot_opcode ⟨h,hh⟩ i
  · simpa only [fieldWord,hh,↓reduceDIte] using NativeLargeDescriptors.slot_opcode (by omega : 32 ≤ h) i

theorem slot_parameter_length (h : ℕ) (i : Fin 13) :
    (fieldWord h (.parameter i)).length ≤ h+laneBits h+2 := by
  by_cases hh : h < 32
  · simpa only [fieldWord,hh,↓reduceDIte] using NativeSmallDescriptors.slot_parameter_length_bound ⟨h,hh⟩ i
  · simpa only [fieldWord,hh,↓reduceDIte,width] using NativeLargeDescriptors.parameterWord_length h i

theorem slot_opcode_length (h : ℕ) (i : Fin 13) : (fieldWord h (.opcode i)).length=2 := by
  rw [slot_opcode]
  cases (canonicalGates h)[i.val]? with
  | none => rfl
  | some g => cases g <;> rfl

/-- Every generated field and descriptor has a uniformly linear physical length. -/
theorem field_word_length (h : ℕ) (p : NativeSmallDescriptors.Port) :
    (fieldWord h p).length ≤ 4*h+8 := by
  have hu : laneBits h ≤ h := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hw : tailBits h ≤ h+1 := by unfold tailBits dummyBits; omega
  have hn : halfAddress h ≤ 2*h+1 := by unfold halfAddress; omega
  cases p with
  | opcode i => rw [slot_opcode_length]; omega
  | parameter i => exact (slot_parameter_length h i).trans (by omega)
  | u =>
    by_cases hh : h < 32 <;>
      simp only [fieldWord,hh,↓reduceDIte,NativeSmallDescriptors.word,MeasuredWord.result_length,uword_length] <;> omega
  | w =>
    by_cases hh : h < 32 <;>
      simp only [fieldWord,hh,↓reduceDIte,NativeSmallDescriptors.word,MeasuredWord.result_length,W_length,width] <;> omega
  | n =>
    by_cases hh : h < 32 <;>
      simp only [fieldWord,hh,↓reduceDIte,NativeSmallDescriptors.word,MeasuredWord.result_length,N_length,width] <;> omega
  | r =>
    by_cases hh : h < 32 <;>
      simp only [fieldWord,hh,↓reduceDIte,NativeSmallDescriptors.word,MeasuredWord.result_length,R_length,width] <;> omega

theorem slot_parameter_length_linear (h : ℕ) (i : Fin 13) :
    (fieldWord h (.parameter i)).length ≤ 2*h+2 := by
  have hu : laneBits h ≤ h := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))
  exact (slot_parameter_length h i).trans (by omega)

theorem final_scratch (h : ℕ) (p : NativeCanonicalParameters.Port)
    (hp : p≠.h ∧ p≠.u ∧ p≠.double ∧ p≠.total ∧ p≠.diff) :
    final h (.work p)=(⟨[],[]⟩ : Tape Bool) := by
  by_cases hh : h < 32 <;> simp only [final,hh,↓reduceDIte] <;> cases p <;>
    simp_all [smallFinal,smallBinding,FinitePortBinding.values,initial,
      NativeLargeDescriptors.initial,NativeCanonicalParameters.initial,
      NativeLargeDescriptors.final,NativeLargeDescriptors.stage,NativeCanonicalParameters.final]

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_generate (h : ℕ) (pos : Port → ℤ) (input : List Bool)
    (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget h, Transpose.stepN nativeMachine input t
      ((cfg start (initial h) pos).denote nativeEncoding program inputPos outRev)=
      some ((cfg .done (final h) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (final h) pos).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace h pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro hc
  exact hc.1 rfl

theorem fixed_resources : nativeMachine.k=38 ∧ nativeMachine.g+1=5 ∧
    nativeEncoding.label start=0 := by
  constructor
  · change Fintype.card Port=38
    decide +kernel
  · exact ⟨rfl,NativeMicrocode.initialEncoding_start _⟩

end BitWord.NativeCanonicalGenerator
