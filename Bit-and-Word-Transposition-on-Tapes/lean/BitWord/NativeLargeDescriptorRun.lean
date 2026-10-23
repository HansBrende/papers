import BitWord.NativeLargeDescriptors

namespace BitWord.NativeLargeDescriptors
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def computed (h : ℕ) : Bank
  | .work p => NativeCanonicalParameters.final h p
  | _ => ⟨[],[]⟩

theorem arithmetic_call (h : ℕ) (hh : 2 ≤ h) (pos : Port → ℤ) :
    ∃ t ≤ NativeCanonicalParameters.budget h, Trace t (cfg start (initial h) pos)
      (cfg (.arithmetic .done) (computed h) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeCanonicalParameters.complete_trace h hh (fun p => pos (.work p))
  have he := NativeBindingCalls.restoring_call workBinding Label.arithmetic
    NativeCanonicalParameters.program program arithmetic_code NativeCanonicalParameters.start .done
    (initial h) pos (NativeCanonicalParameters.final h) t htr
  have hf : workBinding.values (NativeCanonicalParameters.final h) (initial h)=computed h := by
    funext p; cases p <;> rfl
  rw [hf] at he
  exact ⟨t,ht,he⟩

theorem literal_call (h : ℕ) (pos : Port → ℤ) :
    ∃ t ≤ 9, Trace t (cfg (.literal (.start ())) (computed h) pos)
      (cfg (.literal (.done ())) (stage h 0) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeLiteralBank.complete_trace 2 literal ()
    (by intro i; simp [literal]; split <;> decide) (fun i => pos (.opcode i))
  have he := NativeBindingCalls.restoring_call literalBinding Label.literal
    (NativeLiteralBank.program 2 literal) program literal_code (.start ()) (.done ())
    (computed h) pos (fun i => Counter.marked (literal () i)) t
      (by simpa only [NativeLiteralBank.cfg,NativeZipper.Config.denote,Microcode.Config.denote,workCfg,
        show ∀ i,literalBinding.ports i=Port.opcode i from fun _ => rfl,computed] using htr)
  have hf : literalBinding.values (fun i => Counter.marked (literal () i)) (computed h)=stage h 0 := by
    funext p; cases p <;> simp [literalBinding,FinitePortBinding.values,computed,stage]
  rw [hf] at he
  exact ⟨t,ht,he⟩

theorem copy_call (h : ℕ) (j : Fin 13) (pos : Port → ℤ) :
    ∃ t ≤ 6*width h+14, Trace t
      (cfg (.copy j (.init (.erase 0))) (stage h j.val) pos)
      (cfg (.copy j (.seal .done)) (stage h (j.val+1)) pos) := by
  let xs := sourceWord h (source j)
  let s := stage h j.val
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace (mapBit j) xs
    (fun p => pos ((copyBinding j).ports p))
  have hi : NativeMappedCopy.bank (Counter.marked xs) ⟨[],[]⟩=
      fun p => s ((copyBinding j).ports p) := by
    funext p; fin_cases p
    · exact (source_marked h j.val j).symm
    · change (⟨[],[]⟩ : Tape Bool) = if j.val<j.val then Counter.marked (parameterWord h j) else ⟨[],[]⟩
      simp
  have hf : NativeMappedCopy.bank (Counter.marked xs) (Counter.marked (xs.map (mapBit j)))=
      Function.update (fun p => s ((copyBinding j).ports p)) 1 (Counter.marked (parameterWord h j)) := by
    funext p; fin_cases p
    · exact (source_marked h j.val j).symm
    · rfl
  have he := NativeBindingCalls.restoring_call (copyBinding j) (Label.copy j)
    (NativeMappedCopy.program (mapBit j)) program (copy_code j) _ _ s pos _ t
      (by simpa only [NativeMappedCopy.cfg,workCfg,hi,hf] using htr)
  rw [←(copyBinding j).values_update,(copyBinding j).values_project] at he
  change Trace t (cfg (.copy j (.init (.erase 0))) (stage h j.val) pos)
    (cfg (.copy j (.seal .done)) (Function.update (stage h j.val) (.parameter j) (Counter.marked (parameterWord h j))) pos) at he
  rw [stage_step] at he
  exact ⟨t,by have := sourceWord_length h j; dsimp [xs] at ht; omega,he⟩

theorem copy_from (h k : ℕ) (hk : k≤13) (pos : Port → ℤ) :
    ∃ t ≤ (13-k)*(6*width h+15), Trace t (cfg (entry k) (stage h k) pos)
      (cfg .done (final h) pos) := by
  induction he : 13-k generalizing k with
  | zero =>
    have hh : k=13 := by omega
    subst k
    refine ⟨0,by simp,?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,final]
    exact .refl _
  | succ n ih =>
    have hkr : k<13 := by omega
    let j : Fin 13 := ⟨k,hkr⟩
    obtain ⟨a,ha,ta⟩ := copy_call h j pos
    have tj := jump (.copy j (.seal .done)) (entry (k+1)) (stage h (k+1)) pos rfl
    obtain ⟨b,hb,tb⟩ := ih (k+1) (by omega) (by omega)
    refine ⟨a+1+b,?_,?_⟩
    · rw [Nat.add_mul]
      omega
    · have hs : entry k=.copy j (.init (.erase 0)) := by simp [entry,hkr,j]
      rw [hs]
      exact trace_trans (trace_trans ta tj) tb

def budget (h : ℕ) := 300*(h+laneBits h+1)+1000

theorem budget_linear (h : ℕ) : budget h ≤ 1600*(h+1) := by
  have hu : laneBits h ≤ h := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))
  unfold budget
  omega

theorem complete_trace (h : ℕ) (hh : 32 ≤ h) (pos : Port → ℤ) :
    ∃ t ≤ budget h, Trace t (cfg start (initial h) pos) (cfg .done (final h) pos) := by
  obtain ⟨a,ha,ta⟩ := arithmetic_call h (by omega) pos
  have ja := jump (.arithmetic .done) (.literal (.start ())) (computed h) pos rfl
  obtain ⟨b,hb,tb⟩ := literal_call h pos
  have jb := jump (.literal (.done ())) (entry 0) (stage h 0) pos rfl
  obtain ⟨c,hc,tc⟩ := copy_from h 0 (by omega) pos
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb tc)))⟩
  unfold budget NativeCanonicalParameters.budget width at *
  omega

theorem slot_parameter {h : ℕ} (hh : 32 ≤ h) (i : Fin 13) :
    Counter.value (parameterWord h i)=NativeSmallDescriptors.parameterValue ((canonicalGates h)[i.val]?) := by
  have hn : ¬h<32 := by omega
  fin_cases i <;> simp [parameterWord,source,sourceWord,mapBit,canonicalGates,hn,
    elevenGates,fiveGates,NativeSmallDescriptors.parameterValue,W_value,N_value,R_value hh,
    List.map_const',PaddedWord.value_zeroes]

theorem slot_opcode {h : ℕ} (hh : 32 ≤ h) (i : Fin 13) :
    literal () i=NativeSmallDescriptors.opcodeWord ((canonicalGates h)[i.val]?) := by
  have hn : ¬h<32 := by omega
  fin_cases i <;> simp [literal,canonicalGates,hn,elevenGates,fiveGates,NativeSmallDescriptors.opcodeWord]

theorem final_fields {h : ℕ} (_hh : 32 ≤ h) :
    final h (.work .h)=Counter.marked (hword h) ∧
    final h (.work .u)=Counter.marked (uword h) ∧
    final h (.work .double)=Counter.marked (W h) ∧
    final h (.work .total)=Counter.marked (N h) ∧
    final h (.work .diff)=Counter.marked (R h) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem final_slots (h : ℕ) (i : Fin 13) :
    final h (.opcode i)=Counter.marked (literal () i) ∧
    final h (.parameter i)=Counter.marked (parameterWord h i) := by
  simp only [final,stage,i.isLt,↓reduceIte,and_self]

theorem final_work (h : ℕ) (p : NativeCanonicalParameters.Port) :
    final h (.work p)=NativeCanonicalParameters.final h p := rfl

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_generate (h : ℕ) (hh : 32 ≤ h) (pos : Port → ℤ) (input : List Bool)
    (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget h, Transpose.stepN nativeMachine input t
      ((cfg start (initial h) pos).denote nativeEncoding program inputPos outRev)=
      some ((cfg .done (final h) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (final h) pos).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace h hh pos
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

end BitWord.NativeLargeDescriptors
