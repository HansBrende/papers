import BitWord.NativeGate

namespace BitWord.NativeGate
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section

theorem jump (M : Transpose.TM) (pc next : Label M) (s : Bank M) (pos : Port M → ℤ)
    (h : program M pc=.jump next) : Trace M 1 (cfg M pc s pos) (cfg M next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem read_call (M : Transpose.TM) (raw param fs : List Bool) (a b : Bool) (pos : Port M → ℤ) :
    ∃ t≤5,Trace M t (cfg M (start M) (bank M raw param [a,b] fs) pos)
      (cfg M (selected M a b) (bank M raw param [a,b] fs) pos) := by
  let s := bank M raw param [a,b] fs
  obtain ⟨t,ht,htr⟩ := NativeOpcode.complete_trace a b (fun _ => pos (opcode M))
  have hh := call_single (opcode M) Label.read NativeOpcode.program (program M) (read_code M)
    NativeOpcode.start (.done a b) s pos (s (opcode M)) (pos (opcode M)) t
    (by simpa [NativeOpcode.cfg,NativeZipper.Config.denote,Microcode.Config.denote,workCfg,s] using htr)
  have hc : Trace M t (cfg M (start M) s pos) (cfg M (.read (.done a b)) s pos) := by
    simpa only [Function.update_eq_self,start] using hh
  have hj := jump M (.read (.done a b)) (selected M a b) s pos rfl
  exact ⟨t+1,by omega,trace_trans hc hj⟩

theorem split_call (M : Transpose.TM) (raw param code fs : List Bool) (pos : Port M → ℤ) :
    ∃ t≤20*raw.length+60,Trace M t
      (cfg M (.split NativeSplit.start) (bank M raw param code fs) pos)
      (cfg M (.split .done) (bank M (NativeSplit.output raw) param code fs) pos) := by
  let s := bank M raw param code fs
  have hproj : (fun i => s ((splitBinding M).ports i))=![Counter.marked raw,⟨[],[]⟩,⟨[],[]⟩] := by
    funext i; fin_cases i <;> rfl
  obtain ⟨t,ht,htr⟩ := NativeSplit.complete_trace raw (fun i => pos ((splitBinding M).ports i))
  have hh := NativeBindingCalls.restoring_call (splitBinding M) Label.split NativeSplit.program
    (program M) (split_code M) NativeSplit.start .done s pos
    ![Counter.marked (NativeSplit.output raw),⟨[],[]⟩,⟨[],[]⟩] t
    (by rw [hproj]; exact htr)
  exact ⟨t,ht,by simpa only [s,split_values] using hh⟩

theorem merge_call (M : Transpose.TM) (a b fs param code : List Bool)
    (hab : a.length=b.length) (hfs : fs.length=a.length) (pos : Port M → ℤ) :
    ∃ t≤50*a.length+80,Trace M t
      (cfg M (.merge NativeUnsplit.start) (bank M (a++b) param code fs) pos)
      (cfg M (.merge .done) (bank M (NativeInterleave.output a b) param code fs) pos) := by
  let s := bank M (a++b) param code fs
  have hproj : (fun i => s ((leftBinding M).ports i))=
      ![Counter.marked (a++b),⟨[],[]⟩,⟨[],[]⟩,Counter.marked fs] := by
    funext i; fin_cases i <;> rfl
  obtain ⟨t,ht,htr⟩ := NativeUnsplit.complete_trace a b fs hab hfs (fun i => pos ((leftBinding M).ports i))
  have hh := NativeBindingCalls.restoring_call (leftBinding M) Label.merge NativeUnsplit.program
    (program M) (merge_code M) NativeUnsplit.start .done s pos
    ![Counter.marked (NativeInterleave.output a b),⟨[],[]⟩,⟨[],[]⟩,Counter.marked fs] t
    (by rw [hproj]; exact htr)
  exact ⟨t,ht,by simpa only [s,left_values] using hh⟩

theorem suffix_call (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    {N k : ℕ} (hk : 2*k≤N) (b : Address N → Bool) (xs code fs : List Bool)
    (hx : Counter.value xs=k) (sp tp kp pp : ℤ) (extra : Fin 4 → ℤ) :
    ∃ t≤NativeSuffixPowered.budget M C N k xs,Trace M t
      (cfg M (.suffix (NativeSuffixPowered.start M)) (bank M (flattenBank b) xs code fs)
        (positions M sp tp kp pp extra))
      (cfg M (.suffix .done)
        (bank M (flattenBank (moveBank (Gate.equiv N (.suffix k) hk) b)) xs code fs)
        (positions M sp tp kp pp extra)) := by
  obtain ⟨t,ht,htr⟩ := NativeSuffixPowered.complete_trace M C hM hk b xs hx sp tp kp pp
  let s := bank M (flattenBank b) xs code fs
  have hh := MicrocodeEmbedding.trace_embed (suffixBinding M).ports Label.suffix
    (NativeSuffixPowered.program M) (program M) (frame s (positions M sp tp kp pp extra))
    (suffix_code M) htr
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht,by simpa only [s,bank,positions,suffix_values] using hh⟩

end
end BitWord.NativeGate
