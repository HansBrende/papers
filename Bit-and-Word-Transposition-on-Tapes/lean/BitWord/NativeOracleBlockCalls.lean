import BitWord.NativeOracleBlock

namespace BitWord.NativeOracleBlock
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls
set_option autoImplicit false
noncomputable section

abbrev Bank (M : Transpose.TM) := Port M → Tape Bool

theorem jump (M : Transpose.TM) (pc next : Label M) (s : Bank M) (pos : Port M → ℤ)
    (h : program M pc=.jump next) : Trace M 1 (cfg M pc s pos) (cfg M next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem initialize_input_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ)
    (hs : s (input M)=⟨[],[]⟩) :
    ∃ t≤2, Trace M t (cfg M (.initInput (.erase 0)) s pos)
      (cfg M (.initInput .done) (Function.update s (input M) (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos (input M))
  have hh := call_single (input M) Label.initInput NativeBuffer.program (program M) (initInput_code M)
    (.erase 0) .done s pos (NativeSealBack.openWord []) (pos (input M)) t
  have hh' := hh (by simpa [workCfg,NativeBuffer.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

theorem initialize_capture_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ)
    (hs : s (capture M)=⟨[],[]⟩) :
    ∃ t≤2, Trace M t (cfg M (.initCapture (.erase 0)) s pos)
      (cfg M (.initCapture .done) (Function.update s (capture M) (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos (capture M))
  have hh := call_single (capture M) Label.initCapture NativeBuffer.program (program M) (initCapture_code M)
    (.erase 0) .done s pos (NativeSealBack.openWord []) (pos (capture M)) t
  have hh' := hh (by simpa [workCfg,NativeBuffer.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

theorem load_values {A : Type*} (M : Transpose.TM) (a b c : A) (s : Port M → A) :
    (loadBinding M).values ![a,b,c] s =
      Function.update (Function.update (Function.update s (source M) a) (input M) b) (clock M) c := by
  funext p
  by_cases hs : p=source M <;> by_cases hi : p=input M <;> by_cases hc : p=clock M <;>
    simp_all [loadBinding,FinitePortBinding.values,source,input,clock]

theorem load_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ)
    (xs fs : List Bool) (hlen : fs.length=xs.length) (sl sr : List (Sym Bool))
    (hs : s (source M)=⟨sl,symbols xs++sr⟩)
    (hi : s (input M)=NativeSealBack.openWord []) (hc : s (clock M)=Counter.marked fs) :
    ∃ t≤6*xs.length+5, Trace M t (cfg M (.load .scan) s pos)
      (cfg M (.load .done)
        (Function.update (Function.update s (source M) ⟨(symbols xs).reverse++sl,sr⟩)
          (input M) (Counter.marked xs))
        (Function.update pos (source M) (pos (source M)+xs.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeBoundedCopy.block_trace xs fs hlen sl sr []
    ![pos (source M),pos (input M),pos (clock M)]
  have hshift : NativeBoundedCopy.shift ![pos (source M),pos (input M),pos (clock M)]
      xs.length 0 0=![pos (source M)+xs.length,pos (input M),pos (clock M)] := by
    funext p; fin_cases p <;> simp [NativeBoundedCopy.shift]
  have htr' : NativeBoundedCopy.Trace t
      (workCfg .scan ![s (source M),s (input M),s (clock M)]
        ![pos (source M),pos (input M),pos (clock M)])
      (workCfg .done ![⟨(symbols xs).reverse++sl,sr⟩,Counter.marked xs,s (clock M)]
        ![pos (source M)+xs.length,pos (input M),pos (clock M)]) := by
    simpa only [NativeBoundedCopy.cfg,NativeBoundedCopy.bank,NativeZipper.Config.denote,
      Microcode.Config.denote,workCfg,hs,hi,hc,NativeSealBack.openWord,Counter.marked,
      symbols,List.map_nil,List.reverse_nil,List.nil_append,List.cons_append,List.nil_append,hshift]
      using htr
  have hh := MicrocodeEmbedding.trace_embed (loadBinding M).ports Label.load NativeBoundedCopy.program
    (program M) (frame s pos) (load_code M) htr'
  rw [embed_work,embed_work,load_values,load_values,load_values,load_values] at hh
  have hb : Function.update
      (Function.update (Function.update s (source M) ⟨(symbols xs).reverse++sl,sr⟩)
        (input M) (Counter.marked xs)) (clock M) (s (clock M)) =
      Function.update (Function.update s (source M) ⟨(symbols xs).reverse++sl,sr⟩)
        (input M) (Counter.marked xs) := by
    funext p
    by_cases hc' : p=clock M
    · subst p; simp [source,input,clock]
    · simp [hc']
  have hp' : Function.update
      (Function.update (Function.update pos (source M) (pos (source M)+xs.length))
        (input M) (pos (input M))) (clock M) (pos (clock M)) =
      Function.update pos (source M) (pos (source M)+xs.length) := by
    funext p
    by_cases hc' : p=clock M
    · subst p; simp [source,input,clock]
    · by_cases hi' : p=input M
      · subst p; simp [source,input,clock]
      · simp [hc',hi']
  exact ⟨t,ht,by simpa only [Function.update_eq_self,hb,hp'] using hh⟩

def poolSet {A : Type*} (M : Transpose.TM) (a : Pool M → A) (s : Port M → A) : Port M → A :=
  Sum.elim a (fun i => s (.inr i))
@[simp] theorem pool_values {A : Type*} (M : Transpose.TM) (a : Pool M → A) (s : Port M → A) :
    (poolBinding M).values a s=poolSet M a s := by funext p; cases p <;> rfl

theorem oracle_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ)
    (xs out : List Bool) (T : ℕ) (h : Transpose.ComputesWithin M xs out T)
    (hs : ∀ p,s (.inl p)=NativeOracleReset.initialBank M xs p)
    (hp : ∀ p,pos (.inl p)=0) :
    ∃ t≤NativeOracleReset.budget M T, Trace M t (cfg M (.oracle none) s pos)
      (cfg M (.oracle (NativeOracleReset.terminal M))
        (poolSet M (NativeOracleReset.finalBank M xs out) s)
        (poolSet M (NativeOracleReset.finalPos M out) pos)) := by
  obtain ⟨t,ht,htr⟩ := NativeOracleReset.call_trace M xs out T h
  have hh := MicrocodeEmbedding.trace_embed (poolBinding M).ports Label.oracle (NativeOracleReset.program M)
    (program M) (frame s pos) (oracle_code M) htr
  rw [embed_work,embed_work,pool_values,pool_values,pool_values,pool_values] at hh
  have hb : poolSet M (NativeOracleReset.initialBank M xs) s=s := by
    funext p; cases p with | inl p => exact (hs p).symm | inr p => rfl
  have hpos : poolSet M (fun _ => (0:ℤ)) pos=pos := by
    funext p; cases p with | inl p => exact (hp p).symm | inr p => rfl
  exact ⟨t,ht,by simpa only [hb,hpos] using hh⟩

theorem seal_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (out : List Bool)
    (hs : s (capture M)=NativeSealBack.openWord out) :
    ∃ t≤2*out.length+5,Trace M t (cfg M (.seal .seal) s pos)
      (cfg M (.seal .done) (Function.update s (capture M) (Counter.marked out))
        (Function.update pos (capture M) (pos (capture M)-out.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace out (fun _ => pos (capture M))
  refine ⟨t,ht,call_single (capture M) Label.seal NativeSealBack.program (program M) (seal_code M)
    .seal .done s pos (Counter.marked out) (pos (capture M)-out.length) t ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

@[simp] theorem append_positions (a b : ℤ) (n : ℕ) :
    NativeMappedAppend.finalPositions ![a,b] n=![a,b+n] := by
  funext i; fin_cases i <;> simp [NativeMappedAppend.finalPositions]

theorem append_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (out acc : List Bool)
    (hs : s (capture M)=Counter.marked out) (ha : s (target M)=NativeSealBack.openWord acc) :
    ∃ t≤4*out.length+5,Trace M t (cfg M (.append 0) s pos)
      (cfg M (.append 7) (Function.update s (target M) (NativeSealBack.openWord (acc++out)))
        (Function.update pos (target M) (pos (target M)+out.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id out
    ((symbols acc).reverse++[.start]) ![pos (capture M),pos (target M)]
  have hh := call_pair (capture M) (target M) (by simp [capture,target]) Label.append
    (Microcode.MappedAppendFamily.program id) (program M) (append_code M) 0 7 s pos
    (s (capture M)) (NativeSealBack.openWord (acc++out)) (pos (capture M)) (pos (target M)+out.length) t
  refine ⟨t,ht,?_⟩
  apply (by simpa only [Function.update_eq_self] using hh)
  simpa [workCfg,NativeMappedAppend.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus2,Microcode.focus,hs,ha,NativeSealBack.openWord,
    symbols,List.map_append,List.reverse_append,List.append_assoc,append_positions] using htr

theorem erase_capture_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (out : List Bool)
    (hs : s (capture M)=Counter.marked out) :
    ∃ t≤4*out.length+4,Trace M t (cfg M (.eraseCapture 2) s pos)
      (cfg M (.eraseCapture 0) (Function.update s (capture M) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace out (fun _ => pos (capture M))
  have hh := call_single (capture M) Label.eraseCapture NativeErase.program (program M) (eraseCapture_code M)
    2 0 s pos ⟨[],[]⟩ (pos (capture M)) t
  have hh' := hh (by simpa [workCfg,NativeErase.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

theorem erase_input_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (xs : List Bool)
    (hs : s (input M)=Counter.marked xs) :
    ∃ t≤4*xs.length+4,Trace M t (cfg M (.eraseInput 2) s pos)
      (cfg M (.eraseInput 0) (Function.update s (input M) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (input M))
  have hh := call_single (input M) Label.eraseInput NativeErase.program (program M) (eraseInput_code M)
    2 0 s pos ⟨[],[]⟩ (pos (input M)) t
  have hh' := hh (by simpa [workCfg,NativeErase.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

end
end BitWord.NativeOracleBlock
