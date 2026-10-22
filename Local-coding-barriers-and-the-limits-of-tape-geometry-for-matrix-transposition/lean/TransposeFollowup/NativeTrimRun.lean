import TransposeFollowup.NativeTrimMachine

namespace TransposeFollowup.NativeTrim
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem prefix_run (xs ys : List Bool) (k : ℕ) (hy : Normalized ys)
    (hx : xs=ys++List.replicate k false) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*xs.length+2*k+4) (cfg .scan (Counter.marked xs) pos)=
      cfg (.seal .seal) (endBlank ys (1+k)) (shift pos ys.length) := by
  have hl : xs.length=ys.length+k := by simp [hx]
  rw [show 2*xs.length+2*k+4=(2*xs.length+1)+1+2*k+2 by omega,
    NativeZipper.run_add,NativeZipper.run_add,NativeZipper.run_add,← cursor_start,
    forward_run,List.nil_append,stop_run]
  rw [hx,drop_zeroes_run,ready_run ys hy]
  simp only [shift_add]
  congr 2
  simp only [List.length_append,List.length_replicate,Nat.cast_add]
  omega

theorem endBlank_denote (xs : List Bool) (k : ℕ) :
    (endBlank xs k).denote=(NativeSealBack.openWord xs).denote := by
  simp only [endBlank,NativeSealBack.openWord,Tape.denote,Turing.Tape.mk₂]
  rw [EraseStream.blanks_eq_nil k]

theorem seal_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc≠.halt)
    (_ : NativeSealBack.program pc≠.reject) :
    program (.seal pc)=MicrocodeEmbedding.instruction binding.ports Label.seal (NativeSealBack.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem embed_seal (pc : NativeSealBack.Label) (word : Tape Bool) (pos : Fin 1 → ℤ) (frame : MicrocodeEmbedding.Frame (Fin 1)) :
    MicrocodeEmbedding.embed binding.ports Label.seal (NativeSealBack.cfg pc word pos).denote
      frame=(cfg (.seal pc) word pos).denote := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg cfg NativeZipper.Config.denote Microcode.Config.denote
  simp only [← binding.values_eq_extend]
  congr 2
  funext p;fin_cases p;rfl

theorem seal_call (ys : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*ys.length+5,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg (.seal .seal) (NativeSealBack.openWord ys) (shift pos ys.length)).denote
        (cfg (.seal .done) (Counter.marked ys) pos).denote := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace ys (shift pos ys.length)
  have he := MicrocodeEmbedding.trace_embed binding.ports Label.seal NativeSealBack.program program
    ⟨fun _ => (⟨[],[]⟩:Tape Bool).denote,pos⟩ seal_code htr
  have hp : (fun p => shift pos ys.length p-ys.length)=pos := by funext p;simp [shift]
  exact ⟨t,ht,by simpa only [embed_seal,hp] using he⟩

theorem jump_trace (ys : List Bool) (pos : Fin 1 → ℤ) :
    OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) 1
      (cfg (.seal .done) (Counter.marked ys) pos).denote (cfg .done (Counter.marked ys) pos).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,NativeZipper.Config.denote,Microcode.Config.denote,program]
  · exact .refl _

theorem trim_trace (xs ys : List Bool) (k : ℕ) (hy : Normalized ys)
    (hx : xs=ys++List.replicate k false) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 4*xs.length+10,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .scan (Counter.marked xs) pos).denote (cfg .done (Counter.marked ys) pos).denote := by
  obtain ⟨a,ha,ta⟩ := NativeZipper.trace_of_run program (prefix_run xs ys k hy hx pos)
  have he : (cfg (.seal .seal) (endBlank ys (1+k)) (shift pos ys.length)).denote=
      (cfg (.seal .seal) (NativeSealBack.openWord ys) (shift pos ys.length)).denote := by
    unfold NativeZipper.Config.denote Microcode.Config.denote cfg
    simp only [endBlank_denote]
  rw [he] at ta
  obtain ⟨b,hb,tb⟩ := seal_call ys pos
  have hl : xs.length=ys.length+k := by simp [hx]
  refine ⟨a+b+1,by omega,?_⟩
  exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tb) (jump_trace ys pos)

theorem complete_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ ys,Normalized ys ∧ Counter.value ys=Counter.value xs ∧ ys.length=(Counter.value xs).size ∧
    ∃ t ≤ 4*xs.length+10,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .scan (Counter.marked xs) pos).denote (cfg .done (Counter.marked ys) pos).denote := by
  obtain ⟨ys,k,hy,hx⟩ := decomposition xs
  have hv : Counter.value ys=Counter.value xs := by rw [hx,PaddedWord.value_append_zeroes]
  exact ⟨ys,hy,hv,by rw [← hv];exact normalized_length ys hy,trim_trace xs ys k hy hx pos⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 1) Label.scan
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_complete (xs : List Bool) (pos : Fin 1 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ ys,Normalized ys ∧ Counter.value ys=Counter.value xs ∧ ys.length=(Counter.value xs).size ∧
    ∃ t ≤ 4*xs.length+10,
      Transpose.stepN nativeMachine input t ((cfg .scan (Counter.marked xs) pos).denote.denote nativeEncoding program ip outRev)=
        some ((cfg .done (Counter.marked ys) pos).denote.denote nativeEncoding program ip outRev) ∧
      Transpose.step nativeMachine input ((cfg .done (Counter.marked ys) pos).denote.denote nativeEncoding program ip outRev)=none := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace xs pos
  refine ⟨ys,hy,hv,hl,t,ht,NativeMicrocode.trace_stepN nativeEncoding program input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input ip outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Fin 1 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ ys,Normalized ys ∧ Counter.value ys=Counter.value xs ∧ ys.length=(Counter.value xs).size ∧
    ∃ t ≤ 4*xs.length+10,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .scan (Counter.marked xs) pos).denote frame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (Counter.marked ys) pos).denote frame).denote encoding target ip outRev) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace xs pos
  exact ⟨ys,hy,hv,hl,t,ht,MicrocodeEmbedding.native_call encoding ports labels program target frame input ip outRev hc htr⟩

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=14 ∧ nativeEncoding.label .scan=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=14
  decide +kernel

end TransposeFollowup.NativeTrim
