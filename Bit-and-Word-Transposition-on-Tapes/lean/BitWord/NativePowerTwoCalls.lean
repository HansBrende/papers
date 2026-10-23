import BitWord.NativePowerTwo

namespace BitWord.NativePowerTwo
open TransposeFollowup FixedTapeCompiler CopyMachine
set_option autoImplicit false

 theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem embed_single {J : Type*} (p : Port) (labels : J → Label) (pc : J)
    (t : Tape Bool) (outer : Bank) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (single p).ports labels
      (⟨⟨pc,fun _ => t.denote⟩,fun _ => z⟩ : NativeMicrocode.Config (Fin 1) J)
      (frame outer pos)=cfg (labels pc) (Function.update outer p t) (Function.update pos p z) := by
  unfold MicrocodeEmbedding.embed frame cfg
  simp only [←(single p).values_eq_extend]
  congr 2 <;> funext q <;> by_cases h : q=p <;> simp [single,FinitePortBinding.values,h]

private theorem single_focus (t : Tape Bool) :
    (Function.update (fun _ : Fin 1 => (⟨[],[]⟩ : Tape Bool)) 0 t)=fun _ => t := by
  funext i; fin_cases i; rfl

theorem init_call (s : Bool) (outer : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 2, Trace t
      (cfg (.init s (.erase 0)) (Function.update outer (outputPort s) ⟨[],[]⟩) pos)
      (cfg (.init s .done) (Function.update outer (outputPort s) (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos (outputPort s))
  have he := MicrocodeEmbedding.trace_embed (single (outputPort s)).ports (Label.init s)
    NativeBuffer.program program (frame outer pos) (init_code s) htr
  exact ⟨t,ht,by simpa only [NativeBuffer.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus,single_focus,embed_single,Function.update_eq_self,
    BinaryCarry.preparedOutput,NativeSealBack.openWord,symbols,List.map_nil,List.reverse_nil,List.nil_append] using he⟩

def fillBank (s : Bool) (fuel acc : List Bool) (outer : Bank) : Bank :=
  Function.update (Function.update outer (fuelPort s) (Counter.marked fuel))
    (outputPort s) (NativeSealBack.openWord acc)
def fillPos (s : Bool) (origin : Port → ℤ) (acc : List Bool) :=
  Function.update origin (outputPort s) (origin (outputPort s)+acc.length)

@[simp] theorem fillPos_nil (s : Bool) (origin : Port → ℤ) : fillPos s origin []=origin := by
  simp [fillPos]

theorem embed_fill (s : Bool) (pc : CountedFill.Label 1) (fuel acc : List Bool)
    (outer : Bank) (origin : Port → ℤ) :
    MicrocodeEmbedding.embed (fillBinding s).ports (Label.fill s)
      (CountedFill.cfg pc fuel acc (fun p => origin ((fillBinding s).ports p))).denote
      (frame outer origin)=cfg (.fill s pc) (fillBank s fuel acc outer) (fillPos s origin acc) := by
  unfold MicrocodeEmbedding.embed CountedFill.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [←(fillBinding s).values_eq_extend]
  congr 2 <;> funext p <;> cases s <;> cases p <;>
    simp [fillBinding,pair,FinitePortBinding.values,CountedFill.bank,CountedFill.positions,
      fillBank,fillPos,fuelPort,outputPort]

theorem fill_call (s : Bool) (fuel acc : List Bool) (outer : Bank) (origin : Port → ℤ) :
    ∃ t ≤ 11*Counter.value fuel+8+4*fuel.length, Trace t
      (cfg (.fill s (.counter 0)) (fillBank s fuel acc outer) (fillPos s origin acc))
      (cfg (.fill s (.counter 12))
        (fillBank s (List.replicate fuel.length true) (acc++List.replicate (Counter.value fuel) s) outer)
        (fillPos s origin (acc++List.replicate (Counter.value fuel) s))) := by
  obtain ⟨t,ht,htr⟩ := CountedFill.fill_trace 1 s fuel acc (fun p => origin ((fillBinding s).ports p))
  have he := MicrocodeEmbedding.trace_embed (fillBinding s).ports (Label.fill s)
    (CountedFill.program 1 s) program (frame outer origin) (fill_code s) htr
  exact ⟨t,by omega,by simpa only [Nat.mul_one,embed_fill] using he⟩

theorem seal_call (s : Bool) (acc : List Bool) (outer : Bank) (origin : Port → ℤ) :
    ∃ t ≤ 2*acc.length+5, Trace t
      (cfg (.seal s .seal) (Function.update outer (outputPort s) (NativeSealBack.openWord acc))
        (fillPos s origin acc))
      (cfg (.seal s .done) (Function.update outer (outputPort s) (Counter.marked acc)) origin) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace acc (fun _ => origin (outputPort s)+acc.length)
  have he := MicrocodeEmbedding.trace_embed (single (outputPort s)).ports (Label.seal s)
    NativeSealBack.program program (frame outer origin) (seal_code s) htr
  exact ⟨t,ht,by simpa [NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus,single_focus,embed_single,fillPos] using he⟩

theorem erase_call (s : Bool) (fuel : List Bool) (outer : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 4*fuel.length+4, Trace t
      (cfg (.erase s 2) (Function.update outer (fuelPort s) (Counter.marked fuel)) pos)
      (cfg (.erase s 0) (Function.update outer (fuelPort s) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace fuel (fun _ => pos (fuelPort s))
  have he := MicrocodeEmbedding.trace_embed (single (fuelPort s)).ports (Label.erase s)
    NativeErase.program program (frame outer pos) (erase_code s) htr
  exact ⟨t,ht,by simpa only [NativeErase.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus,single_focus,embed_single,Function.update_eq_self] using he⟩

theorem embed_copy (pc : NativeMappedCopy.Label) (source target : Tape Bool)
    (outer : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc source target (fun p => pos (copyBinding.ports p)))
      (frame outer pos)=cfg (.copy pc)
        (Function.update (Function.update outer .source source) .fuel target) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg frame cfg
  simp only [←copyBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;>
    simp [copyBinding,pair,FinitePortBinding.values,NativeMappedCopy.bank] <;> rfl

theorem copy_call (xs : List Bool) (outer : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 6*xs.length+14, Trace t
      (cfg start (Function.update (Function.update outer .source (Counter.marked xs)) .fuel ⟨[],[]⟩) pos)
      (cfg (.copy (.seal .done))
        (Function.update (Function.update outer .source (Counter.marked xs)) .fuel (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun p => pos (copyBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy
    (NativeMappedCopy.program id) program (frame outer pos) copy_code htr
  exact ⟨t,ht,by simpa only [List.map_id,embed_copy,start] using he⟩

end BitWord.NativePowerTwo
