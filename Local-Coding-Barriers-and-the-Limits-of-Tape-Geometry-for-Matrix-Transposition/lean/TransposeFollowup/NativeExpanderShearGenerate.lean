import TransposeFollowup.OpcodeGeneratorMeaning

/-! Paid suffixes of the existing uniform rational matching generator.
They begin at its actual post-loader state, so a raw caller may supply the
proved half-dimension word while retaining the original matrix payload.
No execution-correctness premise is assumed. -/
namespace TransposeFollowup.NativeExpanderShearGenerate
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

abbrev Port := FamilyEnumeration.Port

def familyEntry (F : Fin (r+1) → RationalMobius) : FamilyEnumeration.Label F :=
  .first (.enumeration (SeededEnumeration.start (F 0)))

theorem family_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ FamilyEnumeration.coefficient F*Transpose.inputLength n,
      FamilyEnumeration.Trace F w t
        (FamilyEnumeration.cfg (familyEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (FamilyEnumeration.cfg .done (RawEnumeration.loaded w xs (FamilyEnumeration.stream F xs).reverse)
          (FamilyEnumeration.advance pos (FamilyEnumeration.stream F xs).length) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := RawEnumeration.enumeration_call (F 0) w xs [] pos w.length outRev
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (FamilyEnumeration.Label.first (F:=F)) (RawEnumeration.program (F 0))
    (FamilyEnumeration.program F) (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos)
    w (FamilyEnumeration.first_code F) ta
  simp only [FamilyEnumeration.embed_first,List.append_nil] at tea
  let bits := RowEnumeration.rowsFrom (F 0) xs (Counter.value xs) 0
  have ts := FamilyEnumeration.seal_trace F (.first (.enumeration .done)) (FamilyEnumeration.entry F 0)
    rfl w xs (symbols bits).reverse (FamilyEnumeration.advance pos bits.length) w.length outRev
  obtain ⟨b,hb,tb⟩ := FamilyEnumeration.rest_trace F w xs r 0 (by omega)
    ((FamilyEnumeration.batch (F 0) xs).reverse) (FamilyEnumeration.advance pos (FamilyEnumeration.batch (F 0) xs).length) w.length outRev
  have ha' := SeededEnumeration.total_budget (F 0) n xs hn hv
    (by rw [hl];exact Nat.size_le_size (Nat.le_succ n))
  have hb' := FamilyEnumeration.rest_budget_le F xs n hn hv hl r 0
  have hL := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b,?_,?_⟩
  · change SeededEnumeration.budget (F 0) xs ≤ FamilyEnumeration.seededCoefficient (F 0)*Transpose.inputLength n at ha'
    have hco : FamilyEnumeration.seededCoefficient (F 0)≤RawEnumeration.coefficient (F 0) := by
      unfold FamilyEnumeration.seededCoefficient RawEnumeration.coefficient
      dsimp only
      omega
    have ha'' := ha.trans (ha'.trans (Nat.mul_le_mul_right (Transpose.inputLength n) hco))
    unfold FamilyEnumeration.coefficient
    nlinarith
  · have hs : (FamilyEnumeration.batch (F 0) xs).reverse=.stop::(symbols bits).reverse := by
      simp [FamilyEnumeration.batch,bits,List.reverse_append]
    have hp : FamilyEnumeration.advance (FamilyEnumeration.advance pos bits.length) 1=
        FamilyEnumeration.advance pos (FamilyEnumeration.batch (F 0) xs).length := by
      rw [FamilyEnumeration.advance_add]
      simp [FamilyEnumeration.batch,bits,symbols]
    rw [← hs,hp] at ts
    have hi : RawEnumeration.finalPositions pos bits=FamilyEnumeration.advance pos bits.length :=
      FamilyEnumeration.advance_bits pos bits
    rw [hi] at tea
    have htr := NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea ts) tb
    simpa only [familyEntry,FamilyEnumeration.stream,List.reverse_append,List.append_assoc,
      FamilyEnumeration.advance_add,List.length_append] using htr

def readerEntry (F : Fin (r+1) → RationalMobius) : FamilyReader.Label F := .generate (familyEntry F)

theorem reader_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ FamilyReader.coefficient F*Transpose.inputLength n,
      FamilyReader.Trace F w t
        (FamilyReader.cfg (readerEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (FamilyReader.cfg (.rewind .done) (FamilyReader.readBank w xs (FamilyEnumeration.stream F xs)) pos w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := family_trace F w xs n hn hv hl pos outRev
  have hs : (FamilyEnumeration.stream F xs).length≤a := by
    have hp := (NativeHeadDisplacement.trace_bounds (FamilyEnumeration.program F) w ta FamilyEnumeration.output).2
    simp only [FamilyEnumeration.cfg,FamilyEnumeration.workCfg,FamilyEnumeration.advance,ite_true] at hp
    omega
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (FamilyReader.Label.generate (F:=F)) (FamilyEnumeration.program F) (FamilyReader.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (FamilyReader.generate_code F) ta
  simp only [FamilyReader.embed_generate] at tea
  obtain ⟨b,hb,tb⟩ := FamilyReader.rewind_call F w xs (FamilyEnumeration.stream F xs)
    (FamilyReader.stream_nonblank F xs) pos w.length outRev
  have tj := FamilyReader.jump_trace F w (RawEnumeration.loaded w xs (FamilyEnumeration.stream F xs).reverse)
    (FamilyEnumeration.advance pos (FamilyEnumeration.stream F xs).length) w.length outRev
  have hL := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea tj) tb⟩
  unfold FamilyReader.coefficient
  nlinarith

def normalizedEntry (F : Fin (r+1) → RationalMobius) : RawNormalization.Label F := .generate (readerEntry F)

theorem normalization_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ RawNormalization.coefficient F*Transpose.inputLength n,
      RawNormalization.Trace F w t
        (RawNormalization.cfg (normalizedEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (RawNormalization.cfg (.normalize .done)
          (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
            ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
          (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length
            (FamilyNormalization.outputStream F xs).length) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := reader_trace F w xs n hn hv hl pos outRev
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (RawNormalization.Label.generate (F:=F)) (FamilyReader.program F) (RawNormalization.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (RawNormalization.generate_code F) ta
  simp only [RawNormalization.embed_generate,← RawNormalization.bank_ready] at tea
  have hnx : 1≤Counter.value xs := by omega
  have hxs : xs.length≤(Counter.value xs+1).size := by rw [hl,hv];exact Nat.size_le_size (Nat.le_succ n)
  obtain ⟨b,hb,tb⟩ := RawNormalization.normalize_call F w xs hnx hxs [] [] [] pos w.length outRev
  simp only [List.append_nil,FamilyNormalization.input_stream_eq] at tb
  rw [hv] at hb
  have tj := RawNormalization.transfer_trace F w
    (RawNormalization.bank w xs ⟨[],FamilyEnumeration.stream F xs⟩ ⟨[],[]⟩) pos w.length outRev
  have hL := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea tj) tb⟩
  unfold RawNormalization.coefficient
  nlinarith


def normalReaderEntry (F : Fin (r+1) → RationalMobius) : NormalizedReader.Label F := .generate (normalizedEntry F)

theorem normalized_reader_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ NormalizedReader.coefficient F*Transpose.inputLength n,
      NormalizedReader.Trace F w t
        (NormalizedReader.cfg (normalReaderEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (NormalizedReader.cfg (.rewind .done)
          (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩)
          (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length 0) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := normalization_trace F w xs n hn hv hl pos outRev
  have hs : (FamilyNormalization.outputStream F xs).length≤a := by
    have hp := (NativeHeadDisplacement.trace_bounds (RawNormalization.program F) w ta RawNormalization.output).2
    have hp' : RawNormalization.output≠RawNormalization.rawOutput := by decide +kernel
    simp only [RawNormalization.cfg,RawNormalization.workCfg,RawNormalization.advance,hp',ite_false,ite_true,add_zero] at hp
    omega
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (NormalizedReader.Label.generate (F:=F)) (RawNormalization.program F) (NormalizedReader.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (NormalizedReader.generate_code F) ta
  simp only [NormalizedReader.embed_generate] at tea
  obtain ⟨b,hb,tb⟩ := NormalizedReader.rewind_call F w xs (FamilyEnumeration.stream F xs)
    (FamilyNormalization.outputStream F xs) (RawNormalization.output_nonblank F xs) pos w.length outRev
  have tj := NormalizedReader.transfer_trace F w
    (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
    (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length outRev
  have hL := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea tj) tb⟩
  unfold NormalizedReader.coefficient
  nlinarith

def selectorEntry (F : Fin (r+1) → RationalMobius) : RawSelector.Label F := .prepare (normalReaderEntry F)

theorem selector_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ RawSelector.coefficient F*Transpose.inputLength n,
      RawSelector.Trace F w t
        (RawSelector.cfg (selectorEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (RawSelector.cfg (.select .done) (RawSelector.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
          ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
          (RawSelector.advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := normalized_reader_trace F w xs n hn hv hl pos outRev
  have hs : (FamilyEnumeration.stream F xs).length≤a := by
    have hp := (NativeHeadDisplacement.trace_bounds (NormalizedReader.program F) w ta RawSelector.rawOutput).2
    simp only [NormalizedReader.cfg,NormalizedReader.workCfg,RawNormalization.advance,
      ite_true,Nat.cast_zero,ite_self,add_zero] at hp
    omega
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (RawSelector.Label.prepare (F:=F)) (NormalizedReader.program F) (RawSelector.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (RawSelector.prepare_code F) ta
  simp only [RawSelector.embed_prepare,RawSelector.prepared_bank] at tea
  obtain ⟨b,hb,tb⟩ := RawSelector.rewind_call F w xs (FamilyEnumeration.stream F xs)
    (FamilyReader.stream_nonblank F xs) ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩ pos w.length outRev
  have j1 := RawSelector.prepare_transfer F w
    (RawSelector.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩)
    (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length 0) w.length outRev
  have j2 := RawSelector.select_transfer F w
    (RawSelector.bank w xs ⟨[],FamilyEnumeration.stream F xs⟩ ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩) pos w.length outRev
  have hn' : 1≤Counter.value xs := by omega
  have hl' : xs.length≤(Counter.value xs+1).size := by rw [hv,hl];exact Nat.size_le_size (by omega)
  obtain ⟨c,hc,tc⟩ := RawSelector.select_call F w xs hn' hl' [] [] [] pos w.length outRev
  simp only [List.append_nil,FamilyNormalization.input_stream_eq] at tc
  rw [hv] at hc
  have hL := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b+1+c,?_,?_⟩
  · unfold RawSelector.coefficient
    nlinarith
  · exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea j1) tb) j2) tc

def canonicalEntry (F : Fin (r+1) → RationalMobius) : CanonicalReader.Label F := .generate (selectorEntry F)

theorem canonical_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ CanonicalReader.coefficient F*Transpose.inputLength n,
      CanonicalReader.Trace F w t
        (CanonicalReader.cfg (canonicalEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (CanonicalReader.cfg (.rewind .done) (CanonicalReader.readyBank F w xs)
          (CanonicalReader.finalPositions F xs pos) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := selector_trace F w xs n hn hv hl pos outRev
  have hs : (FamilySelector.outputStream F xs).length≤a := by
    have hp := (NativeHeadDisplacement.trace_bounds (RawSelector.program F) w ta RawSelector.output).2
    have hp' : RawSelector.output≠RawSelector.rawOutput := by decide +kernel
    simp only [RawSelector.cfg,RawSelector.workCfg,RawSelector.advance,hp',ite_false,ite_true,add_zero] at hp
    omega
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (CanonicalReader.Label.generate (F:=F)) (RawSelector.program F) (CanonicalReader.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (CanonicalReader.generate_code F) ta
  simp only [CanonicalReader.embed_generate] at tea
  obtain ⟨b,hb,tb⟩ := CanonicalReader.rewind_call F w xs (FamilyEnumeration.stream F xs)
    (FamilySelector.outputStream F xs) (FamilySelector.output_nonblank F xs)
    ⟨[],FamilyNormalization.outputStream F xs⟩ pos w.length outRev
  have tj := CanonicalReader.transfer_trace F w
    (RawSelector.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
      ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
    (RawSelector.advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev
  have hL := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea tj) tb⟩
  unfold CanonicalReader.coefficient
  nlinarith

def schedulerEntry (F : Fin (r+1) → RationalMobius) : SchedulerSeed.Label F := .prepare (canonicalEntry F)

theorem scheduler_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ SchedulerSeed.coefficient F*Transpose.inputLength n,
      SchedulerSeed.Trace F w t
        (SchedulerSeed.cfg (schedulerEntry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (SchedulerSeed.cfg (.seed .done) (SchedulerSeed.readyBank F w xs)
          (CanonicalReader.finalPositions F xs pos) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := canonical_trace F w xs n hn hv hl pos outRev
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (SchedulerSeed.Label.prepare (F:=F)) (CanonicalReader.program F) (SchedulerSeed.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (SchedulerSeed.prepare_code F) ta
  simp only [SchedulerSeed.embed_prepare] at tea
  have tj := SchedulerSeed.transfer_trace F w (CanonicalReader.readyBank F w xs)
    (CanonicalReader.finalPositions F xs pos) w.length outRev
  obtain ⟨b,hb,tb⟩ := SchedulerSeed.seed_call F w xs (CanonicalReader.finalPositions F xs pos) w.length outRev
  have hnL := DimensionCandidate.dimension_le_length n hn
  have hs : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hlL : xs.length≤Transpose.inputLength n := by omega
  have h1 := hn.trans hnL
  refine ⟨a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea tj) tb⟩
  unfold ArithmeticSeed.budget at hb
  unfold SchedulerSeed.coefficient
  nlinarith

def entry (F : Fin (r+1) → RationalMobius) : OpcodeGenerator.Label F := .prepare (schedulerEntry F)

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (n : ℕ) (hn : 1≤n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ OpcodeGenerator.coefficient F*Transpose.inputLength n,
      OpcodeGenerator.Trace F w t
        (OpcodeGenerator.cfg (entry F) (RawEnumeration.loaded w xs []) pos w.length outRev)
        (OpcodeGenerator.cfg (.schedule .done) (OpcodeGenerator.finalBank F w xs)
          (OpcodeGenerator.finalPositions F xs pos) w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := scheduler_trace F w xs n hn hv hl pos outRev
  have tea := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports
    (OpcodeGenerator.Label.prepare (F:=F)) (SchedulerSeed.program F) (OpcodeGenerator.program F)
    (RawEnumeration.frame (RawEnumeration.loaded w xs []) pos) w (OpcodeGenerator.prepare_code F) ta
  simp only [OpcodeGenerator.embed_prepare] at tea
  have tj := OpcodeGenerator.transfer_trace F w (SchedulerSeed.readyBank F w xs)
    (CanonicalReader.finalPositions F xs pos) w.length outRev
  obtain ⟨b,hb,tb⟩ := OpcodeGenerator.schedule_call F w xs (CanonicalReader.finalPositions F xs pos) w.length outRev
  have hl' : xs.length≤(Counter.value xs+1).size := by rw [hv,hl];exact Nat.size_le_size (by omega)
  have hbudget := VertexScheduler.budget_linear F xs (by omega) hl'
  rw [hv] at hbudget
  have h1 := hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tea tj) tb⟩
  unfold OpcodeGenerator.coefficient
  nlinarith

end TransposeFollowup.NativeExpanderShearGenerate
