import TransposeFollowup.PortBindingFrame
import TransposeFollowup.InputMeasureMachine

namespace TransposeFollowup.InputMeasure
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem load_work_embed (pc : RawInputCopy.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 0).ports Label.load (RawInputCopy.workCfg pc word (pos 0)) (frame s pos)=
      workCfg (.load pc) (Function.update s 0 word) pos := by
  unfold MicrocodeEmbedding.embed RawInputCopy.workCfg workCfg frame
  simp only [← (singleBinding 0).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> simp [singleBinding,FinitePortBinding.values]

theorem embed_load (pc : RawInputCopy.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed (singleBinding 0).ports Label.load (RawInputCopy.cfg pc word (pos 0) ip outRev) (frame s pos)=
      cfg (.load pc) (Function.update s 0 word) pos ip outRev := by
  unfold NativeIOEmbedding.embed RawInputCopy.cfg cfg
  rw [load_work_embed]

theorem copy_positions (finish : Bool) (pos : Port → ℤ) :
    (copyBinding finish).values (fun p => pos (copyPorts finish p)) pos=pos := by
  funext p;cases finish <;> fin_cases p <;> rfl

theorem embed_copy (finish : Bool) (pc : NativeMappedCopy.Label) (source target : Tape Bool)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (copyBinding finish).ports (Label.copy finish)
      (NativeMappedCopy.cfg pc source target (fun p => pos (copyPorts finish p))) (frame s pos)=
      workCfg (.copy finish pc) ((copyBinding finish).values (NativeMappedCopy.bank source target) s) pos := by
  exact (copyBinding finish).embed_bank_project _ _ _ _ _

theorem embed_scan (pc : MeasuredScan.Label) (source : Tape Bool) (cw : List Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (copyBinding false).ports Label.scan
      (MeasuredScan.cfg pc source cw (fun p => pos (copyPorts false p))) (frame s pos)=
      workCfg (.scan pc) ((copyBinding false).values (MeasuredScan.bank source cw) s) pos := by
  exact (copyBinding false).embed_bank_project _ _ _ _ _

theorem embed_erase (pc : NativeErase.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 1).ports Label.erase (NativeErase.cfg pc word (fun _ => pos 1)).denote (frame s pos)=
      workCfg (.erase pc) (Function.update s 1 word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus workCfg frame
  simp only [← (singleBinding 1).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> simp [singleBinding,FinitePortBinding.values]

theorem jump_trace (w : List Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool)
    (h : program pc=.work (.jump next)) : Trace w 1 (cfg pc s pos ip outRev) (cfg next s pos ip outRev) :=
  NativeIO.jump_trace _ _ _ _ h

theorem load_call (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ 5*w.length+10, Trace w t (cfg start initial pos 0 outRev)
      (cfg (.load .done) (loaded w) pos w.length outRev) := by
  obtain ⟨t,ht,htr⟩ := RawInputCopy.complete_trace w (pos 0) outRev
  have he := NativeIOEmbedding.trace_embed (singleBinding 0).ports Label.load RawInputCopy.program program
    (frame initial pos) w load_code htr
  have hi : Function.update initial 0 (⟨[],[]⟩:Tape Bool)=initial := Function.update_eq_self _ _
  have hf : Function.update initial 0 (Counter.marked w)=loaded w := by
    funext p;fin_cases p <;> simp [initial,loaded,bank]
  exact ⟨t,ht,by simpa only [embed_load,hi,hf,start] using he⟩

abbrev WorkTrace := OperationalTrace.Trace (NativeMicrocode.step (NativeIO.workProgram program))
  (NativeMicrocode.Active (NativeIO.workProgram program))

theorem ones_work_call (w : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 6*w.length+14, WorkTrace t (workCfg (.copy false (.init (.erase 0))) (loaded w) pos)
      (workCfg (.copy false (.seal .done)) (seeded w) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace (mapFor false) w (fun p => pos (copyPorts false p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding false).ports (Label.copy false)
    (NativeMappedCopy.program (mapFor false)) (NativeIO.workProgram program) (frame (loaded w) pos) (copy_code false) htr
  have hi : (copyBinding false).values (NativeMappedCopy.bank (Counter.marked w) ⟨[],[]⟩) (loaded w)=loaded w := by
    funext p;fin_cases p <;> rfl
  have hf : (copyBinding false).values (NativeMappedCopy.bank (Counter.marked w) (Counter.marked (w.map (mapFor false)))) (loaded w)=seeded w := by
    funext p;fin_cases p <;> simp [copyBinding,copyPorts,FinitePortBinding.values,NativeMappedCopy.bank,
      mapFor,loaded,seeded,bank,List.map_const']
  exact ⟨t,ht,by simpa only [embed_copy,hi,hf] using he⟩

theorem ones_call (w : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*w.length+14, Trace w t (cfg (.copy false (.init (.erase 0))) (loaded w) pos ip outRev)
      (cfg (.copy false (.seal .done)) (seeded w) pos ip outRev) := by
  obtain ⟨t,ht,htr⟩:=ones_work_call w pos
  exact ⟨t,ht,by simpa only [cfg] using NativeIO.lift_work_trace program w ip outRev htr⟩

theorem scan_work_call (w : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 16*w.length+6, WorkTrace t (workCfg (.scan .read) (seeded w) pos)
      (workCfg (.scan .done) (counted w) pos) := by
  obtain ⟨t,ht,htr⟩ := MeasuredScan.length_count_trace w (fun p => pos (copyPorts false p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding false).ports Label.scan MeasuredScan.program
    (NativeIO.workProgram program) (frame (seeded w) pos) scan_code htr
  have hi : (copyBinding false).values (MeasuredScan.bank (Counter.marked w) (List.replicate w.length true)) (seeded w)=seeded w := by
    funext p;fin_cases p <;> rfl
  have hf : (copyBinding false).values (MeasuredScan.bank (Counter.marked w) (MeasuredWord.counted w.length)) (seeded w)=counted w := by
    funext p;fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [embed_scan,hi,hf] using he⟩

theorem scan_call (w : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 16*w.length+6, Trace w t (cfg (.scan .read) (seeded w) pos ip outRev)
      (cfg (.scan .done) (counted w) pos ip outRev) := by
  obtain ⟨t,ht,htr⟩:=scan_work_call w pos
  exact ⟨t,ht,by simpa only [cfg] using NativeIO.lift_work_trace program w ip outRev htr⟩

theorem complement_work_call (w : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 6*w.length+14, WorkTrace t (workCfg (.copy true (.init (.erase 0))) (counted w) pos)
      (workCfg (.copy true (.seal .done)) (copied w) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace (mapFor true) (MeasuredWord.counted w.length) (fun p => pos (copyPorts true p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding true).ports (Label.copy true)
    (NativeMappedCopy.program (mapFor true)) (NativeIO.workProgram program) (frame (counted w) pos) (copy_code true) htr
  have hi : (copyBinding true).values (NativeMappedCopy.bank (Counter.marked (MeasuredWord.counted w.length)) ⟨[],[]⟩) (counted w)=counted w := by
    funext p;fin_cases p <;> rfl
  have hf : (copyBinding true).values (NativeMappedCopy.bank (Counter.marked (MeasuredWord.counted w.length))
      (Counter.marked ((MeasuredWord.counted w.length).map (mapFor true)))) (counted w)=copied w := by
    funext p;fin_cases p <;> rfl
  refine ⟨t,?_,by simpa only [embed_copy,hi,hf] using he⟩
  simpa only [MeasuredWord.counted,MeasuredWord.after_length,List.length_replicate] using ht

theorem complement_call (w : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*w.length+14, Trace w t (cfg (.copy true (.init (.erase 0))) (counted w) pos ip outRev)
      (cfg (.copy true (.seal .done)) (copied w) pos ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complement_work_call w pos
  exact ⟨t,ht,by simpa only [cfg] using NativeIO.lift_work_trace program w ip outRev htr⟩

theorem erase_work_call (w : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*w.length+4, WorkTrace t (workCfg (.erase 2) (copied w) pos)
      (workCfg (.erase 0) (final w) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace (MeasuredWord.counted w.length) (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed (singleBinding 1).ports Label.erase NativeErase.program
    (NativeIO.workProgram program) (frame (copied w) pos) erase_code htr
  have hi : Function.update (copied w) 1 (Counter.marked (MeasuredWord.counted w.length))=copied w := Function.update_eq_self _ _
  have hf : Function.update (copied w) 1 (⟨[],[]⟩:Tape Bool)=final w := by
    funext p;fin_cases p <;> simp [copied,final,bank]
  refine ⟨t,?_,by simpa only [embed_erase,hi,hf] using he⟩
  simpa only [MeasuredWord.counted,MeasuredWord.after_length,List.length_replicate] using ht

theorem erase_call (w : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*w.length+4, Trace w t (cfg (.erase 2) (copied w) pos ip outRev)
      (cfg (.erase 0) (final w) pos ip outRev) := by
  obtain ⟨t,ht,htr⟩:=erase_work_call w pos
  exact ⟨t,ht,by simpa only [cfg] using NativeIO.lift_work_trace program w ip outRev htr⟩


end TransposeFollowup.InputMeasure
