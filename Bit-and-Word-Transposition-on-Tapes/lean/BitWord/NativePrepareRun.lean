import BitWord.NativePrepare

namespace BitWord.NativePrepare
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop

theorem bootstrap_call (w : List Bool) (d : ℕ) (hd : 1≤d) (hw : w.length=Transpose.inputLength d)
    (pos : Port → ℤ) (out : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
    ∃ t≤8300*w.length+50*d.size+89,Trace w t (cfg start initial pos 0 out)
      (cfg (.bootstrap .done) (loaded w xs) pos w.length out) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := NativeBootstrap.complete_trace w d hd hw
    (fun p => pos (.bootstrap p)) out
  have he := NativeIOEmbedding.trace_embed bootstrapBinding.ports Label.bootstrap NativeBootstrap.program program
    (frame initial pos) w bootstrap_code htr
  change Trace w t
    (NativeIOEmbedding.embed bootstrapBinding.ports Label.bootstrap
      (NativeExpanderShearFrames.cfg NativeBootstrap.start NativeBootstrap.initial
        (fun p => pos (.bootstrap p)) 0 out) _)
    (NativeIOEmbedding.embed bootstrapBinding.ports Label.bootstrap
      (NativeExpanderShearFrames.cfg .done (NativeBootstrap.final w xs)
        (fun p => pos (.bootstrap p)) w.length out) _) at he
  rw [embed_io,embed_io] at he
  have hi : bootstrapBinding.values NativeBootstrap.initial initial=initial := by funext p; cases p <;> rfl
  have hp : bootstrapBinding.values (fun p => pos (.bootstrap p)) pos=pos := by funext p; cases p <;> rfl
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [hi,hp,start,cfg,loaded] using he⟩

theorem generator_call (w xs : List Bool) (pos : Port → ℤ) (ip : ℤ) (out : List Bool) :
    ∃ t≤NativeCanonicalGenerator.budget (h xs),Trace w t
      (cfg (.generator NativeCanonicalGenerator.start) (loaded w xs) pos ip out)
      (cfg (.generator .done) (generated w xs) pos ip out) := by
  obtain ⟨t,ht,htr⟩ := NativeCanonicalGenerator.complete_trace (h xs)
    (fun p => pos (generatorBinding.ports p))
  have he := NativeBindingCalls.restoring_call generatorBinding Label.generator NativeCanonicalGenerator.program
    (NativeIO.workProgram program) generator_code NativeCanonicalGenerator.start .done
    (loaded w xs) pos (NativeCanonicalGenerator.final (h xs)) t
    (by rw [show (fun p => loaded w xs (generatorBinding.ports p))=NativeCanonicalGenerator.initial (h xs)
          from generator_initial w xs]; exact htr)
  exact ⟨t,ht,NativeIO.lift_work_trace program w ip out he⟩

theorem rulers_call (w xs : List Bool) (pos : Port → ℤ) (ip : ℤ) (out : List Bool) :
    ∃ t≤NativeRulers.budget xs (hword xs) (wword xs),Trace w t
      (cfg (.rulers NativeRulers.start) (generated w xs) pos ip out)
      (cfg (.rulers .done) (final w xs) pos ip out) := by
  obtain ⟨t,ht,htr⟩ := NativeRulers.complete_trace xs (hword xs) (wword xs)
    (fun p => pos (rulersBinding.ports p))
  have he := NativeBindingCalls.restoring_call rulersBinding Label.rulers NativeRulers.program
    (NativeIO.workProgram program) rulers_code NativeRulers.start .done (generated w xs) pos
    (NativeRulers.final xs (hword xs) (wword xs)) t
    (by rw [show (fun p => generated w xs (rulersBinding.ports p))=NativeRulers.initial xs (hword xs) (wword xs)
          from rulers_initial w xs]; exact htr)
  exact ⟨t,ht,NativeIO.lift_work_trace program w ip out he⟩

theorem jump (w : List Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (out : List Bool)
    (hc : program pc=.work (.jump next)) : Trace w 1 (cfg pc s pos ip out) (cfg next s pos ip out) :=
  NativeIO.jump_trace program w (cfg pc s pos ip out) next hc

/-- Setup from completely blank work tapes. The original read-only input is
scanned once into the payload bank; every work head finishes at its own origin. -/
theorem complete_trace (w : List Bool) (d : ℕ) (hd : 1≤d) (hw : w.length=Transpose.inputLength d)
    (pos : Port → ℤ) (out : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
    ∃ t≤40000*w.length,Trace w t (cfg start initial pos 0 out)
      (cfg .done (final w xs) pos w.length out) := by
  obtain ⟨xs,hx,hv,hl,t0,h0,tr0⟩ := bootstrap_call w d hd hw pos out
  have j0 := jump w (.bootstrap .done) (.generator NativeCanonicalGenerator.start) (loaded w xs) pos w.length out rfl
  obtain ⟨t1,h1,tr1⟩ := generator_call w xs pos w.length out
  have j1 := jump w (.generator .done) (.rulers NativeRulers.start) (generated w xs) pos w.length out rfl
  obtain ⟨t2,h2,tr2⟩ := rulers_call w xs pos w.length out
  have j2 := jump w (.rulers .done) .done (final w xs) pos w.length out rfl
  have s0 := trace_trans tr0 j0
  have s1 := trace_trans tr1 j1
  have s2 := trace_trans tr2 j2
  have acc1 := trace_trans s0 s1
  have acc2 := trace_trans acc1 s2
  refine ⟨xs,hx,hv,hl,_,?_,acc2⟩
  have hh : h xs=Transpose.entryBits d := by simp [h,hv]
  have hgen := h1.trans (NativeCanonicalGenerator.budget_linear (h xs))
  rw [hh] at hgen
  have hrulers := canonical_rulers_budget hd xs (hword xs) (wword xs) hv hl
    (by simp [hword,MeasuredWord.result_value,hh])
    (by simp [hword,MeasuredWord.result_length,hh])
    (by simpa only [wword,hh] using (NativeCanonicalGenerator.field_values (h xs)).2.1)
    (by simpa only [wword,hh] using NativeCanonicalGenerator.field_word_length (h xs) .w)
  have hr := h2.trans hrulers
  obtain ⟨hP,_,hhP,hsP,_,_⟩ := canonical_input_bounds hd
  rw [←hw] at hP hhP hsP hr
  omega

end BitWord.NativePrepare
