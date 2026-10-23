import BitWord.NativeReductionLayout

namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

theorem prepare_call (M : Transpose.TM) (w : List Bool) (d : ℕ) (hd : 1≤d)
    (hw : w.length=Transpose.inputLength d) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
    ∃ t≤40000*w.length,Trace M w t (cfg M (start M) (blank M) (fun _=>0) 0 [])
      (cfg M (.prepare .done) (bank M w xs w ⟨[],[]⟩) (fun _=>0) w.length []) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := NativePrepare.complete_trace w d hd hw (fun _=>0) []
  have he := NativeIOEmbedding.trace_embed (prepareBinding M).ports Label.prepare NativePrepare.program
    (program M) (frame (blank M) (fun _=>0)) w (prepare_code M) htr
  change Trace M w t
    (NativeIOEmbedding.embed (prepareBinding M).ports Label.prepare
      (NativeExpanderShearFrames.cfg NativePrepare.start NativePrepare.initial (fun _=>0) 0 []) _)
    (NativeIOEmbedding.embed (prepareBinding M).ports Label.prepare
      (NativeExpanderShearFrames.cfg .done (NativePrepare.final w xs) (fun _=>0) w.length []) _) at he
  rw [embed_io,embed_io] at he
  have hi : (prepareBinding M).values NativePrepare.initial (blank M)=blank M := by
    funext p
    simp only [FinitePortBinding.values]
    split <;> rfl
  have hp : (prepareBinding M).values (fun _=> (0:ℤ)) (fun _=>0)=fun _=>0 :=
    (prepareBinding M).values_project (fun _ : Port M => (0:ℤ))
  refine ⟨xs,hx,hv,hl,t,ht,?_⟩
  simpa only [hi,hp,prepare_values,bank_initial,start,cfg] using he

theorem output_call (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) (ip : ℤ) :
    ∃ t≤3*raw.length+1,∃ s pos,Trace M w t
      (cfg M (.output .read) (bank M w xs raw clock) (fun _=>0) ip [])
      (cfg M (.output .done) s pos ip raw.reverse) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorOutput.output_trace raw (fun _=>0) w ip []
  have he := NativeIOEmbedding.trace_embed (outputBinding M).ports Label.output NativeMatchingXorOutput.program
    (program M) (frame (bank M w xs raw clock) (fun _=>0)) w (output_code M) htr
  change Trace M w t
    (NativeIOEmbedding.embed (outputBinding M).ports Label.output
      (NativeExpanderShearFrames.cfg .read (fun _=>Counter.marked raw) (fun _=>0) ip []) _)
    (NativeIOEmbedding.embed (outputBinding M).ports Label.output
      (NativeExpanderShearFrames.cfg .done (fun _=>⟨(symbols raw).reverse++[.start],[.stop]⟩)
        (fun _=> (0:ℤ)+raw.length) ip (raw.reverse++[])) _) at he
  rw [embed_io,embed_io] at he
  have hi : (outputBinding M).values (fun _=>Counter.marked raw) (bank M w xs raw clock)=bank M w xs raw clock := by
    have hp : (fun p=>bank M w xs raw clock ((outputBinding M).ports p))=(fun _=>Counter.marked raw) := by
      funext p; exact bank_main M w xs raw clock
    rw [←hp,FinitePortBinding.values_project]
  have hp : (outputBinding M).values (fun _=> (0:ℤ)) (fun _=>0)=fun _=>0 :=
    (outputBinding M).values_project (fun _ : Port M => (0:ℤ))
  exact ⟨t,ht,_,_,by simpa only [hi,hp,List.append_nil,cfg] using he⟩

end
end BitWord.NativeReductionMachine
