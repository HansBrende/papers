import BitWord.NativeReductionIOCalls
import BitWord.NativeReductionStages
import BitWord.NativeReductionBudget

/-! Complete execution of the one fixed raw bit-to-word transposition machine.
The oracle assumption concerns only the original raw bit machine. All wrapper
setup, normalization, simulation reset, routing, cropping and output are paid. -/
namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
open NativeCountedLoop Transpose
set_option autoImplicit false
noncomputable section

/-- Every positive dimension, including the smallest one, uses the same finite
controller from entirely blank work tapes. No metadata or ruler is an input. -/
theorem complete_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    (d : ℕ) (hd : 1≤d) (A : Transpose.Matrix) :
    ∃ t≤(200000+208*NativeOracleBatch.suffixConstant M C)*Transpose.inputLength d,
      ∃ s pos,Trace M (Transpose.encode d (Transpose.entryBits d) A) t
        (cfg M (start M) (blank M) (fun _=>0) 0 [])
        (cfg M .done s pos (Transpose.inputLength d)
          ((Transpose.encode d (Transpose.entryBits d) (Transpose.transpose A)).reverse)) := by
  let w := encode d (entryBits d) A
  let out := encode d (entryBits d) (transpose A)
  have hw : w.length=inputLength d := Tape.Impl.length_encode _ _ _
  have hout : out.length=inputLength d := Tape.Impl.length_encode _ _ _
  obtain ⟨xs,hxs,hv,hl,t0,h0,tr0⟩ := prepare_call M w d hd hw
  have hh : H xs=entryBits d := by simp [H,NativePrepare.h,hv]
  have hhpos : 0<H xs := hh.symm ▸ canonical_h_pos d
  have hdim : Counter.value xs≤D xs := by simpa [D,hh,hv] using (canonical_dimension_bounds hd).1
  have hB : H xs≤B xs := tail_padding_lower hhpos
  have hD : 0<D xs := by unfold D; positivity
  let large := NativeNormalize.largeWord (Counter.value xs) (D xs) (H xs) (B xs) A
  let largeOut := NativeNormalize.largeWord (Counter.value xs) (D xs) (H xs) (B xs) (transpose A)
  have hsmall : NativeNormalize.smallWord (Counter.value xs) (H xs) A=w := by simp [NativeNormalize.smallWord,hv,hh,w]
  have hsmallOut : NativeNormalize.smallWord (Counter.value xs) (H xs) (transpose A)=out := by
    simp [NativeNormalize.smallWord,hv,hh,out]
  have j0 := jump M w (.prepare .done) (.normalize true (NativeNormalize.start true))
    (bank M w xs w ⟨[],[]⟩) (fun _=>0) w.length [] rfl
  obtain ⟨t1,h1,tr1⟩ := normalize_call M w xs ⟨[],[]⟩ true hdim hhpos hB hD A w.length
  simp only [NativeNormalize.inputWord,NativeNormalize.outputWord,ite_true,hsmall] at tr1
  have j1 := jump M w (.normalize true .done) (.half NativeHalfRuler.start)
    (bank M w xs large ⟨[],[]⟩) (fun _=>0) w.length [] rfl
  obtain ⟨t2,h2,tr2⟩ := half_call M w xs large (nword_positive xs hhpos) w.length
  have j2 := jump M w (.half .done) (.stages (NativeStages.start M))
    (bank M w xs large (Counter.marked (halfWord xs))) (fun _=>0) w.length [] rfl
  obtain ⟨t3,h3,tr3⟩ := stages_call M C hM w xs hhpos
    (padSquare (Counter.value xs) (widenMatrix (H xs) A)) w.length
  have hlargeOut : encode (D xs) (B xs) (transpose (padSquare (Counter.value xs) (widenMatrix (H xs) A)))=largeOut := by
    rw [padSquare_transpose,widen_transpose]
    rfl
  rw [hlargeOut] at tr3
  have j3 := jump M w (.stages .done) (.normalize false (NativeNormalize.start false))
    (bank M w xs largeOut (Counter.marked (halfWord xs))) (fun _=>0) w.length [] rfl
  obtain ⟨t4,h4,tr4⟩ := normalize_call M w xs (Counter.marked (halfWord xs)) false hdim hhpos hB hD
    (transpose A) w.length
  simp only [NativeNormalize.inputWord,NativeNormalize.outputWord,Bool.false_eq_true,ite_false,hsmallOut] at tr4
  have j4 := jump M w (.normalize false .done) (.output .read)
    (bank M w xs out (Counter.marked (halfWord xs))) (fun _=>0) w.length [] rfl
  obtain ⟨t5,h5,s,pos,tr5⟩ := output_call M w xs out (Counter.marked (halfWord xs)) w.length
  have j5 := jump M w (.output .done) .done s pos w.length out.reverse rfl
  have a0 := trace_trans tr0 j0
  have a1 := trace_trans a0 tr1
  have a2 := trace_trans a1 j1
  have a3 := trace_trans a2 tr2
  have a4 := trace_trans a3 j2
  have a5 := trace_trans a4 tr3
  have a6 := trace_trans a5 j3
  have a7 := trace_trans a6 tr4
  have a8 := trace_trans a7 j4
  have a9 := trace_trans a8 tr5
  have a10 := trace_trans a9 j5
  refine ⟨t0+1+t1+1+t2+1+t3+1+t4+1+t5+1,?_,s,pos,?_⟩
  · have hhalf := h2.trans (NativeHalfRuler.budget_bound (nword xs) (nword_positive xs hhpos))
    have he : 2*Counter.value (nword xs)=2*entryBits d+tailBits (entryBits d) := by
      rw [nword_value,halfAddress_double,hh]
    have hvlarge : D xs*D xs*B xs=NativeReductionBudget.volume d := by
      simpa only [D,B,hh] using (NativeReductionBudget.volume_eq d).symm
    have hword : nword xs=NativeCanonicalGenerator.fieldWord (entryBits d) .n := by simp only [nword,hh]
    rw [hw] at h0
    rw [hout] at h5
    rw [hvlarge] at h1 h4
    rw [he,hword] at hhalf
    simp only [NativeStages.perStageBudget,hh] at h3
    have hb := NativeReductionBudget.canonical_bound hd (NativeOracleBatch.suffixConstant M C)
    unfold NativeReductionBudget.total at hb
    unfold NativeReductionBudget.volume at hb h1 h4
    omega
  · simpa only [hw] using a10

end
end BitWord.NativeReductionMachine
