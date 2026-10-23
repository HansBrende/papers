import BitWord.NativeReductionFields

namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
open NativeCountedLoop
set_option autoImplicit false
noncomputable section

theorem normalize_call (M : Transpose.TM) (w xs : List Bool) (clock : Tape Bool)
    (expand : Bool) (hd : Counter.value xs≤D xs) (hh : 0<H xs) (hB : H xs≤B xs) (hD : 0<D xs)
    (A : Transpose.Matrix) (ip : ℤ) :
    ∃ t≤200*(D xs*D xs*B xs)+200,Trace M w t
      (cfg M (.normalize expand (NativeNormalize.start expand))
        (bank M w xs (NativeNormalize.inputWord expand (Counter.value xs) (D xs) (H xs) (B xs) A) clock)
        (fun _=>0) ip [])
      (cfg M (.normalize expand .done)
        (bank M w xs (NativeNormalize.outputWord expand (Counter.value xs) (D xs) (H xs) (B xs) A) clock)
        (fun _=>0) ip []) := by
  obtain ⟨t,ht,htr⟩ := NativeNormalize.complete_trace expand (Counter.value xs) (D xs) (H xs) (B xs)
    hd hh hB hD A (fun _=>0)
  let raw := NativeNormalize.inputWord expand (Counter.value xs) (D xs) (H xs) (B xs) A
  let out := NativeNormalize.outputWord expand (Counter.value xs) (D xs) (H xs) (B xs) A
  have he := NativeBindingCalls.restoring_call (normalizeBinding M) (Label.normalize expand)
    (NativeNormalize.program expand) (NativeIO.workProgram (program M)) (normalize_code M expand)
    (NativeNormalize.start expand) .done (bank M w xs raw clock) (fun _=>0)
    (NativeNormalize.bank (Counter.marked out) ⟨[],[]⟩ ⟨[],[]⟩ (Counter.value xs) (D xs) (H xs) (B xs)) t
    (by rw [normalize_projection]; exact htr)
  have hh := NativeIO.lift_work_trace (program M) w ip [] he
  exact ⟨t,ht,by simpa only [normalize_values,cfg,NativeExpanderShearFrames.cfg] using hh⟩

def halfWord (xs : List Bool) := List.replicate (2^(2*Counter.value (nword xs)-1)) true

theorem half_call (M : Transpose.TM) (w xs raw : List Bool) (hx : 0<Counter.value (nword xs)) (ip : ℤ) :
    ∃ t≤NativeHalfRuler.budget (nword xs),Trace M w t
      (cfg M (.half NativeHalfRuler.start) (bank M w xs raw ⟨[],[]⟩) (fun _=>0) ip [])
      (cfg M (.half .done) (bank M w xs raw (Counter.marked (halfWord xs))) (fun _=>0) ip []) := by
  obtain ⟨t,ht,htr⟩ := NativeHalfRuler.complete_trace (nword xs) hx (fun _=>0)
  have he := NativeBindingCalls.restoring_call (halfBinding M) Label.half NativeHalfRuler.program
    (NativeIO.workProgram (program M)) (half_code M) NativeHalfRuler.start .done
    (bank M w xs raw ⟨[],[]⟩) (fun _=>0)
    (NativeHalfRuler.bank (Counter.marked (nword xs)) ⟨[],[]⟩ (Counter.marked (halfWord xs))) t
    (by rw [half_projection]; exact htr)
  have hh := NativeIO.lift_work_trace (program M) w ip [] he
  exact ⟨t,ht,by simpa only [half_values,cfg,NativeExpanderShearFrames.cfg] using hh⟩


end
end BitWord.NativeReductionMachine
