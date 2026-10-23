import BitWord.NativeReductionCalls
import BitWord.NativeReductionStageFrame

namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

theorem nword_value (xs : List Bool) : Counter.value (nword xs)=halfAddress (H xs) :=
  (NativeCanonicalGenerator.field_values (H xs)).2.2.1

theorem nword_positive (xs : List Bool) (hh : 0<H xs) : 0<Counter.value (nword xs) := by
  rw [nword_value]
  unfold halfAddress
  omega

theorem halfWord_length (xs : List Bool) : (halfWord xs).length=2^(2*H xs+tailBits (H xs)-1) := by
  simp only [halfWord,List.length_replicate,nword_value,halfAddress_double]

theorem stages_call (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    (w xs : List Bool) (hh : 0<H xs) (A : Transpose.Matrix) (ip : ℤ) :
    ∃ t≤13*NativeStages.perStageBudget M C (2*H xs+tailBits (H xs)) (2*H xs+2),Trace M w t
      (cfg M (.stages (NativeStages.start M))
        (bank M w xs (Transpose.encode (D xs) (B xs) A) (Counter.marked (halfWord xs))) (fun _=>0) ip [])
      (cfg M (.stages .done)
        (bank M w xs (Transpose.encode (D xs) (B xs) (Transpose.transpose A))
          (Counter.marked (halfWord xs))) (fun _=>0) ip []) := by
  let b := matrixBank (H xs) (tailBits (H xs)) A
  let gs := NativeStages.padded (canonicalGates (H xs))
  have hg := NativeStages.padded_legal _ (canonicalGates_legal hh)
  obtain ⟨t,ht,htr⟩ := NativeStages.complete_trace M C hM (by omega : 0<2*H xs+tailBits (H xs))
    gs hg b (halfWord xs) (halfWord_length xs) (params xs) (codes xs)
    (fun i=>NativeCanonicalGenerator.slot_parameter (H xs) i) (fun _=>rfl)
    (2*H xs+2) (fun i=>NativeCanonicalGenerator.slot_parameter_length_linear (H xs) i)
  let result := flattenBank (NativeStages.after gs hg b 13)
  have he := NativeBindingCalls.restoring_call (stagesBinding M) Label.stages (NativeStages.program M)
    (NativeIO.workProgram (program M)) (stages_code M) (NativeStages.start M) .done
    (bank M w xs (flattenBank b) (Counter.marked (halfWord xs))) (fun _=>0)
    (NativeStages.bank M result (halfWord xs) (params xs) (codes xs)) t
    (by rw [stages_projection]; exact htr)
  have hi : flattenBank b=Transpose.encode (D xs) (B xs) A := matrixBank_flatten _ _ A
  have ho : result=Transpose.encode (D xs) (B xs) (Transpose.transpose A) := by
    dsimp [result,gs,hg,b]
    rw [NativeStages.canonical_after hh,canonical_flatten_transpose hh]
    rfl
  have hh := NativeIO.lift_work_trace (program M) w ip [] he
  refine ⟨t,ht,?_⟩
  simpa only [stages_values,hi,ho,cfg,NativeExpanderShearFrames.cfg] using hh

end
end BitWord.NativeReductionMachine
