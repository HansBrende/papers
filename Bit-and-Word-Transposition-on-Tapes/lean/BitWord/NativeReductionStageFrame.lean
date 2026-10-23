import BitWord.NativeReductionLayout

/-! Exact framing of the thirteen-slot machine in the shared raw reduction
workspace. Generated parameter/opcode tapes are read in their original locations. -/
namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

private theorem stages_data_contents (M : Transpose.TM) (raw fs : List Bool)
    (ps cs : Fin 13 → List Bool) (p : NativeStages.DataPort M) :
    NativeStages.bank M raw fs ps cs (.inl p)=
      if p=NativeGate.main M then Counter.marked raw
      else if p=NativeGate.halfRuler M then Counter.marked fs else ⟨[],[]⟩ := by
  cases p with
  | inr p => fin_cases p <;> simp [NativeStages.bank,NativeStages.parameter,NativeStages.opcode,
      NativeGate.bank,NativeGate.main,NativeGate.opcode,NativeGate.halfRuler]
  | inl p => cases p with
    | inr p => fin_cases p <;> simp [NativeStages.bank,NativeStages.parameter,NativeStages.opcode,
        NativeGate.bank,NativeGate.main,NativeGate.opcode,NativeGate.halfRuler,
        NativeSuffixPowered.bank,NativeSuffixPowered.layout,NativeSuffixPowered.parameter]
    | inl p => cases p with
      | inr p => fin_cases p <;> simp [NativeStages.bank,NativeStages.parameter,NativeStages.opcode,
          NativeGate.bank,NativeGate.main,NativeGate.opcode,NativeGate.halfRuler,
          NativeSuffixPowered.bank,NativeSuffixPowered.layout,NativeSuffixPowered.parameter,
          NativeSuffixPowered.innerBank,NativeOracleBlock.layout,NativeOracleBlock.source]
      | inl p => cases p with
        | data p => cases p <;> rfl
        | log r => rfl

theorem stages_projection (M : Transpose.TM) (w xs raw fs : List Bool) :
    (fun p => bank M w xs raw (Counter.marked fs) ((stagesBinding M).ports p))=
      NativeStages.bank M raw fs (params xs) (codes xs) := by
  funext p
  rw [stagesBinding_ports]
  cases p with
  | inl p =>
    rw [stages_data_contents]
    by_cases hm : p=NativeGate.main M
    · subst p; simp [stagesPort,dataPort]
    by_cases hc : p=NativeGate.halfRuler M
    · subst p; simp [stagesPort,dataPort,hm]
    · simp [stagesPort,dataPort,hm,hc,bank_data]
  | inr p =>
    rcases p with ⟨b,i⟩
    cases b with
    | false =>
      change bank M w xs raw (Counter.marked fs)
        (.prepare (NativePrepare.generatorPort (.parameter i)))=Counter.marked (params xs i)
      rw [bank_prepare M w xs raw _ _ (by simp [NativePrepare.generatorPort,NativePrepare.mainPort])]
      exact NativePrepare.final_field w xs (.parameter i)
    | true =>
      change bank M w xs raw (Counter.marked fs)
        (.prepare (NativePrepare.generatorPort (.opcode i)))=Counter.marked (codes xs i)
      rw [bank_prepare M w xs raw _ _ (by simp [NativePrepare.generatorPort,NativePrepare.mainPort])]
      have hf := NativePrepare.final_field w xs (.opcode i)
      simpa only [H,codes,NativeCanonicalGenerator.slot_opcode,NativeCanonicalGenerator.smallPort] using hf

/-- The stage family changes only the main raw bank; every descriptor, ruler,
and auxiliary tape remains in the declared global configuration. -/
theorem stages_values (M : Transpose.TM) (w xs raw out fs : List Bool) :
    (stagesBinding M).values (NativeStages.bank M out fs (params xs) (codes xs))
      (bank M w xs raw (Counter.marked fs))=bank M w xs out (Counter.marked fs) := by
  let i : NativeStages.Port M := .inl (NativeGate.main M)
  have hi : (stagesBinding M).ports i=main M := by simp [i,stagesPort,dataPort]
  have hp : NativeStages.bank M out fs (params xs) (codes xs)=
      Function.update (fun p => bank M w xs raw (Counter.marked fs) ((stagesBinding M).ports p))
        i (Counter.marked out) := by
    rw [←stages_projection M w xs out fs,←bank_update_main M w xs raw out (Counter.marked fs)]
    funext p
    by_cases h : p=i
    · subst p; simp only [hi,Function.update_self]
    · have hn : (stagesBinding M).ports p≠main M := by
        intro he
        exact h ((stagesBinding M).ports.injective (he.trans hi.symm))
      simp only [Function.update_of_ne h,Function.update_of_ne hn]
  rw [hp,←(stagesBinding M).values_update,(stagesBinding M).values_project,hi,bank_update_main]

end
end BitWord.NativeReductionMachine
