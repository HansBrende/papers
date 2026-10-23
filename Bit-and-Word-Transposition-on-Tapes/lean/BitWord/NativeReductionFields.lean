import BitWord.NativeReductionLayout

namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

theorem bank_generator (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool)
    (p : NativeCanonicalGenerator.Port) :
    bank M w xs raw clock (.prepare (NativePrepare.generatorPort p))=NativeCanonicalGenerator.final (H xs) p := by
  rw [bank_prepare M w xs raw clock _ (by by_cases hp : p=.work .h <;> simp [NativePrepare.generatorPort,hp,NativePrepare.mainPort,NativeBootstrap.payload])]
  exact NativePrepare.final_generator w xs p

theorem bank_field (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool)
    (p : NativeSmallDescriptors.Port) :
    bank M w xs raw clock (.prepare (NativePrepare.generatorPort (NativeCanonicalGenerator.smallPort p)))=
      Counter.marked (NativeCanonicalGenerator.fieldWord (H xs) p) := by
  rw [bank_generator,NativeCanonicalGenerator.final_fields]

theorem bank_ruler (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool)
    (p : NativeRulers.Port) :
    bank M w xs raw clock (.prepare (NativePrepare.rulerPort p))=
      NativeRulers.contents xs (NativePrepare.hword xs) (NativePrepare.wword xs) p := by
  rw [bank_prepare M w xs raw clock _ (by cases p <;>
    simp [NativePrepare.rulerPort,NativePrepare.mainPort,NativeBootstrap.payload,NativeBootstrap.dimension])]
  exact NativePrepare.final_rulers w xs p

theorem normalize_projection (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) :
    (fun p => bank M w xs raw clock ((normalizeBinding M).ports p))=
      NativeNormalize.bank (Counter.marked raw) ⟨[],[]⟩ ⟨[],[]⟩ (Counter.value xs) (D xs) (H xs) (B xs) := by
  have hv : Counter.value (NativePrepare.wword xs)=tailBits (H xs) :=
    (NativeCanonicalGenerator.field_values (H xs)).2.1
  have hh : Counter.value (NativePrepare.hword xs)=H xs := MeasuredWord.result_value _
  funext p
  fin_cases p
  · exact bank_main M w xs raw clock
  · exact bank_normalize M w xs raw clock 0
  · exact bank_normalize M w xs raw clock 1
  · simpa [normalizeBinding_ports,normalizePorts,NativeNormalize.bank,NativeRulers.contents,hh,NativeResizeScan.markedRuler] using bank_ruler M w xs raw clock .h
  · simpa [normalizeBinding_ports,normalizePorts,NativeNormalize.bank,NativeRulers.contents,hv,NativeResizeScan.markedRuler,B] using bank_ruler M w xs raw clock .B
  · simpa [normalizeBinding_ports,normalizePorts,NativeNormalize.bank,NativeRulers.contents,NativeResizeScan.markedRuler] using bank_ruler M w xs raw clock .d
  · simpa [normalizeBinding_ports,normalizePorts,NativeNormalize.bank,NativeRulers.contents,hh,NativeResizeScan.markedRuler,D] using bank_ruler M w xs raw clock .D
  · simpa [normalizeBinding_ports,normalizePorts,NativeNormalize.bank,NativeRulers.contents,hv,NativeResizeScan.markedRuler,B] using bank_ruler M w xs raw clock .dB
  · simpa [normalizeBinding_ports,normalizePorts,NativeNormalize.bank,NativeRulers.contents,hh,hv,NativeResizeScan.markedRuler,D,B] using bank_ruler M w xs raw clock .DB

@[simp] theorem normalize_bank_update (a b c v : Tape Bool) (d D h B : ℕ) :
    Function.update (NativeNormalize.bank a b c d D h B) 0 v=NativeNormalize.bank v b c d D h B := by
  funext i; fin_cases i <;> simp [NativeNormalize.bank]

theorem normalize_values (M : Transpose.TM) (w xs raw out : List Bool) (clock : Tape Bool) :
    (normalizeBinding M).values (NativeNormalize.bank (Counter.marked out) ⟨[],[]⟩ ⟨[],[]⟩
      (Counter.value xs) (D xs) (H xs) (B xs)) (bank M w xs raw clock)=bank M w xs out clock := by
  rw [←normalize_bank_update (Counter.marked raw) ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked out),
    ←normalize_projection M w xs raw clock,←FinitePortBinding.values_update,FinitePortBinding.values_project]
  change Function.update (bank M w xs raw clock) (main M) (Counter.marked out)=_
  exact bank_update_main M w xs raw out clock

theorem half_projection (M : Transpose.TM) (w xs raw : List Bool) :
    (fun p => bank M w xs raw ⟨[],[]⟩ ((halfBinding M).ports p))=
      NativeHalfRuler.bank (Counter.marked (nword xs)) ⟨[],[]⟩ ⟨[],[]⟩ := by
  funext p
  cases p with
  | inl p => cases p <;> simp [halfBinding_ports,halfPort,NativeHalfRuler.bank]
  | inr p =>
    change bank M w xs raw _ (.prepare (NativePrepare.generatorPort (NativeCanonicalGenerator.smallPort .n)))=_
    exact bank_field M w xs raw _ .n

@[simp] theorem half_bank_update (a b c v : Tape Bool) :
    Function.update (NativeHalfRuler.bank a b c) NativeHalfRuler.result v=NativeHalfRuler.bank a b v := by
  funext i; cases i with
  | inl i => cases i <;> simp [NativeHalfRuler.bank,NativeHalfRuler.result]
  | inr i => simp [NativeHalfRuler.bank,NativeHalfRuler.result]

theorem half_values (M : Transpose.TM) (w xs raw : List Bool) (clock : Tape Bool) :
    (halfBinding M).values (NativeHalfRuler.bank (Counter.marked (nword xs)) ⟨[],[]⟩ clock)
      (bank M w xs raw ⟨[],[]⟩)=bank M w xs raw clock := by
  rw [←half_bank_update (Counter.marked (nword xs)) ⟨[],[]⟩ ⟨[],[]⟩ clock,
    ←half_projection M w xs raw,←FinitePortBinding.values_update,FinitePortBinding.values_project]
  change Function.update (bank M w xs raw ⟨[],[]⟩) (.data (NativeGate.halfRuler M)) clock=_
  exact bank_update_clock M w xs raw _ clock

end
end BitWord.NativeReductionMachine
