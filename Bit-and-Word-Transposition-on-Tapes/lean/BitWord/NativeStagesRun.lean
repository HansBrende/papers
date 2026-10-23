import BitWord.NativeStages

namespace BitWord.NativeStages
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section

def after {N : ℕ} (g : Fin 13 → Option Gate) (hg : ∀ i,NativeGate.Legal N (g i))
    (b : Address N → Bool) : ℕ → Address N → Bool
  | 0 => b
  | n+1 => if hn : n<13 then NativeGate.moved (g ⟨n,hn⟩) (hg ⟨n,hn⟩) (after g hg b n)
      else after g hg b n

@[simp] theorem gate_positions_zero (M : Transpose.TM) :
    NativeGate.positions M 0 0 0 0 (fun _ => 0)=fun _ => 0 := by
  have h3 : (![0,0,0] : Fin 3 → ℤ)=fun _ => 0 := by funext i; fin_cases i <;> rfl
  have h4 : (![0,0,0,0] : Fin 4 → ℤ)=fun _ => 0 := by funext i; fin_cases i <;> rfl
  have hb : NativeOracleBlock.layout M (0:ℤ) 0 0 (fun _ => 0)=fun _ => 0 := by
    funext p
    cases p with
    | inl p => cases p with
      | data p => cases p <;> rfl
      | log p => rfl
    | inr p => rfl
  unfold NativeGate.positions NativeSuffixPowered.positions NativeOracleBlock.blockPos
  rw [h4,h3,hb]
  funext p
  cases p with
  | inl p => cases p <;> rfl
  | inr p => rfl

theorem stage_call (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C) {N : ℕ} (hN : 0<N)
    (i : Fin 13) (g : Option Gate) (hg : NativeGate.Legal N g) (b : Address N → Bool)
    (fs : List Bool) (hfs : fs.length=2^(N-1)) (params codes : Fin 13 → List Bool)
    (hp : Counter.value (params i)=NativeSmallDescriptors.parameterValue g)
    (hc : codes i=NativeSmallDescriptors.opcodeWord g) :
    ∃ t≤NativeGate.budget M C N (params i)+1,Trace M t
      (cfg M (entry M i.val) (bank M (flattenBank b) fs params codes) (fun _ => 0))
      (cfg M (entry M (i.val+1)) (bank M (flattenBank (NativeGate.moved g hg b)) fs params codes) (fun _ => 0)) := by
  obtain ⟨t,ht,htr⟩ := NativeGate.complete_trace M C hM hN g hg b (params i) fs hp hfs 0 0 0 0 (fun _ => 0)
  rw [gate_positions_zero,←hc] at htr
  let s := bank M (flattenBank b) fs params codes
  have hproj := stage_projection M i (flattenBank b) fs params codes
  have hh := NativeBindingCalls.restoring_call (stageBinding M i) (Label.stage i) (NativeGate.program M)
    (program M) (stage_code M i) (NativeGate.start M) .done s (fun _ => 0)
    (NativeGate.bank M (flattenBank (NativeGate.moved g hg b)) (params i) (codes i) fs) t
    (by rw [show (fun p => s ((stageBinding M i).ports p))=_ from hproj]; exact htr)
  have hh' : Trace M t (cfg M (entry M i.val) s (fun _ => 0))
      (cfg M (.stage i .done) (bank M (flattenBank (NativeGate.moved g hg b)) fs params codes) (fun _ => 0)) := by
    simpa only [s,stage_values,entry,i.isLt,↓reduceDIte] using hh
  have hj : Trace M 1
      (cfg M (.stage i .done) (bank M (flattenBank (NativeGate.moved g hg b)) fs params codes) (fun _ => 0))
      (cfg M (entry M (i.val+1)) (bank M (flattenBank (NativeGate.moved g hg b)) fs params codes) (fun _ => 0)) :=
    NativeMicrocode.jump_trace _ _ _ rfl
  exact ⟨t+1,by omega,trace_trans hh' hj⟩

def perStageBudget (M : Transpose.TM) (C N maxWord : ℕ) :=
  (NativeOracleBatch.suffixConstant M C+300)*2^N+24*maxWord+101

theorem prefix_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C) {N : ℕ} (hN : 0<N)
    (g : Fin 13 → Option Gate) (hg : ∀ i,NativeGate.Legal N (g i)) (b : Address N → Bool)
    (fs : List Bool) (hfs : fs.length=2^(N-1)) (params codes : Fin 13 → List Bool)
    (hp : ∀ i,Counter.value (params i)=NativeSmallDescriptors.parameterValue (g i))
    (hc : ∀ i,codes i=NativeSmallDescriptors.opcodeWord (g i))
    (maxWord : ℕ) (hw : ∀ i,(params i).length≤ maxWord) (n : ℕ) (hn : n≤13) :
    ∃ t≤n*perStageBudget M C N maxWord,Trace M t
      (cfg M (start M) (bank M (flattenBank b) fs params codes) (fun _ => 0))
      (cfg M (entry M n) (bank M (flattenBank (after g hg b n)) fs params codes) (fun _ => 0)) := by
  induction n with
  | zero => exact ⟨0,by simp,.refl _⟩
  | succ n ih =>
    have hn' : n<13 := by omega
    let i : Fin 13 := ⟨n,hn'⟩
    obtain ⟨t0,h0,tr0⟩ := ih (by omega)
    obtain ⟨t1,h1,tr1⟩ := stage_call M C hM hN i (g i) (hg i) (after g hg b n)
      fs hfs params codes (hp i) (hc i)
    have htr := trace_trans tr0 tr1
    refine ⟨t0+t1,?_,?_⟩
    · have hi := hw i
      dsimp [NativeGate.budget] at h1
      dsimp [perStageBudget] at h0 ⊢
      nlinarith
    · simpa only [after,hn',↓reduceDIte] using htr

/-- Every slot is executed by one fixed finite controller. Empty slots are
literal idle opcodes; there is no runtime schedule premise. -/
theorem complete_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C) {N : ℕ} (hN : 0<N)
    (g : Fin 13 → Option Gate) (hg : ∀ i,NativeGate.Legal N (g i)) (b : Address N → Bool)
    (fs : List Bool) (hfs : fs.length=2^(N-1)) (params codes : Fin 13 → List Bool)
    (hp : ∀ i,Counter.value (params i)=NativeSmallDescriptors.parameterValue (g i))
    (hc : ∀ i,codes i=NativeSmallDescriptors.opcodeWord (g i))
    (maxWord : ℕ) (hw : ∀ i,(params i).length≤ maxWord) :
    ∃ t≤13*perStageBudget M C N maxWord,Trace M t
      (cfg M (start M) (bank M (flattenBank b) fs params codes) (fun _ => 0))
      (cfg M .done (bank M (flattenBank (after g hg b 13)) fs params codes) (fun _ => 0)) := by
  simpa only [entry,show ¬13<13 by omega,↓reduceDIte] using
    prefix_trace M C hM hN g hg b fs hfs params codes hp hc maxWord hw 13 (by rfl)
end
end BitWord.NativeStages
