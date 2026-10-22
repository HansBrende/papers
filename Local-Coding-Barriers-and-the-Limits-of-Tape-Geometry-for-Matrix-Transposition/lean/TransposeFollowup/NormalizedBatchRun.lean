import TransposeFollowup.NormalizedBatchLoop

namespace TransposeFollowup.NormalizedBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

noncomputable def nativeEncoding (small pad : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 6) (start small pad)
noncomputable def nativeMachine (small pad : ℕ) := NativeMicrocode.machine (nativeEncoding small pad) (program small pad)

def labelEquiv (small pad : ℕ) : Label small pad ≃ PreparedPair.Label small pad ⊕ (Bool × Microcode.MappedAppendFamily.Label) ⊕ (Bool × NativeErase.Label) ⊕ Unit where
  toFun | .read pc => .inl pc | .append b pc => .inr (.inl (b,pc)) | .erase b pc => .inr (.inr (.inl (b,pc))) | .done => .inr (.inr (.inr ()))
  invFun | .inl pc => .read pc | .inr (.inl (b,pc)) => .append b pc | .inr (.inr (.inl (b,pc))) => .erase b pc | .inr (.inr (.inr _)) => .done
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|⟨b,pc⟩|⟨b,pc⟩|⟨⟩) <;> rfl

theorem fixed_resources (small pad : ℕ) : (nativeMachine small pad).k=6 ∧ (nativeMachine small pad).g+1=5 ∧
    (nativeMachine small pad).q+1=small+2*pad+197 ∧ (nativeEncoding small pad).label (start small pad)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label small pad)-1+1=_
  rw [Fintype.card_congr (labelEquiv small pad)]
  have hs := (PreparedPair.fixed_resources small pad).2.2.1
  change Fintype.card (PreparedPair.Label small pad)-1+1=small+2*pad+164 at hs
  have hp : 0<Fintype.card (PreparedPair.Label small pad) := Fintype.card_pos_iff.mpr ⟨.done false⟩
  have ha : Fintype.card Microcode.MappedAppendFamily.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_unit,ha]
  omega

theorem native_batch (small pad : ℕ) (xs : List Bool) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small pad xs rs,
      Transpose.stepN (nativeMachine small pad) input t
        ((cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputBatch rs++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos).denote
          (nativeEncoding small pad) (program small pad) inputPos outRev)=
        some ((cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputBatch rs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
          ⟨(outputBatch pad rs).reverse++out,[]⟩) (advance pos (inputBatch rs).length (outputBatch pad rs).length)).denote
          (nativeEncoding small pad) (program small pad) inputPos outRev) ∧
      Transpose.step (nativeMachine small pad) input
        ((cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputBatch rs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
          ⟨(outputBatch pad rs).reverse++out,[]⟩) (advance pos (inputBatch rs).length (outputBatch pad rs).length)).denote
          (nativeEncoding small pad) (program small pad) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := batch_trace small pad xs hp rs hw pre suffix out pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding small pad) (program small pad) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding small pad) (program small pad) input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (small pad : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 6 ↪ U) (labels : Label small pad → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program small pad pc≠.halt → program small pad pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program small pad pc))
    (xs : List Bool) (hp : 0<2*xs.length+small) (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small pad xs rs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (start small pad) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputBatch rs++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
          outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputBatch rs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
            ⟨(outputBatch pad rs).reverse++out,[]⟩) (advance pos (inputBatch rs).length (outputBatch pad rs).length))
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := batch_trace small pad xs hp rs hw pre suffix out pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program small pad) target outerFrame input inputPos outRev hc htr⟩

def normalizedRecords (pad : ℕ) (rs : List (List Bool × List Bool)) :=
  rs.map (fun p => (NativePaddedField.padded pad p.1,NativePaddedField.padded pad p.2))

theorem output_encoding (pad : ℕ) (rs : List (List Bool × List Bool)) :
    outputBits pad rs=inputBits (normalizedRecords pad rs) := by
  simp only [outputBits,inputBits,normalizedRecords,List.flatMap_map]
  rfl

theorem values_preserved (pad : ℕ) (rs : List (List Bool × List Bool)) :
    (normalizedRecords pad rs).map (fun p => (Counter.value p.1,Counter.value p.2))=
      rs.map (fun p => (Counter.value p.1,Counter.value p.2)) := by
  simp [normalizedRecords,List.map_map,Function.comp_def,NativePaddedField.padded_value]

theorem normalized_width (small large : ℕ) (h : small≤large) (xs : List Bool) (rs : List (List Bool × List Bool))
    (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small) :
    ∀ p ∈ normalizedRecords (large-small) rs,p.1.length=2*xs.length+large ∧ p.2.length=2*xs.length+large := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hq':=hw q hq
  have hh:=PreparedPair.common_words small large h xs q.1 q.2 hq'.1 hq'.2
  exact ⟨hh.1,hh.2.1⟩

end TransposeFollowup.NormalizedBatch
