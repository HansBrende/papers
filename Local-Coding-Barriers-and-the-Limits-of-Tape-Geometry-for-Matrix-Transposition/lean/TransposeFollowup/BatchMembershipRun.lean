import TransposeFollowup.BatchMembershipLoop
import TransposeFollowup.FamilyReaderRun

namespace TransposeFollowup.BatchMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

noncomputable def nativeEncoding (small : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 7) (start small false)
noncomputable def nativeMachine (small : ℕ) := NativeMicrocode.machine (nativeEncoding small) (program small)

def labelEquiv (small : ℕ) : Label small ≃ (Bool × PreparedPair.Label small 0) ⊕ (Bool × NativePairEqual.Label) ⊕ (Bool × Bool × NativeErase.Label) ⊕ Bool where
  toFun | .read f pc => .inl (f,pc) | .compare f pc => .inr (.inl (f,pc)) | .erase f s pc => .inr (.inr (.inl (f,s,pc))) | .done f => .inr (.inr (.inr f))
  invFun | .inl (f,pc) => .read f pc | .inr (.inl (f,pc)) => .compare f pc | .inr (.inr (.inl (f,s,pc))) => .erase f s pc | .inr (.inr (.inr f)) => .done f
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨f,pc⟩|⟨f,pc⟩|⟨f,s,pc⟩|f) <;> rfl

theorem fixed_resources (small : ℕ) : (nativeMachine small).k=7 ∧ (nativeMachine small).g+1=5 ∧
    (nativeMachine small).q+1=2*small+478 ∧ (nativeEncoding small).label (start small false)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label small)-1+1=_
  rw [Fintype.card_congr (labelEquiv small)]
  have hp:=(PreparedPair.fixed_resources small 0).2.2.1
  change Fintype.card (PreparedPair.Label small 0)-1+1=small+2*0+164 at hp
  have hpos : 0<Fintype.card (PreparedPair.Label small 0) := Fintype.card_pos_iff.mpr ⟨.done false⟩
  have hc : Fintype.card NativePairEqual.Label=58 := by decide +kernel
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,hc,he]
  omega

theorem native_batch (small : ℕ) (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small xs rs,
      Transpose.stepN (nativeMachine small) input t
        ((cfg (start small found) (queryBank xs a ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos).denote (nativeEncoding small) (program small) ip outRev)=
        some ((cfg (.done (found || rs.any (NativePairEqual.samePair a)))
          (queryBank xs a ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)).denote
          (nativeEncoding small) (program small) ip outRev) ∧
      Transpose.step (nativeMachine small) input ((cfg (.done (found || rs.any (NativePairEqual.samePair a)))
          (queryBank xs a ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)).denote
          (nativeEncoding small) (program small) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=batch_trace small found xs a ha1 ha2 hp rs hw pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding small) (program small) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding small) (program small) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (small : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 7 ↪ U) (labels : Label small → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program small pc≠.halt → program small pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program small pc))
    (found : Bool) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small xs rs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start small found) (queryBank xs a ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos)
          outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (found || rs.any (NativePairEqual.samePair a)))
            (queryBank xs a ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length))
          outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=batch_trace small found xs a ha1 ha2 hp rs hw pre suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program small) target outerFrame input ip outRev hc htr⟩

theorem any_samePair_iff (a : List Bool × List Bool) (rs : List (List Bool × List Bool)) :
    rs.any (NativePairEqual.samePair a)=true ↔ RowEnumeration.decodePair a ∈ rs.map RowEnumeration.decodePair := by
  simp only [List.any_eq_true,NativePairEqual.samePair,decide_eq_true_eq,List.mem_map]
  constructor
  · rintro ⟨p,hp,he⟩;exact ⟨p,hp,he.symm⟩
  · rintro ⟨p,hp,he⟩;exact ⟨p,hp,he.symm⟩

end TransposeFollowup.BatchMembership
