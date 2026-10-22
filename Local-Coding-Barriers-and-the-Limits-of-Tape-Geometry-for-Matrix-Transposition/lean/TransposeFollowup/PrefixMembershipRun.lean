import TransposeFollowup.PrefixMembershipLoop

namespace TransposeFollowup.PrefixMembership
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

noncomputable def nativeEncoding (small K : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 7) (start small K)
noncomputable def nativeMachine (small K : ℕ) := NativeMicrocode.machine (nativeEncoding small K) (program small K)

def labelEquiv (small K : ℕ) : Label small K ≃ (Fin K × BatchMembership.Label small) ⊕ (Bool × NativeSpanRewind.Label) where
  toFun | .phase i pc => .inl (i,pc) | .rewind f pc => .inr (f,pc)
  invFun | .inl (i,pc) => .phase i pc | .inr (f,pc) => .rewind f pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨i,pc⟩|⟨f,pc⟩) <;> rfl

theorem fixed_resources (small K : ℕ) : (nativeMachine small K).k=7 ∧ (nativeMachine small K).g+1=5 ∧
    (nativeMachine small K).q+1=K*(2*small+478)+8 ∧ (nativeEncoding small K).label (start small K)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label small K)-1+1=_
  rw [Fintype.card_congr (labelEquiv small K)]
  have hp:=(BatchMembership.fixed_resources small).2.2.1
  change Fintype.card (BatchMembership.Label small)-1+1=2*small+478 at hp
  have hpos : 0<Fintype.card (BatchMembership.Label small) := Fintype.card_pos_iff.mpr ⟨.done false⟩
  have hc : Fintype.card (BatchMembership.Label small)=2*small+478 := by omega
  have hr : Fintype.card NativeSpanRewind.Label=4 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,hc,hr]
  omega

theorem native_complete (small : ℕ) (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3*scanBudget small xs batches 0 K+3,
      Transpose.stepN (nativeMachine small K) input t
        ((cfg (start small K) (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos).denote
          (nativeEncoding small K) (program small K) ip outRev)=
        some ((cfg (.rewind ((segments batches 0 K).any (NativePairEqual.samePair a)) .done)
          (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos).denote (nativeEncoding small K) (program small K) ip outRev) ∧
      Transpose.step (nativeMachine small K) input
        ((cfg (.rewind ((segments batches 0 K).any (NativePairEqual.samePair a)) .done)
          (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos).denote (nativeEncoding small K) (program small K) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace small xs a ha1 ha2 hp batches hw suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding small K) (program small K) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding small K) (program small K) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,NativeSpanRewind.program]

theorem native_call {U J : Type*} {k q : ℕ} (small : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 7 ↪ U) (labels : Label small K → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program small K pc≠.halt → program small K pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program small K pc))
    (xs : List Bool) (a : List Bool × List Bool)
    (ha1 : a.1.length=2*xs.length+small) (ha2 : a.2.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (batches : Fin K → List (List Bool × List Bool))
    (hw : ∀ i,∀ p ∈ batches i,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3*scanBudget small xs batches 0 K+3,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start small K) (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos)
          outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.rewind ((segments batches 0 K).any (NativePairEqual.samePair a)) .done)
            (BatchMembership.queryBank xs a ⟨[],stream batches 0 K++suffix⟩) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace small xs a ha1 ha2 hp batches hw suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program small K) target outerFrame input ip outRev hc htr⟩

theorem mapped_segments_mem {α β : Type*} (V : Fin K → List α) (f : α → β) (b : β) :
    b ∈ (segments V 0 K).map f ↔ ∃ i,b ∈ (V i).map f := by
  rw [segments_ofFn V K 0 (by omega)]
  simp only [Nat.zero_add]
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp h
    obtain ⟨xs,hxs,ha⟩:=List.mem_flatten.mp ha
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hxs
    exact ⟨i,List.mem_map.mpr ⟨a,ha,rfl⟩⟩
  · rintro ⟨i,hi⟩
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
    exact List.mem_map.mpr ⟨a,List.mem_flatten.mpr ⟨V i,List.mem_ofFn.mpr ⟨i,rfl⟩,ha⟩,rfl⟩

theorem result_iff (a : List Bool × List Bool) (batches : Fin K → List (List Bool × List Bool)) :
    (segments batches 0 K).any (NativePairEqual.samePair a)=true ↔
      ∃ i,RowEnumeration.decodePair a ∈ (batches i).map RowEnumeration.decodePair := by
  rw [BatchMembership.any_samePair_iff,mapped_segments_mem]

end TransposeFollowup.PrefixMembership
