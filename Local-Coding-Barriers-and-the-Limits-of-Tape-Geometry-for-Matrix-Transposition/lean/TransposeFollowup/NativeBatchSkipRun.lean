import TransposeFollowup.NativeBatchSkipMachine

namespace TransposeFollowup.NativeBatchSkip
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {K : ℕ}

theorem rest_trace (words : Fin K → List Bool) (q k : ℕ) (hk : k+q=K)
    (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*(stream words k q).length,
      OperationalTrace.Trace (NativeMicrocode.step (program K)) (NativeMicrocode.Active (program K)) t
        (cfg (entry K k) ⟨left,stream words k q++suffix⟩ pos).denote
        (cfg .done ⟨(stream words k q).reverse++left,suffix⟩ (fun p => pos p+(stream words k q).length)).denote := by
  induction q generalizing k left pos with
  | zero =>
    have he : k=K := by omega
    subst k
    refine ⟨0,by simp,?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,stream,PrefixMembership.segments,List.nil_append,List.reverse_nil,
      List.length_nil,Nat.cast_zero,add_zero]
    exact .refl _
  | succ q ih =>
    have hkK : k<K := by omega
    let i : Fin K:=⟨k,hkK⟩
    obtain ⟨x,hx,tx⟩:=batch_trace i (words i) left (stream words (k+1) q++suffix) pos
    obtain ⟨y,hy,ty⟩:=ih (k+1) (by omega) ((block (words i)).reverse++left) (fun p => pos p+(block (words i)).length)
    refine ⟨x+y,?_,?_⟩
    · simp only [stream,PrefixMembership.segments,hkK,↓reduceDIte,List.length_append,Nat.mul_add]
      dsimp only [i] at hx
      dsimp only [stream] at hy
      omega
    · simpa only [stream,PrefixMembership.segments,hkK,↓reduceDIte,List.append_assoc,List.reverse_append,
        List.length_append,Nat.cast_add,add_assoc] using NativeCountedLoop.trace_trans tx ty

theorem complete_trace (words : Fin K → List Bool) (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*(stream words 0 K).length,
      OperationalTrace.Trace (NativeMicrocode.step (program K)) (NativeMicrocode.Active (program K)) t
        (cfg (entry K 0) ⟨left,stream words 0 K++suffix⟩ pos).denote
        (cfg .done ⟨(stream words 0 K).reverse++left,suffix⟩ (fun p => pos p+(stream words 0 K).length)).denote :=
  rest_trace words K 0 (by omega) left suffix pos

noncomputable def nativeEncoding (K : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 1) (entry K 0)
noncomputable def nativeMachine (K : ℕ) := NativeMicrocode.machine (nativeEncoding K) (program K)
def labelEquiv (K : ℕ) : Label K ≃ Fin K ⊕ Fin K ⊕ Fin K ⊕ Unit ⊕ Unit where
  toFun
    | .read i => .inl i
    | .dataStep i => .inr (.inl i)
    | .stopStep i => .inr (.inr (.inl i))
    | .done => .inr (.inr (.inr (.inl ())))
    | .reject => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl i => .read i
    | .inr (.inl i) => .dataStep i
    | .inr (.inr (.inl i)) => .stopStep i
    | .inr (.inr (.inr (.inl _))) => .done
    | .inr (.inr (.inr (.inr _))) => .reject
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (i|i|i|⟨⟩|⟨⟩) <;> rfl

theorem label_card (K : ℕ) : Fintype.card (Label K)=3*K+2 := by
  rw [Fintype.card_congr (labelEquiv K)]
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  omega
theorem fixed_resources (K : ℕ) : (nativeMachine K).k=1 ∧ (nativeMachine K).g+1=5 ∧
    (nativeMachine K).q+1=3*K+2 ∧ (nativeEncoding K).label (entry K 0)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label K)-1+1=_
  rw [label_card];omega

theorem native_complete (words : Fin K → List Bool) (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*(stream words 0 K).length,
      Transpose.stepN (nativeMachine K) input t
        ((cfg (entry K 0) ⟨left,stream words 0 K++suffix⟩ pos).denote.denote (nativeEncoding K) (program K) ip outRev)=
        some ((cfg .done ⟨(stream words 0 K).reverse++left,suffix⟩ (fun p => pos p+(stream words 0 K).length)).denote.denote
          (nativeEncoding K) (program K) ip outRev) ∧
      Transpose.step (nativeMachine K) input
        ((cfg .done ⟨(stream words 0 K).reverse++left,suffix⟩ (fun p => pos p+(stream words 0 K).length)).denote.denote
          (nativeEncoding K) (program K) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace words left suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding K) (program K) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding K) (program K) input ip outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label K → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program K pc≠.halt → program K pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program K pc))
    (words : Fin K → List Bool) (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*(stream words 0 K).length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (entry K 0) ⟨left,stream words 0 K++suffix⟩ pos).denote outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done ⟨(stream words 0 K).reverse++left,suffix⟩ (fun p => pos p+(stream words 0 K).length)).denote outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace words left suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program K) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.NativeBatchSkip
