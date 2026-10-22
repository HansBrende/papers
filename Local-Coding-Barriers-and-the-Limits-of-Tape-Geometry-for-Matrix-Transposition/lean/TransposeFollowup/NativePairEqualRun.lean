import TransposeFollowup.NativePairEqualMachine

namespace TransposeFollowup.NativePairEqual
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def markedBank (a b : List Bool × List Bool) :=
  bank (BinaryCompare.marked a.1) (BinaryCompare.marked a.2) (BinaryCompare.marked b.1) (BinaryCompare.marked b.2)

theorem pair_trace (a b : List Bool × List Bool) (h1 : a.1.length=b.1.length) (h2 : a.2.length=b.2.length) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 5*a.1.length+5*a.2.length+14,Trace t
      (cfg start (markedBank a b) pos) (cfg (.done (samePair a b)) (markedBank a b) pos) := by
  let r1:=BinaryCompare.numeric .equal (BinaryCompare.value a.1) (BinaryCompare.value b.1)
  let r2:=BinaryCompare.numeric .equal (BinaryCompare.value a.2) (BinaryCompare.value b.2)
  obtain ⟨x,hx,tx⟩:=compare_call false a.1 b.1 h1 (markedBank a b) rfl rfl pos
  by_cases hr : r1=.equal
  · have hv : BinaryCompare.value a.1=BinaryCompare.value b.1 := (numeric_equal_iff _ _).mp hr
    have tf:=jump_trace (.compare false (.done r1)) (.compare true (.scan .equal)) (markedBank a b) pos (by simp [program,hr])
    obtain ⟨y,hy,ty⟩:=compare_call true a.2 b.2 h2 (markedBank a b) rfl rfl pos
    have tj:=jump_trace (.compare true (.done r2)) (.done (decide (r2=.equal))) (markedBank a b) pos rfl
    have hm : decide (r2=.equal)=samePair a b := by simp [r2,samePair,Prod.mk.injEq,numeric_equal_iff,hv]
    refine ⟨x+1+y+1,by omega,?_⟩
    simpa only [start,hm] using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx tf) ty) tj
  · have hv : BinaryCompare.value a.1≠BinaryCompare.value b.1 := by intro h;exact hr ((numeric_equal_iff _ _).mpr h)
    have tj:=jump_trace (.compare false (.done r1)) (.done false) (markedBank a b) pos (by simp [program,hr])
    have hm : samePair a b=false := by simp [samePair,Prod.mk.injEq,hv]
    refine ⟨x+1,by omega,?_⟩
    simpa only [start,hm] using NativeCountedLoop.trace_trans tx tj

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 4) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=4 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=58 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_pair (a b : List Bool × List Bool) (h1 : a.1.length=b.1.length) (h2 : a.2.length=b.2.length)
    (pos : Fin 4 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5*a.1.length+5*a.2.length+14,
      Transpose.stepN nativeMachine input t ((cfg start (markedBank a b) pos).denote nativeEncoding program ip outRev)=
        some ((cfg (.done (samePair a b)) (markedBank a b) pos).denote nativeEncoding program ip outRev) ∧
      Transpose.step nativeMachine input ((cfg (.done (samePair a b)) (markedBank a b) pos).denote nativeEncoding program ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=pair_trace a b h1 h2 pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 4 ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (a b : List Bool × List Bool) (h1 : a.1.length=b.1.length) (h2 : a.2.length=b.2.length)
    (pos : Fin 4 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5*a.1.length+5*a.2.length+14,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (markedBank a b) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg (.done (samePair a b)) (markedBank a b) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=pair_trace a b h1 h2 pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.NativePairEqual
