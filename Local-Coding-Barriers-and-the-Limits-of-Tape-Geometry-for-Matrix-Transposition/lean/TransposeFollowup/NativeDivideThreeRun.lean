import TransposeFollowup.NativeDivideThreeMachine

/-! Native correctness, cost, quotient and remainder of the in-place
constant divider. Markers and absolute head are restored, and other tapes
are preserved through the existing framed-call interface. -/
namespace TransposeFollowup.NativeDivideThree
open FixedTapeCompiler CopyMachine
open NativeTrim (cursor shift shift_zero shift_add)
set_option autoImplicit false

theorem complete_run (xs : List Bool) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (4*xs.length+4) (cfg .scan (Counter.marked xs) pos)=
      cfg (.done (divide xs 0).2) (Counter.marked (divide xs 0).1) pos := by
  have hpre : NativeZipper.run program (2*xs.length+2) (cfg .scan (Counter.marked xs) pos)=
      cfg (.read 0) (cursor xs []).moveLeft (shift (shift pos xs.length) (-1)) := by
    rw [show 2*xs.length+2=(2*xs.length+1)+1 by omega,NativeZipper.run_add,
      ← NativeTrim.cursor_start,forward_run,List.nil_append,turn_step]
  rw [show 4*xs.length+4=(2*xs.length+2)+(2*xs.length+2) by omega,
    NativeZipper.run_add,hpre,backward_run,List.append_nil]
  congr 1
  funext p
  dsimp [shift]
  omega


theorem complete_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 4*xs.length+4,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .scan (Counter.marked xs) pos).denote
        (cfg (.done (divide xs 0).2) (Counter.marked (divide xs 0).1) pos).denote :=
  NativeZipper.trace_of_run program (complete_run xs pos)

theorem native_divide (xs : List Bool) (pos : Fin 1 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ (ys : List Bool) (r : Fin 3),ys.length=xs.length ∧ Counter.value ys=Counter.value xs/3 ∧ r.val=Counter.value xs%3 ∧
      ∃ t ≤ 4*xs.length+4,
        Transpose.stepN nativeMachine input t
          ((cfg .scan (Counter.marked xs) pos).denote.denote nativeEncoding program inputPos outRev)=
          some ((cfg (.done r) (Counter.marked ys) pos).denote.denote nativeEncoding program inputPos outRev) ∧
        Transpose.step nativeMachine input
          ((cfg (.done r) (Counter.marked ys) pos).denote.denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace xs pos
  refine ⟨(divide xs 0).1,(divide xs 0).2,divide_length xs 0,divide_value xs,divide_remainder xs,t,ht,
    NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=19 ∧ nativeEncoding.label .scan=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=19
  decide +kernel

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Fin 1 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+4,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .scan (Counter.marked xs) pos).denote outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (divide xs 0).2) (Counter.marked (divide xs 0).1) pos).denote outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace xs pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeDivideThree
