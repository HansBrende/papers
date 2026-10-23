import BitWord.NativePowerTwoCalls

namespace BitWord.NativePowerTwo
open TransposeFollowup FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def bank (xs : List Bool) (fuel power result : Tape Bool) : Bank
  | .source => Counter.marked xs | .fuel => fuel | .power => power | .result => result

@[simp] theorem update_source (xs : List Bool) (f p r : Tape Bool) :
    Function.update (bank xs f p r) .source (Counter.marked xs)=bank xs f p r := by
  funext t; cases t <;> rfl
@[simp] theorem update_fuel (xs : List Bool) (f p r x : Tape Bool) :
    Function.update (bank xs f p r) .fuel x=bank xs x p r := by funext t; cases t <;> rfl
@[simp] theorem update_power (xs : List Bool) (f p r x : Tape Bool) :
    Function.update (bank xs f p r) .power x=bank xs f x r := by funext t; cases t <;> rfl
@[simp] theorem update_result (xs : List Bool) (f p r x : Tape Bool) :
    Function.update (bank xs f p r) .result x=bank xs f p x := by funext t; cases t <;> rfl
@[simp] theorem initial_bank (xs : List Bool) : initial xs=bank xs ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ := by
  funext p; cases p <;> rfl
@[simp] theorem final_bank (xs : List Bool) :
    final xs=bank xs ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked (ruler xs)) := by simp [final]

theorem append_step (xs acc : List Bool) (f r : Tape Bool) (origin : Port → ℤ) :
    NativeMicrocode.step program
      (cfg .append (bank xs f (NativeSealBack.openWord acc) r) (fillPos false origin acc))=
    cfg (.seal false .seal) (bank xs f (NativeSealBack.openWord (acc++[true])) r)
      (fillPos false origin (acc++[true])) := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,cfg]
  congr 1
  · congr 1
    funext p; cases p <;>
      simp [Microcode.single,Microcode.Action.actual,bank,NativeSealBack.openWord,Tape.denote,
        symbols,List.reverse_append,Turing.Tape.mk₂,Turing.Tape.write_mk']
  · funext p; cases p <;>
      simp [Microcode.single,fillPos,outputPort,NativeMicrocode.direction,Transpose.Dir.shift]
    omega

theorem append_call (xs acc : List Bool) (f r : Tape Bool) (origin : Port → ℤ) :
    Trace 1 (cfg .append (bank xs f (NativeSealBack.openWord acc) r) (fillPos false origin acc))
      (cfg (.seal false .seal) (bank xs f (NativeSealBack.openWord (acc++[true])) r)
        (fillPos false origin (acc++[true]))) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · rw [append_step]
    exact .refl _

def budget (xs : List Bool) := 13*2^Counter.value xs+21*Counter.value xs+14*xs.length+72

theorem power_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 10*xs.length+13*Counter.value xs+36, Trace t
      (cfg start (initial xs) pos)
      (cfg (.init true (.erase 0))
        (bank xs (Counter.marked (List.replicate xs.length true))
          (Counter.marked (powerWord (Counter.value xs))) ⟨[],[]⟩) pos) := by
  let e := Counter.value xs
  let ones := List.replicate xs.length true
  let z := List.replicate e false
  let pw := powerWord e
  let out := ruler xs
  let empty : Tape Bool := ⟨[],[]⟩
  obtain ⟨a,ha,ta⟩ := copy_call xs (initial xs) pos
  simp only [initial_bank,update_source,update_fuel] at ta
  have ja := jump_trace (.copy (.seal .done)) (.init false (.erase 0))
    (bank xs (Counter.marked xs) empty empty) pos rfl
  obtain ⟨b,hb,tb⟩ := init_call false (bank xs (Counter.marked xs) empty empty) pos
  simp only [outputPort,Bool.false_eq_true,↓reduceIte,update_power] at tb
  have jb := jump_trace (.init false .done) (.fill false (.counter 0))
    (bank xs (Counter.marked xs) (NativeSealBack.openWord []) empty) pos rfl
  obtain ⟨c,hc,tc⟩ := fill_call false xs [] (initial xs) pos
  simp only [fillBank,fuelPort,outputPort,Bool.false_eq_true,↓reduceIte,initial_bank,
    update_fuel,update_power,fillPos_nil,List.nil_append] at tc
  have jc := jump_trace (.fill false (.counter 12)) .append
    (bank xs (Counter.marked ones) (NativeSealBack.openWord z) empty) (fillPos false pos z) rfl
  have td := append_call xs z (Counter.marked ones) empty pos
  obtain ⟨f,hf,tf⟩ := seal_call false pw (bank xs (Counter.marked ones) empty empty) pos
  simp only [outputPort,Bool.false_eq_true,↓reduceIte,update_power] at tf
  have jf := jump_trace (.seal false .done) (.init true (.erase 0))
    (bank xs (Counter.marked ones) (Counter.marked pw) empty) pos rfl
  refine ⟨_,?_,by
    rw [initial_bank]
    exact trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb (trace_trans tc
      (trace_trans jc (trace_trans td (trace_trans tf jf)))))))⟩
  simp only [pw,powerWord_length,e] at hf
  omega

theorem ruler_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 13*2^Counter.value xs+8*Counter.value xs+4*xs.length+36, Trace t
      (cfg (.init true (.erase 0))
        (bank xs (Counter.marked (List.replicate xs.length true))
          (Counter.marked (powerWord (Counter.value xs))) ⟨[],[]⟩) pos)
      (cfg .done (final xs) pos) := by
  let e := Counter.value xs
  let ones := List.replicate xs.length true
  let pw := powerWord e
  let out := ruler xs
  let empty : Tape Bool := ⟨[],[]⟩
  obtain ⟨g,hg,tg⟩ := init_call true (bank xs (Counter.marked ones) (Counter.marked pw) empty) pos
  simp only [outputPort,↓reduceIte,update_result] at tg
  have jg := jump_trace (.init true .done) (.fill true (.counter 0))
    (bank xs (Counter.marked ones) (Counter.marked pw) (NativeSealBack.openWord [])) pos rfl
  obtain ⟨h,hh,th⟩ := fill_call true pw [] (bank xs (Counter.marked ones) empty empty) pos
  simp only [fillBank,fuelPort,outputPort,↓reduceIte,update_power,
    update_result,fillPos_nil,List.nil_append] at th
  have hw : Counter.value pw=2^e := powerWord_value e
  have hp : pw.length=e+1 := powerWord_length e
  rw [hw,hp] at th
  have jh := jump_trace (.fill true (.counter 12)) (.seal true .seal)
    (bank xs (Counter.marked ones) (Counter.marked (List.replicate (e+1) true))
      (NativeSealBack.openWord out)) (fillPos true pos out) rfl
  obtain ⟨i,hi,ti⟩ := seal_call true out
    (bank xs (Counter.marked ones) (Counter.marked (List.replicate (e+1) true)) empty) pos
  simp only [outputPort,↓reduceIte,update_result] at ti
  have ji := jump_trace (.seal true .done) (.erase false 2)
    (bank xs (Counter.marked ones) (Counter.marked (List.replicate (e+1) true)) (Counter.marked out)) pos rfl
  obtain ⟨j,hj,tj⟩ := erase_call false ones
    (bank xs empty (Counter.marked (List.replicate (e+1) true)) (Counter.marked out)) pos
  simp only [fuelPort,Bool.false_eq_true,↓reduceIte,update_fuel] at tj
  have jj := jump_trace (.erase false 0) (.erase true 2)
    (bank xs empty (Counter.marked (List.replicate (e+1) true)) (Counter.marked out)) pos rfl
  obtain ⟨k,hk,tk⟩ := erase_call true (List.replicate (e+1) true)
    (bank xs empty empty (Counter.marked out)) pos
  simp only [fuelPort,↓reduceIte,update_power] at tk
  have jk := jump_trace (.erase true 0) .done (bank xs empty empty (Counter.marked out)) pos rfl
  refine ⟨_,?_,by
    rw [final_bank]
    exact trace_trans tg (trace_trans jg (trace_trans th (trace_trans jh (trace_trans ti
      (trace_trans ji (trace_trans tj (trace_trans jj (trace_trans tk jk))))))))⟩
  simp only [hw,hp,List.length_replicate] at hh hk
  simp only [ones,List.length_replicate] at hj
  simp only [out,ruler,List.length_replicate] at hi
  dsimp [e] at hh hk
  omega

theorem complete_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ budget xs, Trace t (cfg start (initial xs) pos) (cfg .done (final xs) pos) := by
  obtain ⟨a,ha,ta⟩ := power_trace xs pos
  obtain ⟨b,hb,tb⟩ := ruler_trace xs pos
  exact ⟨a+b,by unfold budget; omega,trace_trans ta tb⟩

/-- An exponent-length bound usable before any canonical-shape specialization. -/
theorem budget_bound (xs : List Bool) :
    budget xs ≤ 100*(2^Counter.value xs+(Counter.value xs+1)*(xs.length+1)) := by
  have hp : 1 ≤ 2^Counter.value xs := Nat.one_le_pow _ _ (by omega)
  unfold budget
  nlinarith

theorem fixed_resources : nativeMachine.k=4 ∧ nativeMachine.g+1=5 ∧
    nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

/-- Literal native execution, preserving the external input and output streams. -/
theorem native_ruler (xs : List Bool) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget xs,
      Transpose.stepN nativeMachine input t
        ((cfg start (initial xs) pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done (final xs) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (final xs) pos).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace xs pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

end BitWord.NativePowerTwo
