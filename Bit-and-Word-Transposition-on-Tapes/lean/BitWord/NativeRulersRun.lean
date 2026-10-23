import BitWord.NativeRulersCalls

namespace BitWord.NativeRulers
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop

def budget (xs hs ws : List Bool) :=
  (13*Counter.value xs+14*xs.length+40) +
  (13*Counter.value hs+14*hs.length+40) +
  NativePowerTwo.budget hs + (6*2^Counter.value hs+14) +
  NativePowerTwo.budget ws + (6*2^Counter.value ws+14) +
  (6*Counter.value xs*2^Counter.value ws+9*Counter.value xs+16) +
  (6*2^Counter.value hs*2^Counter.value ws+9*2^Counter.value hs+16)+8

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) := NativeMicrocode.jump_trace _ _ _ h

/-- All six false-bit rulers are constructed by one fixed controller. The three
parameter words are retained, and the two reusable work tapes finish blank. -/
theorem complete_trace (xs hs ws : List Bool) (pos : Port → ℤ) :
    ∃ t≤budget xs hs ws,Trace t (cfg start (initial xs hs ws) pos) (cfg .done (final xs hs ws) pos) := by
  obtain ⟨t0,h0,tr0⟩ := unary_call false xs hs ws pos
  have j0 := jump (.unary false .done) (.unary true NativeUnary.start) (stage xs hs ws 1) pos rfl
  obtain ⟨t1,h1,tr1⟩ := unary_call true xs hs ws pos
  have j1 := jump (.unary true .done) (.power false NativePowerTwo.start) (stage xs hs ws 2) pos rfl
  obtain ⟨t2,h2,tr2⟩ := power_call false xs hs ws pos
  have j2 := jump (.power false .done) (.map false (.init (.erase 0))) (stage xs hs ws 3) pos rfl
  obtain ⟨t3,h3,tr3⟩ := map_call false xs hs ws pos
  have j3 := jump (.map false (.seal .done)) (.power true NativePowerTwo.start) (stage xs hs ws 4) pos rfl
  obtain ⟨t4,h4,tr4⟩ := power_call true xs hs ws pos
  have j4 := jump (.power true .done) (.map true (.init (.erase 0))) (stage xs hs ws 5) pos rfl
  obtain ⟨t5,h5,tr5⟩ := map_call true xs hs ws pos
  have j5 := jump (.map true (.seal .done)) (.product false NativeExpanderShearTagPage.start) (stage xs hs ws 6) pos rfl
  obtain ⟨t6,h6,tr6⟩ := product_call false xs hs ws pos
  have j6 := jump (.product false .done) (.product true NativeExpanderShearTagPage.start) (stage xs hs ws 7) pos rfl
  obtain ⟨t7,h7,tr7⟩ := product_call true xs hs ws pos
  have j7 := jump (.product true .done) .done (stage xs hs ws 8) pos rfl
  have s0 := trace_trans tr0 j0
  have s1 := trace_trans tr1 j1
  have s2 := trace_trans tr2 j2
  have s3 := trace_trans tr3 j3
  have s4 := trace_trans tr4 j4
  have s5 := trace_trans tr5 j5
  have s6 := trace_trans tr6 j6
  have s7 := trace_trans tr7 j7
  have acc1 := trace_trans s0 s1
  have acc2 := trace_trans acc1 s2
  have acc3 := trace_trans acc2 s3
  have acc4 := trace_trans acc3 s4
  have acc5 := trace_trans acc4 s5
  have acc6 := trace_trans acc5 s6
  have acc7 := trace_trans acc6 s7
  refine ⟨_,?_,acc7⟩
  simp only [unaryWord,powerWord,productCount,Bool.false_eq_true,↓reduceIte] at h0 h1 h2 h3 h4 h5 h6 h7
  unfold budget
  omega

theorem final_contents (xs hs ws : List Bool) : final xs hs ws=contents xs hs ws := by
  funext p; cases p <;> rfl

/-- A coarse bound isolates the input-size absorption used by the final caller. -/
theorem budget_le (xs hs ws : List Bool) : budget xs hs ws ≤
    400*(Counter.value xs*2^Counter.value ws + 2^Counter.value hs*2^Counter.value ws +
      2^Counter.value hs+2^Counter.value ws+Counter.value xs+Counter.value hs+Counter.value ws+
      xs.length+hs.length+ws.length+1) := by
  unfold budget NativePowerTwo.budget
  simp only [Nat.mul_assoc]
  omega

end BitWord.NativeRulers
