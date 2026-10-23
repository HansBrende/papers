import BitWord.NativeSuffixPowered
import BitWord.NativeTapeCalls

namespace BitWord.NativeSuffixPowered
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section

theorem jump (M : Transpose.TM) (pc next : Label M) (s : Bank M) (pos : Port M → ℤ)
    (h : program M pc=.jump next) : Trace M 1 (cfg M pc s pos) (cfg M next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem double_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (xs : List Bool)
    (hp : s (parameter M)=Counter.marked xs) (he : s (exponent M)=⟨[],[]⟩) :
    ∃ t≤6*xs.length+20,Trace M t (cfg M (.double NativeDoubleWord.start) s pos)
      (cfg M (.double .done) (Function.update s (exponent M) (Counter.marked (false::xs))) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeDoubleWord.complete_trace xs ![pos (parameter M),pos (exponent M)]
  have hh := call_pair (parameter M) (exponent M) (by simp [parameter,exponent]) Label.double
    NativeDoubleWord.program (program M) (double_code M) NativeDoubleWord.start .done s pos
    (s (parameter M)) (Counter.marked (false::xs)) (pos (parameter M)) (pos (exponent M)) t
  have hh' := hh (by simpa only [hp,he] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

theorem power_call (M : Transpose.TM) (main : Tape Bool) (xs exp : List Bool) (sp tp kp pp : ℤ) :
    ∃ t≤NativePowerTwo.budget exp,Trace M t
      (cfg M (.power NativePowerTwo.start) (bank M main ⟨[],[]⟩ (Counter.marked xs) (Counter.marked exp))
        (positions M sp tp kp pp))
      (cfg M (.power .done) (bank M main (Counter.marked (NativePowerTwo.ruler exp))
        (Counter.marked xs) (Counter.marked exp)) (positions M sp tp kp pp)) := by
  let s := bank M main ⟨[],[]⟩ (Counter.marked xs) (Counter.marked exp)
  let pos := positions M sp tp kp pp
  have hproj : (fun p => s ((powerBinding M).ports p))=NativePowerTwo.initial exp := by
    funext p; cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := NativePowerTwo.complete_trace exp (fun p => pos ((powerBinding M).ports p))
  have hh := NativeBindingCalls.restoring_call (powerBinding M) Label.power NativePowerTwo.program
    (program M) (power_code M) NativePowerTwo.start .done s pos (NativePowerTwo.final exp) t
    (by
      rw [hproj]
      simpa only [NativePowerTwo.cfg,workCfg] using htr)
  have hout : (powerBinding M).values (NativePowerTwo.final exp) s=
      bank M main (Counter.marked (NativePowerTwo.ruler exp)) (Counter.marked xs) (Counter.marked exp) := by
    rw [power_values]
    simp [NativePowerTwo.final,NativePowerTwo.bank,s,bank,exponent,fuel,power,ruler]
  exact ⟨t,ht,by simpa only [hout] using hh⟩

theorem suffix_call (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    {N k : ℕ} (hk : 2*k≤N) (b : Address N → Bool) (xs exp : List Bool) (sp tp kp pp : ℤ) :
    ∃ t≤(NativeOracleBatch.suffixConstant M C+44)*(2^N),Trace M t
      (cfg M (.suffix (NativeOracleInPlace.start M))
        (bank M (Counter.marked (flattenBank b)) (Counter.marked (List.replicate (4^k) true))
          (Counter.marked xs) (Counter.marked exp)) (positions M sp tp kp pp))
      (cfg M (.suffix .done)
        (bank M (Counter.marked (flattenBank (moveBank (Gate.equiv N (.suffix k) hk) b)))
          (Counter.marked (List.replicate (4^k) true)) (Counter.marked xs) (Counter.marked exp))
        (positions M sp tp kp pp)) := by
  obtain ⟨t,ht,htr⟩ := NativeOracleInPlace.suffix_trace M C hM hk b sp tp kp
  let base := bank M (Counter.marked (flattenBank b)) (Counter.marked (List.replicate (4^k) true))
    (Counter.marked xs) (Counter.marked exp)
  have hh := MicrocodeEmbedding.trace_embed (dataBinding M).ports Label.suffix
    (NativeOracleInPlace.program M) (program M) (frame base (positions M sp tp kp pp)) (suffix_code M) htr
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht,by simpa only [base,bank,positions,data_values,innerBank,NativeOracleInPlace.blockBank,NativeOracleInPlace.blockPos,NativeOracleBlock.blockBank] using hh⟩

def budget (M : Transpose.TM) (C N k : ℕ) (xs : List Bool) : ℕ :=
  NativePowerTwo.budget (false::xs)+(NativeOracleBatch.suffixConstant M C+44)*(2^N)+
    4*(4^k)+10*xs.length+50

theorem ruler_double (xs : List Bool) (k : ℕ) (hx : Counter.value xs=k) :
    NativePowerTwo.ruler (false::xs)=List.replicate (4^k) true := by
  unfold NativePowerTwo.ruler
  rw [NativeDoubleWord.value_double,hx]
  congr 1
  rw [show 4=2^2 by norm_num,pow_mul]

/-- A legal suffix operation with all ruler creation and erasure paid. Only
its binary parameter and raw data bank are present initially. -/
theorem complete_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    {N k : ℕ} (hk : 2*k≤N) (b : Address N → Bool) (xs : List Bool)
    (hx : Counter.value xs=k) (sp tp kp pp : ℤ) :
    ∃ t≤budget M C N k xs,Trace M t
      (cfg M (start M) (bank M (Counter.marked (flattenBank b)) ⟨[],[]⟩ (Counter.marked xs) ⟨[],[]⟩)
        (positions M sp tp kp pp))
      (cfg M .done (bank M (Counter.marked (flattenBank (moveBank (Gate.equiv N (.suffix k) hk) b)))
        ⟨[],[]⟩ (Counter.marked xs) ⟨[],[]⟩) (positions M sp tp kp pp)) := by
  let raw := Counter.marked (flattenBank b)
  let out := Counter.marked (flattenBank (moveBank (Gate.equiv N (.suffix k) hk) b))
  let par := Counter.marked xs
  let exp := Counter.marked (false::xs)
  let clk := Counter.marked (List.replicate (4^k) true)
  let z : Tape Bool := ⟨[],[]⟩
  let b0 := bank M raw z par z
  let b1 := bank M raw z par exp
  let b2 := bank M raw clk par exp
  let b3 := bank M out clk par exp
  let b4 := bank M out z par exp
  let b5 := bank M out z par z
  let pos := positions M sp tp kp pp
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤6*xs.length+20,Trace M t (cfg M (start M) b0 pos)
      (cfg M (.double .done) b1 pos) := by
    simpa [start,b0,b1,bank,exponent] using double_call M b0 pos xs rfl rfl
  have j0 := jump M (.double .done) (.power NativePowerTwo.start) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤NativePowerTwo.budget (false::xs),Trace M t
      (cfg M (.power NativePowerTwo.start) b1 pos) (cfg M (.power .done) b2 pos) := by
    simpa only [ruler_double xs k hx] using power_call M raw xs (false::xs) sp tp kp pp
  have j1 := jump M (.power .done) (.suffix (NativeOracleInPlace.start M)) b2 pos rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤(NativeOracleBatch.suffixConstant M C+44)*(2^N),Trace M t
      (cfg M (.suffix (NativeOracleInPlace.start M)) b2 pos) (cfg M (.suffix .done) b3 pos) :=
    suffix_call M C hM hk b xs (false::xs) sp tp kp pp
  have j2 := jump M (.suffix .done) (.eraseRuler 2) b3 pos rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤4*(List.replicate (4^k) true).length+4,Trace M t
      (cfg M (.eraseRuler 2) b3 pos) (cfg M (.eraseRuler 0) b4 pos) := by
    simpa [b3,b4,bank,ruler] using NativeTapeCalls.erase (program M) (ruler M)
      Label.eraseRuler (eraseRuler_code M) b3 pos (List.replicate (4^k) true) rfl
  have j3 := jump M (.eraseRuler 0) (.eraseExponent 2) b4 pos (by simp [program])
  obtain ⟨t4,h4,tr4⟩ : ∃ t≤4*(false::xs).length+4,Trace M t
      (cfg M (.eraseExponent 2) b4 pos) (cfg M (.eraseExponent 0) b5 pos) := by
    simpa [b4,b5,bank,exponent] using NativeTapeCalls.erase (program M) (exponent M)
      Label.eraseExponent (eraseExponent_code M) b4 pos (false::xs) rfl
  have j4 := jump M (.eraseExponent 0) .done b5 pos (by simp [program])
  have a0 := trace_trans tr0 j0
  have a1 := trace_trans a0 tr1
  have a2 := trace_trans a1 j1
  have a3 := trace_trans a2 tr2
  have a4 := trace_trans a3 j2
  have a5 := trace_trans a4 tr3
  have a6 := trace_trans a5 j3
  have a7 := trace_trans a6 tr4
  have a8 := trace_trans a7 j4
  refine ⟨_,?_,a8⟩
  dsimp [budget]
  simp only [List.length_replicate] at h3
  simp only [List.length_cons] at h4
  omega

end
end BitWord.NativeSuffixPowered
