import BitWord.NativeSplit

namespace BitWord.NativeSplit
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop

@[simp] theorem update_three_zero {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (0:Fin 3) x = ![x,b,c] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_three_one {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (1:Fin 3) x = ![a,x,c] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_three_two {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (2:Fin 3) x = ![a,b,x] := by funext i; fin_cases i <;> rfl
@[simp] theorem three_eta {A : Type*} (f : Fin 3 → A) : ![f 0,f 1,f 2] = f := by
  funext i; fin_cases i <;> rfl
@[simp] theorem all_values {A : Type*} (f g : Fin 3 → A) : allBinding.values f g = f := rfl

def evenBits (xs : List Bool) := NativeSplitScan.selected false false xs
def oddBits (xs : List Bool) := NativeSplitScan.selected true false xs
def output (xs : List Bool) := evenBits xs ++ oddBits xs

theorem selected_lengths (p : Bool) (xs : List Bool) :
    (NativeSplitScan.selected false p xs).length +
    (NativeSplitScan.selected true p xs).length = xs.length := by
  induction xs generalizing p with
  | nil => simp [NativeSplitScan.selected]
  | cons b xs ih =>
    have ht := ih true
    have hf := ih false
    cases p <;> simp only [NativeSplitScan.selected,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,List.length_cons] <;> omega

@[simp] theorem output_length (xs : List Bool) : (output xs).length=xs.length := by
  simpa [output,evenBits,oddBits] using selected_lengths false xs

@[simp] theorem split_positions (pos : Fin 3 → ℤ) (n a b : ℕ) :
    NativeSplitScan.positions pos n a b = ![pos 0+n,pos 1+a,pos 2+b] := by
  funext i; fin_cases i <;> simp [NativeSplitScan.positions]

theorem scan_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 2*xs.length+1, Trace t
      (cfg (.scan (.scan false)) ![Counter.marked xs,NativeSealBack.openWord [],NativeSealBack.openWord []] pos)
      (cfg (.scan .done) ![⟨(symbols xs).reverse++[.start],[.stop]⟩,
        NativeSealBack.openWord (evenBits xs),NativeSealBack.openWord (oddBits xs)]
        ![pos 0+xs.length,pos 1+(evenBits xs).length,pos 2+(oddBits xs).length]) := by
  obtain ⟨t,ht,htr⟩ := NativeSplitScan.split_trace xs false [.start] [] [] [] pos
  have hh := MicrocodeEmbedding.trace_embed allBinding.ports Label.scan NativeSplitScan.program program
    (frame (fun _ => ⟨[],[]⟩) pos) scan_code htr
  change Trace t
    (MicrocodeEmbedding.embed allBinding.ports Label.scan
      (workCfg (.scan false) ![Counter.marked xs,NativeSealBack.openWord [],NativeSealBack.openWord []] pos) _)
    (MicrocodeEmbedding.embed allBinding.ports Label.scan
      (workCfg .done ![⟨(symbols xs).reverse++[.start],[.stop]⟩,
        NativeSealBack.openWord ([]++evenBits xs),NativeSealBack.openWord ([]++oddBits xs)]
        (NativeSplitScan.positions pos xs.length (evenBits xs).length (oddBits xs).length)) _) at hh
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht,by simpa only [all_values,List.nil_append,split_positions] using hh⟩

/-- One fixed controller realizes stable split, returns every head, and clears
both scratch tapes. Raw input and final output handling belong to the caller. -/
theorem complete_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 20*xs.length+60, Trace t
      (cfg start ![Counter.marked xs,⟨[],[]⟩,⟨[],[]⟩] pos)
      (cfg .done ![Counter.marked (output xs),⟨[],[]⟩,⟨[],[]⟩] pos) := by
  let E := evenBits xs
  let O := oddBits xs
  have hlen : E.length+O.length=xs.length := selected_lengths false xs
  let z : Tape Bool := ⟨[],[]⟩
  let op := NativeSealBack.openWord
  let mk := Counter.marked
  let b0 : Bank := ![mk xs,z,z]
  let b1 : Bank := ![mk xs,op [],z]
  let b2 : Bank := ![mk xs,op [],op []]
  let b3 : Bank := ![⟨(symbols xs).reverse++[.start],[.stop]⟩,op E,op O]
  let b4 : Bank := ![mk xs,op E,op O]
  let b5 : Bank := ![mk xs,mk E,op O]
  let b6 : Bank := ![mk xs,mk E,mk O]
  let b7 : Bank := ![op [],mk E,mk O]
  let b8 : Bank := ![op E,mk E,mk O]
  let b9 : Bank := ![op (E++O),mk E,mk O]
  let b10 : Bank := ![mk (E++O),mk E,mk O]
  let b11 : Bank := ![mk (E++O),z,mk O]
  let b12 : Bank := ![mk (E++O),z,z]
  let p3 : Port → ℤ := ![pos 0+xs.length,pos 1+E.length,pos 2+O.length]
  let p4 : Port → ℤ := ![pos 0,pos 1+E.length,pos 2+O.length]
  let p5 : Port → ℤ := ![pos 0,pos 1,pos 2+O.length]
  let p8 : Port → ℤ := ![pos 0+E.length,pos 1,pos 2]
  let p9 : Port → ℤ := ![pos 0+(E.length+O.length),pos 1,pos 2]
  obtain ⟨t0,h0,tr0⟩ : ∃ t ≤ 2,Trace t (cfg start b0 pos) (cfg (.init false .done) b1 pos) := by
    simpa [start,b0,b1,scratch,op,z] using initialize_call false b0 pos rfl
  have j0 := jump (.init false .done) (.init true (.erase 0)) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t ≤ 2,Trace t (cfg (.init true (.erase 0)) b1 pos) (cfg (.init true .done) b2 pos) := by
    simpa [b1,b2,scratch,op,z] using initialize_call true b1 pos rfl
  have j1 := jump (.init true .done) (.scan (.scan false)) b2 pos rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t ≤ 2*xs.length+1,Trace t (cfg (.scan (.scan false)) b2 pos) (cfg (.scan .done) b3 p3) :=
    scan_call xs pos
  have j2 := jump (.scan .done) (.seal 0 .back) b3 p3 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t ≤ 2*xs.length+4,Trace t (cfg (.seal 0 .back) b3 p3) (cfg (.seal 0 .done) b4 p4) := by
    simpa [b3,b4,p3,p4,mk] using rewind_source_call b3 p3 xs rfl
  have j3 := jump (.seal 0 .done) (.seal 1 .seal) b4 p4 rfl
  obtain ⟨t4,h4,tr4⟩ : ∃ t ≤ 2*E.length+5,Trace t (cfg (.seal 1 .seal) b4 p4) (cfg (.seal 1 .done) b5 p5) := by
    simpa [b4,b5,p4,p5,mk] using seal_call 1 b4 p4 E rfl
  have j4 := jump (.seal 1 .done) (.seal 2 .seal) b5 p5 rfl
  obtain ⟨t5,h5,tr5⟩ : ∃ t ≤ 2*O.length+5,Trace t (cfg (.seal 2 .seal) b5 p5) (cfg (.seal 2 .done) b6 pos) := by
    simpa [b5,b6,p5,mk] using seal_call 2 b5 p5 O rfl
  have j5 := jump (.seal 2 .done) (.recycle (.erase 2)) b6 pos rfl
  obtain ⟨t6,h6,tr6⟩ : ∃ t ≤ 4*xs.length+6,Trace t (cfg (.recycle (.erase 2)) b6 pos) (cfg (.recycle .done) b7 pos) := by
    simpa [b6,b7,op] using recycle_call b6 pos xs rfl
  have j6 := jump (.recycle .done) (.append false 0) b7 pos rfl
  obtain ⟨t7,h7,tr7⟩ : ∃ t ≤ 4*E.length+5,Trace t (cfg (.append false 0) b7 pos) (cfg (.append false 7) b8 p8) := by
    have hp : Function.update pos 0 (pos 0+E.length)=p8 := by
      funext i; fin_cases i <;> simp [p8]
    simpa [b7,b8,scratch,op,hp] using append_call false b7 pos E [] rfl rfl
  have j7 := jump (.append false 7) (.append true 0) b8 p8 rfl
  obtain ⟨t8,h8,tr8⟩ : ∃ t ≤ 4*O.length+5,Trace t (cfg (.append true 0) b8 p8) (cfg (.append true 7) b9 p9) := by
    simpa [b8,b9,p8,p9,scratch,op,Nat.cast_add,add_assoc] using append_call true b8 p8 O E rfl rfl
  have j8 := jump (.append true 7) (.finish .seal) b9 p9 rfl
  obtain ⟨t9,h9,tr9⟩ : ∃ t ≤ 2*(E++O).length+5,Trace t (cfg (.finish .seal) b9 p9) (cfg (.finish .done) b10 pos) := by
    simpa [b9,b10,p9,mk] using finish_call b9 p9 (E++O) rfl
  have j9 := jump (.finish .done) (.erase false 2) b10 pos rfl
  obtain ⟨t10,h10,tr10⟩ : ∃ t ≤ 4*E.length+4,Trace t (cfg (.erase false 2) b10 pos) (cfg (.erase false 0) b11 pos) := by
    simpa [b10,b11,scratch,z] using erase_call false b10 pos E rfl
  have j10 := jump (.erase false 0) (.erase true 2) b11 pos rfl
  obtain ⟨t11,h11,tr11⟩ : ∃ t ≤ 4*O.length+4,Trace t (cfg (.erase true 2) b11 pos) (cfg (.erase true 0) b12 pos) := by
    simpa [b11,b12,scratch,z] using erase_call true b11 pos O rfl
  have j11 := jump (.erase true 0) .done b12 pos rfl
  have seg0 := trace_trans tr0 j0
  have seg1 := trace_trans tr1 j1
  have seg2 := trace_trans tr2 j2
  have seg3 := trace_trans tr3 j3
  have seg4 := trace_trans tr4 j4
  have seg5 := trace_trans tr5 j5
  have seg6 := trace_trans tr6 j6
  have seg7 := trace_trans tr7 j7
  have seg8 := trace_trans tr8 j8
  have seg9 := trace_trans tr9 j9
  have seg10 := trace_trans tr10 j10
  have seg11 := trace_trans tr11 j11
  have acc0 := seg0
  have acc1 := trace_trans acc0 seg1
  have acc2 := trace_trans acc1 seg2
  have acc3 := trace_trans acc2 seg3
  have acc4 := trace_trans acc3 seg4
  have acc5 := trace_trans acc4 seg5
  have acc6 := trace_trans acc5 seg6
  have acc7 := trace_trans acc6 seg7
  have acc8 := trace_trans acc7 seg8
  have acc9 := trace_trans acc8 seg9
  have acc10 := trace_trans acc9 seg10
  have acc11 := trace_trans acc10 seg11
  have tr := acc11
  refine ⟨_,?_,tr⟩
  simp only [List.length_append] at h9
  omega

/-- The checked split trace can be called from any literal embedding, with an
arbitrary untouched frame and arbitrary raw input/output context. -/
theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 20*xs.length+60,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg start ![Counter.marked xs,⟨[],[]⟩,⟨[],[]⟩] pos) frame).denote
            encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done ![Counter.marked (output xs),⟨[],[]⟩,⟨[],[]⟩] pos) frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace xs pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    frame input inputPos outRev hc htr⟩

end BitWord.NativeSplit
