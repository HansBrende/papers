import BitWord.NativeOracleBlockLayout

/-! A paid resettable call on one clocked block. The source and output streams
advance, but every oracle scratch tape is blank again and its head is at origin. -/
namespace BitWord.NativeOracleBlock
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeCountedLoop
set_option autoImplicit false
noncomputable section

def blockBank (M : Transpose.TM) (src dst : Tape Bool) (fs : List Bool) : Bank M :=
  layout M ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ![src,dst,Counter.marked fs]
def blockPos (M : Transpose.TM) (sp tp kp : ℤ) : Port M → ℤ := layout M 0 0 0 ![sp,tp,kp]
def blockBudget (M : Transpose.TM) (n out T : ℕ) : ℕ :=
  NativeOracleReset.budget M T+10*n+10*out+40

theorem complete_trace (M : Transpose.TM) (xs out fs acc : List Bool)
    (sl sr : List (Sym Bool)) (sp tp kp : ℤ) (T : ℕ)
    (hlen : fs.length=xs.length) (h : Transpose.ComputesWithin M xs out T) :
    ∃ t≤blockBudget M xs.length out.length T, Trace M t
      (cfg M (start M) (blockBank M ⟨sl,symbols xs++sr⟩ (NativeSealBack.openWord acc) fs)
        (blockPos M sp tp kp))
      (cfg M .done (blockBank M ⟨(symbols xs).reverse++sl,sr⟩
        (NativeSealBack.openWord (acc++out)) fs)
        (blockPos M (sp+xs.length) (tp+out.length) kp)) := by
  let z : Tape Bool := ⟨[],[]⟩
  let op := NativeSealBack.openWord
  let mk := Counter.marked
  let src : Tape Bool := ⟨sl,symbols xs++sr⟩
  let src' : Tape Bool := ⟨(symbols xs).reverse++sl,sr⟩
  let o0 : Fin 3 → Tape Bool := ![src,op acc,mk fs]
  let o1 : Fin 3 → Tape Bool := ![src',op acc,mk fs]
  let o2 : Fin 3 → Tape Bool := ![src',op (acc++out),mk fs]
  let b0 := layout M z z z o0
  let b1 := layout M z (op []) z o0
  let b2 := layout M z (op []) (op []) o0
  let b3 := layout M z (mk xs) (op []) o1
  let b4 := layout M z (mk xs) (op out) o1
  let b5 := layout M z (mk xs) (mk out) o1
  let b6 := layout M z (mk xs) (mk out) o2
  let b7 := layout M z (mk xs) z o2
  let b8 := layout M z z z o2
  let p0 := layout M (0:ℤ) 0 0 ![sp,tp,kp]
  let p1 := layout M (0:ℤ) 0 0 ![sp+xs.length,tp,kp]
  let p2 := layout M (0:ℤ) 0 out.length ![sp+xs.length,tp,kp]
  let p3 := layout M (0:ℤ) 0 0 ![sp+xs.length,tp+out.length,kp]
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤2,Trace M t (cfg M (start M) b0 p0)
      (cfg M (.initInput .done) b1 p0) := by
    simpa [start,b0,b1] using initialize_input_call M b0 p0 rfl
  have j0 := jump M (.initInput .done) (.initCapture (.erase 0)) b1 p0 rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤2,Trace M t (cfg M (.initCapture (.erase 0)) b1 p0)
      (cfg M (.initCapture .done) b2 p0) := by
    simpa [b1,b2] using initialize_capture_call M b1 p0 rfl
  have j1 := jump M (.initCapture .done) (.load .scan) b2 p0 rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤6*xs.length+5,Trace M t (cfg M (.load .scan) b2 p0)
      (cfg M (.load .done) b3 p1) := by
    simpa [b2,b3,p0,p1,o0,o1,src,src',mk] using
      load_call M b2 p0 xs fs hlen sl sr rfl rfl rfl
  have j2 := jump M (.load .done) (.oracle none) b3 p1 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤NativeOracleReset.budget M T,
      Trace M t (cfg M (.oracle none) b3 p1)
        (cfg M (.oracle (NativeOracleReset.terminal M)) b4 p2) := by
    have hs : ∀ p,b3 (.inl p)=NativeOracleReset.initialBank M xs p :=
      layout_initial_pool M xs o1
    have hp : ∀ p,p1 (.inl p)=0 := layout_zero_pool M _
    simpa [b3,b4,p1,p2,z] using oracle_call M b3 p1 xs out T h hs hp
  have j3 := jump M (.oracle (NativeOracleReset.terminal M)) (.seal .seal) b4 p2
    (by simp [program])
  obtain ⟨t4,h4,tr4⟩ : ∃ t≤2*out.length+5,Trace M t (cfg M (.seal .seal) b4 p2)
      (cfg M (.seal .done) b5 p1) := by
    simpa [b4,b5,p2,p1,mk] using seal_call M b4 p2 out rfl
  have j4 := jump M (.seal .done) (.append 0) b5 p1 rfl
  obtain ⟨t5,h5,tr5⟩ : ∃ t≤4*out.length+5,Trace M t (cfg M (.append 0) b5 p1)
      (cfg M (.append 7) b6 p3) := by
    simpa [b5,b6,p1,p3,o1,o2] using append_call M b5 p1 out acc rfl rfl
  have j5 := jump M (.append 7) (.eraseCapture 2) b6 p3 (by simp [program])
  obtain ⟨t6,h6,tr6⟩ : ∃ t≤4*out.length+4,Trace M t (cfg M (.eraseCapture 2) b6 p3)
      (cfg M (.eraseCapture 0) b7 p3) := by
    simpa [b6,b7,z] using erase_capture_call M b6 p3 out rfl
  have j6 := jump M (.eraseCapture 0) (.eraseInput 2) b7 p3 (by simp [program])
  obtain ⟨t7,h7,tr7⟩ : ∃ t≤4*xs.length+4,Trace M t (cfg M (.eraseInput 2) b7 p3)
      (cfg M (.eraseInput 0) b8 p3) := by
    simpa [b7,b8,z] using erase_input_call M b7 p3 xs rfl
  have j7 := jump M (.eraseInput 0) .done b8 p3 (by simp [program])
  have s0 := trace_trans tr0 j0
  have s1 := trace_trans tr1 j1
  have s2 := trace_trans tr2 j2
  have s3 := trace_trans tr3 j3
  have s4 := trace_trans tr4 j4
  have s5 := trace_trans tr5 j5
  have s6 := trace_trans tr6 j6
  have s7 := trace_trans tr7 j7
  have a1 := trace_trans s0 s1
  have a2 := trace_trans a1 s2
  have a3 := trace_trans a2 s3
  have a4 := trace_trans a3 s4
  have a5 := trace_trans a4 s5
  have a6 := trace_trans a5 s6
  have a7 := trace_trans a6 s7
  refine ⟨_,?_,a7⟩
  dsimp [blockBudget]
  omega

end
end BitWord.NativeOracleBlock
