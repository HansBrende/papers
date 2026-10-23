import BitWord.NativeOracleBatchLoop

namespace BitWord.NativeOracleBatch
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section

 theorem initialize_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ)
    (hs : s (target M)=⟨[],[]⟩) :
    ∃ t≤2, Trace M t (cfg M (start M) s pos)
      (cfg M (.init .done) (Function.update s (target M) (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos (target M))
  have hh := call_single (target M) Label.init NativeBuffer.program (program M) (init_code M)
    (.erase 0) .done s pos (NativeSealBack.openWord []) (pos (target M)) t
  have hh' := hh (by simpa [workCfg,NativeBuffer.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self,start] using hh'⟩

 theorem seal_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (out : List Bool)
    (hs : s (target M)=NativeSealBack.openWord out) :
    ∃ t≤2*out.length+5,Trace M t (cfg M (.seal .seal) s pos)
      (cfg M (.seal .done) (Function.update s (target M) (Counter.marked out))
        (Function.update pos (target M) (pos (target M)-out.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace out (fun _ => pos (target M))
  refine ⟨t,ht,call_single (target M) Label.seal NativeSealBack.program (program M) (seal_code M)
    .seal .done s pos (Counter.marked out) (pos (target M)-out.length) t ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

 theorem rewind_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (xs : List Bool)
    (hs : s (source M)=RowStream.closedTape xs) :
    ∃ t≤2*xs.length+4,Trace M t (cfg M (.rewind .back) s pos)
      (cfg M (.rewind .done) (Function.update s (source M) (Counter.marked xs))
        (Function.update pos (source M) (pos (source M)-xs.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace xs (fun _ => pos (source M))
  refine ⟨t,ht,call_single (source M) Label.rewind NativeSealBack.program (program M) (rewind_code M)
    .back .done s pos (Counter.marked xs) (pos (source M)-xs.length) t ?_⟩
  simpa [workCfg,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,hs] using htr

def batchBudget (M : Transpose.TM) (n b T : ℕ) : ℕ :=
  n*(NativeOracleReset.budget M T+24*b+42)+20

/-- End-marker batching starts and finishes with blank oracle work tapes.
Only the separately supplied unary block ruler is prepared by its caller. -/
theorem complete_trace (M : Transpose.TM) (f : List Bool → List Bool) (fs : List Bool)
    (hfs : 0<fs.length) (T : ℕ) (blocks : List (List Bool))
    (hb : ∀ xs∈blocks,xs.length=fs.length ∧ (f xs).length=fs.length ∧
      Transpose.ComputesWithin M xs (f xs) T) (sp tp kp : ℤ) :
    ∃ t≤batchBudget M blocks.length fs.length T,Trace M t
      (cfg M (start M) (blockBank M (Counter.marked blocks.flatten) ⟨[],[]⟩ fs)
        (blockPos M sp tp kp))
      (cfg M .done (blockBank M (Counter.marked blocks.flatten)
        (Counter.marked (blocks.map f).flatten) fs) (blockPos M sp tp kp)) := by
  let xs := blocks.flatten
  let ys := (blocks.map f).flatten
  have hx : xs.length=blocks.length*fs.length := flattened_length fs blocks (by
    intro x hx; exact (hb x hx).1)
  have hy : ys.length=blocks.length*fs.length := by
    have hl := flattened_length fs (blocks.map f) (by
      intro y hy; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy; exact (hb x hx).2.1)
    simpa [ys] using hl
  let b0 := blockBank M (Counter.marked xs) ⟨[],[]⟩ fs
  let b1 := blockBank M (Counter.marked xs) (NativeSealBack.openWord []) fs
  let b2 := blockBank M (RowStream.closedTape xs) (NativeSealBack.openWord ys) fs
  let b3 := blockBank M (RowStream.closedTape xs) (Counter.marked ys) fs
  let b4 := blockBank M (Counter.marked xs) (Counter.marked ys) fs
  let p0 := blockPos M sp tp kp
  let p1 := blockPos M (sp+xs.length) (tp+ys.length) kp
  let p2 := blockPos M (sp+xs.length) tp kp
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤2,Trace M t (cfg M (start M) b0 p0) (cfg M (.init .done) b1 p0) := by
    simpa [b0,b1,blockBank,NativeOracleBlock.blockBank,target] using initialize_call M b0 p0 rfl
  have j0 := jump M (.init .done) .check b1 p0 rfl
  obtain ⟨t1,h1,tr1⟩ :
      ∃ t≤blocks.length*(NativeOracleBlock.blockBudget M fs.length fs.length T+2)+1,
        Trace M t (cfg M .check b1 p0) (cfg M (.seal .seal) b2 p1) := by
    simpa [b1,b2,p0,p1,xs,ys,Counter.marked,RowStream.closedTape,symbols] using
      loop_trace M f fs hfs T blocks hb [.start] [] sp tp kp
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤2*ys.length+5,Trace M t (cfg M (.seal .seal) b2 p1)
      (cfg M (.seal .done) b3 p2) := by
    simpa [b2,b3,p1,p2,blockBank,blockPos,NativeOracleBlock.blockBank,NativeOracleBlock.blockPos,target] using seal_call M b2 p1 ys rfl
  have j2 := jump M (.seal .done) (.rewind .back) b3 p2 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤2*xs.length+4,Trace M t (cfg M (.rewind .back) b3 p2)
      (cfg M (.rewind .done) b4 p0) := by
    simpa [b3,b4,p2,p0,blockBank,blockPos,NativeOracleBlock.blockBank,NativeOracleBlock.blockPos,source] using rewind_call M b3 p2 xs rfl
  have j3 := jump M (.rewind .done) .done b4 p0 rfl
  have a0 := trace_trans tr0 j0
  have a1 := trace_trans a0 tr1
  have a2 := trace_trans a1 tr2
  have a3 := trace_trans a2 j2
  have a4 := trace_trans a3 tr3
  have a5 := trace_trans a4 j3
  refine ⟨_,?_,a5⟩
  dsimp [batchBudget]
  simp only [NativeOracleBlock.blockBudget] at h1
  rw [hx] at h3
  rw [hy] at h2
  nlinarith

 theorem batchBudget_linear (M : Transpose.TM) (C n b T : ℕ) (hb : 1≤b) (hT : T≤C*b) :
    batchBudget M n b T≤(NativeOracleReset.overhead M*(C+1)+66)*(n*b)+20 := by
  have hr := NativeOracleReset.budget_le M T
  have ht : T+1≤(C+1)*b := by nlinarith
  have hs : NativeOracleReset.budget M T≤NativeOracleReset.overhead M*((C+1)*b) :=
    hr.trans (Nat.mul_le_mul_left _ ht)
  have hu : NativeOracleReset.budget M T+24*b+42≤
      (NativeOracleReset.overhead M*(C+1)+66)*b := by nlinarith
  have hv := Nat.mul_le_mul_left n hu
  unfold batchBudget
  nlinarith

end
end BitWord.NativeOracleBatch
