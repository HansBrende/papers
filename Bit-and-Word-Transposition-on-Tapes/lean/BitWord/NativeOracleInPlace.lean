import BitWord.ReductionOracle
import TransposeFollowup.NativeMappedCopy

/-! Return a batched suffix call to the same main-bank port. Explicit erasure
and copying replace any free renaming or free exchange of data tapes. -/
namespace BitWord.NativeOracleInPlace
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls NativeCountedLoop
set_option autoImplicit false
noncomputable section
abbrev Port (M : Transpose.TM) := NativeOracleBatch.Port M
abbrev Bank (M : Transpose.TM) := Port M → Tape Bool
abbrev source := NativeOracleBlock.source
abbrev target := NativeOracleBlock.target
abbrev blockBank := NativeOracleBlock.blockBank
abbrev blockPos := NativeOracleBlock.blockPos

def copyBinding (M : Transpose.TM) := pairBinding (target M) (source M) (by simp [target,source,NativeOracleBlock.target,NativeOracleBlock.source])

inductive Label (M : Transpose.TM)
  | batch (pc : NativeOracleBatch.Label M)
  | eraseSource (pc : NativeErase.Label)
  | copy (pc : NativeMappedCopy.Label)
  | eraseTarget (pc : NativeErase.Label)
  | done
  deriving Fintype
noncomputable instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _
def start (M : Transpose.TM) : Label M := .batch (NativeOracleBatch.start M)
def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .batch .done => .jump (.eraseSource 2)
  | .batch pc => (NativeOracleBatch.allBinding M).instruction Label.batch (NativeOracleBatch.program M pc)
  | .eraseSource pc => if pc=0 then .jump (.copy (.init (.erase 0))) else
      (singleBinding (source M)).instruction Label.eraseSource (NativeErase.program pc)
  | .copy (.seal .done) => .jump (.eraseTarget 2)
  | .copy pc => (copyBinding M).instruction Label.copy (NativeMappedCopy.program id pc)
  | .eraseTarget pc => if pc=0 then .jump .done else
      (singleBinding (target M)).instruction Label.eraseTarget (NativeErase.program pc)
  | .done => .halt
abbrev Trace (M : Transpose.TM) := OperationalTrace.Trace (NativeMicrocode.step (program M))
  (NativeMicrocode.Active (program M))
abbrev cfg (M : Transpose.TM) := workCfg (T := Port M) (L := Label M)

theorem batch_code (M : Transpose.TM) (pc : NativeOracleBatch.Label M)
    (hh : NativeOracleBatch.program M pc≠.halt) (_ : NativeOracleBatch.program M pc≠.reject) :
    program M (.batch pc)=MicrocodeEmbedding.instruction (NativeOracleBatch.allBinding M).ports
      Label.batch (NativeOracleBatch.program M pc) := by
  cases pc <;> simp_all [program,NativeOracleBatch.program,FinitePortBinding.instruction_eq]
theorem eraseSource_code (M : Transpose.TM) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program M (.eraseSource pc)=MicrocodeEmbedding.instruction (singleBinding (source M)).ports
      Label.eraseSource (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem eraseTarget_code (M : Transpose.TM) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program M (.eraseTarget pc)=MicrocodeEmbedding.instruction (singleBinding (target M)).ports
      Label.eraseTarget (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem copy_code (M : Transpose.TM) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    program M (.copy pc)=MicrocodeEmbedding.instruction (copyBinding M).ports
      Label.copy (NativeMappedCopy.program id pc) := by
  cases pc with
  | init pc => simp [program,FinitePortBinding.instruction_eq]
  | append pc => simp [program,FinitePortBinding.instruction_eq]
  | «seal» pc => cases pc <;>
      simp_all [program,NativeMappedCopy.program,NativeSealBack.program,FinitePortBinding.instruction_eq,MicrocodeEmbedding.instruction]

theorem jump (M : Transpose.TM) (pc next : Label M) (s : Bank M) (pos : Port M → ℤ)
    (h : program M pc=.jump next) : Trace M 1 (cfg M pc s pos) (cfg M next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem erase_source_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (xs : List Bool)
    (hs : s (source M)=Counter.marked xs) :
    ∃ t≤4*xs.length+4,Trace M t (cfg M (.eraseSource 2) s pos)
      (cfg M (.eraseSource 0) (Function.update s (source M) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (source M))
  have hh := call_single (source M) Label.eraseSource NativeErase.program (program M) (eraseSource_code M)
    2 0 s pos ⟨[],[]⟩ (pos (source M)) t
  have hh' := hh (by simpa [workCfg,NativeErase.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩
theorem erase_target_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (xs : List Bool)
    (hs : s (target M)=Counter.marked xs) :
    ∃ t≤4*xs.length+4,Trace M t (cfg M (.eraseTarget 2) s pos)
      (cfg M (.eraseTarget 0) (Function.update s (target M) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (target M))
  have hh := call_single (target M) Label.eraseTarget NativeErase.program (program M) (eraseTarget_code M)
    2 0 s pos ⟨[],[]⟩ (pos (target M)) t
  have hh' := hh (by simpa [workCfg,NativeErase.cfg,NativeZipper.Config.denote,
    Microcode.Config.denote,Microcode.focus,hs] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

@[simp] theorem copy_bank (a b : Tape Bool) : NativeMappedCopy.bank a b=![a,b] := by
  funext i; fin_cases i <;> rfl

theorem copy_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ) (xs : List Bool)
    (hs : s (target M)=Counter.marked xs) (hd : s (source M)=⟨[],[]⟩) :
    ∃ t≤6*xs.length+14,Trace M t (cfg M (.copy (.init (.erase 0))) s pos)
      (cfg M (.copy (.seal .done)) (Function.update s (source M) (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs ![pos (target M),pos (source M)]
  have hh := call_pair (target M) (source M) (by simp [target,source,NativeOracleBlock.target,NativeOracleBlock.source]) Label.copy
    (NativeMappedCopy.program id) (program M) (copy_code M) (.init (.erase 0)) (.seal .done)
    s pos (s (target M)) (Counter.marked xs) (pos (target M)) (pos (source M)) t
  have hh' := hh (by
    simpa [workCfg,NativeMappedCopy.cfg,copy_bank,hs,hd] using htr)
  exact ⟨t,ht,by simpa only [Function.update_eq_self] using hh'⟩

/-- The fixed program executes a suffix gate in place; its only variable
parameter is supplied as the separately constructed unary block ruler. -/
theorem suffix_trace (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    {N k : ℕ} (hk : 2*k≤N) (bank : Address N → Bool) (sp tp kp : ℤ) :
    ∃ t≤(NativeOracleBatch.suffixConstant M C+44)*(2^N),Trace M t
      (cfg M (start M) (blockBank M (Counter.marked (flattenBank bank)) ⟨[],[]⟩
        (List.replicate (4^k) true)) (blockPos M sp tp kp))
      (cfg M .done (blockBank M
        (Counter.marked (flattenBank (moveBank (Gate.equiv N (.suffix k) hk) bank))) ⟨[],[]⟩
        (List.replicate (4^k) true)) (blockPos M sp tp kp)) := by
  let xs := flattenBank bank
  let ys := flattenBank (moveBank (Gate.equiv N (.suffix k) hk) bank)
  let fs := List.replicate (4^k) true
  let pos := blockPos M sp tp kp
  let b0 := blockBank M (Counter.marked xs) ⟨[],[]⟩ fs
  let b1 := blockBank M (Counter.marked xs) (Counter.marked ys) fs
  let b2 := blockBank M ⟨[],[]⟩ (Counter.marked ys) fs
  let b3 := blockBank M (Counter.marked ys) (Counter.marked ys) fs
  let b4 := blockBank M (Counter.marked ys) ⟨[],[]⟩ fs
  obtain ⟨t0,h0,tr⟩ := NativeOracleBatch.suffix_trace M C hM hk bank sp tp kp
  have he := MicrocodeEmbedding.trace_embed (NativeOracleBatch.allBinding M).ports Label.batch
    (NativeOracleBatch.program M) (program M) (frame (fun _ => ⟨[],[]⟩) (fun _ => 0)) (batch_code M) tr
  rw [embed_work,embed_work] at he
  have tr0 : Trace M t0 (cfg M (start M) b0 pos) (cfg M (.batch .done) b1 pos) := by
    simpa only [NativeOracleBatch.all_values,start,b0,b1,pos,xs,ys,fs] using he
  have j0 := jump M (.batch .done) (.eraseSource 2) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤4*xs.length+4,Trace M t (cfg M (.eraseSource 2) b1 pos)
      (cfg M (.eraseSource 0) b2 pos) := by
    simpa [b1,b2,blockBank,NativeOracleBlock.blockBank,source] using erase_source_call M b1 pos xs rfl
  have j1 := jump M (.eraseSource 0) (.copy (.init (.erase 0))) b2 pos (by simp [program])
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤6*ys.length+14,Trace M t (cfg M (.copy (.init (.erase 0))) b2 pos)
      (cfg M (.copy (.seal .done)) b3 pos) := by
    simpa [b2,b3,blockBank,NativeOracleBlock.blockBank,source] using copy_call M b2 pos ys rfl rfl
  have j2 := jump M (.copy (.seal .done)) (.eraseTarget 2) b3 pos rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤4*ys.length+4,Trace M t (cfg M (.eraseTarget 2) b3 pos)
      (cfg M (.eraseTarget 0) b4 pos) := by
    simpa [b3,b4,blockBank,NativeOracleBlock.blockBank,target] using erase_target_call M b3 pos ys rfl
  have j3 := jump M (.eraseTarget 0) .done b4 pos (by simp [program])
  have a0 := trace_trans tr0 j0
  have a1 := trace_trans a0 tr1
  have a2 := trace_trans a1 j1
  have a3 := trace_trans a2 tr2
  have a4 := trace_trans a3 j2
  have a5 := trace_trans a4 tr3
  have a6 := trace_trans a5 j3
  refine ⟨_,?_,a6⟩
  have hx : xs.length=2^N := flattenBank_length _
  have hy : ys.length=2^N := flattenBank_length _
  have hn : 1≤2^N := Nat.succ_le_of_lt (by positivity)
  rw [hx] at h1
  rw [hy] at h2 h3
  nlinarith

end
end BitWord.NativeOracleInPlace
