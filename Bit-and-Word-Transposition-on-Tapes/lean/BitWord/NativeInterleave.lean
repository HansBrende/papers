import BitWord.NativeInterleaveScan
import BitWord.NativeSplitRun
import BitWord.NativeTapeCalls

/-! Paid interleaving of two equal-length streams, with both inputs erased and
all heads returned to their initial coordinates. -/
namespace BitWord.NativeInterleave
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop
open NativeSplit (update_three_zero update_three_one update_three_two three_eta all_values split_positions)
abbrev Port := Fin 3
abbrev Bank := Port → Tape Bool
abbrev output := NativeInterleaveScan.interleave

def scratch (side : Bool) : Port := if side then 2 else 1

inductive Label
  | init (pc : NativeBuffer.Label)
  | scan (pc : NativeInterleaveScan.Label)
  | seal (port : Port) (pc : NativeSealBack.Label)
  | erase (side : Bool) (pc : NativeErase.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .init (.erase 0)

def program : Microcode.Program Port Label
  | .init .done => .jump (.scan (.scan false))
  | .init pc => (singleBinding 0).instruction Label.init (NativeBuffer.program pc)
  | .scan .done => .jump (.seal 0 .seal)
  | .scan pc => NativeSplit.allBinding.instruction Label.scan (NativeInterleaveScan.program pc)
  | .seal port .done => .jump (if port=0 then .seal 1 .back else if port=1 then .seal 2 .back else .erase false 2)
  | .seal port pc => (singleBinding port).instruction (Label.seal port) (NativeSealBack.program pc)
  | .erase side pc => if pc=0 then .jump (if side then .done else .erase true 2)
      else (singleBinding (scratch side)).instruction (Label.erase side) (NativeErase.program pc)
  | .done => .halt

abbrev cfg := workCfg (T := Port) (L := Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem init_code : NativeTapeCalls.Code program 0 Label.init NativeBuffer.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem scan_code (pc : NativeInterleaveScan.Label)
    (hh : NativeInterleaveScan.program pc ≠ .halt) (_ : NativeInterleaveScan.program pc ≠ .reject) :
    program (.scan pc)=MicrocodeEmbedding.instruction NativeSplit.allBinding.ports Label.scan
      (NativeInterleaveScan.program pc) := by
  cases pc <;> simp_all [program,NativeInterleaveScan.program,FinitePortBinding.instruction_eq]

theorem seal_code (port : Port) :
    NativeTapeCalls.Code program port (Label.seal port) NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem erase_code (side : Bool) :
    NativeTapeCalls.Code program (scratch side) (Label.erase side) NativeErase.program := by
  intro pc hh _
  have hp : pc ≠ 0 := by intro h; subst pc; exact hh rfl
  simp only [program,ite_eq_right hp,FinitePortBinding.instruction_eq]

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) := NativeMicrocode.jump_trace _ _ _ h

theorem scan_call (a b : List Bool) (hab : a.length=b.length) (pos : Port → ℤ) :
    ∃ t ≤ 4*a.length+1,Trace t
      (cfg (.scan (.scan false)) ![NativeSealBack.openWord [],Counter.marked a,Counter.marked b] pos)
      (cfg (.scan .done) ![NativeSealBack.openWord (output a b),
        ⟨(symbols a).reverse++[.start],[.stop]⟩,⟨(symbols b).reverse++[.start],[.stop]⟩]
        ![pos 0+2*a.length,pos 1+a.length,pos 2+b.length]) := by
  obtain ⟨t,ht,htr⟩ := NativeInterleaveScan.interleave_trace a b hab [.start] [] [.start] [] [] pos
  have hh := MicrocodeEmbedding.trace_embed NativeSplit.allBinding.ports Label.scan NativeInterleaveScan.program program
    (frame (fun _ => ⟨[],[]⟩) pos) scan_code htr
  change Trace t
    (MicrocodeEmbedding.embed NativeSplit.allBinding.ports Label.scan
      (workCfg (.scan false) ![NativeSealBack.openWord [],Counter.marked a,Counter.marked b] pos) _)
    (MicrocodeEmbedding.embed NativeSplit.allBinding.ports Label.scan
      (workCfg .done ![NativeSealBack.openWord ([]++output a b),
        ⟨(symbols a).reverse++[.start],[.stop]⟩,⟨(symbols b).reverse++[.start],[.stop]⟩]
        (NativeSplitScan.positions pos (2*a.length) a.length b.length)) _) at hh
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht,by simpa only [all_values,List.nil_append,split_positions,Nat.cast_mul,Nat.cast_ofNat] using hh⟩

/-- Equal-length inputs on the two scratch ports are interleaved into a blank
output port. Every transition, rewind, and scratch erasure is charged. -/
theorem complete_trace (a b : List Bool) (hab : a.length=b.length) (pos : Port → ℤ) :
    ∃ t ≤ 20*a.length+40,Trace t
      (cfg start ![⟨[],[]⟩,Counter.marked a,Counter.marked b] pos)
      (cfg .done ![Counter.marked (output a b),⟨[],[]⟩,⟨[],[]⟩] pos) := by
  let z : Tape Bool := ⟨[],[]⟩
  let op := NativeSealBack.openWord
  let mk := Counter.marked
  let b0 : Bank := ![z,mk a,mk b]
  let b1 : Bank := ![op [],mk a,mk b]
  let b2 : Bank := ![op (output a b),⟨(symbols a).reverse++[.start],[.stop]⟩,⟨(symbols b).reverse++[.start],[.stop]⟩]
  let b3 : Bank := ![mk (output a b),⟨(symbols a).reverse++[.start],[.stop]⟩,⟨(symbols b).reverse++[.start],[.stop]⟩]
  let b4 : Bank := ![mk (output a b),mk a,⟨(symbols b).reverse++[.start],[.stop]⟩]
  let b5 : Bank := ![mk (output a b),mk a,mk b]
  let b6 : Bank := ![mk (output a b),z,mk b]
  let b7 : Bank := ![mk (output a b),z,z]
  let p2 : Port → ℤ := ![pos 0+2*a.length,pos 1+a.length,pos 2+b.length]
  let p3 : Port → ℤ := ![pos 0,pos 1+a.length,pos 2+b.length]
  let p4 : Port → ℤ := ![pos 0,pos 1,pos 2+b.length]
  have hlen : (output a b).length=2*a.length := NativeInterleaveScan.interleave_length a b hab
  obtain ⟨t0,h0,tr0⟩ : ∃ t ≤ 2,Trace t (cfg start b0 pos) (cfg (.init .done) b1 pos) := by
    simpa [start,b0,b1,op,z] using NativeTapeCalls.initialize_call program 0 Label.init init_code b0 pos rfl
  have j0 := jump (.init .done) (.scan (.scan false)) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t ≤ 4*a.length+1,Trace t (cfg (.scan (.scan false)) b1 pos) (cfg (.scan .done) b2 p2) :=
    scan_call a b hab pos
  have j1 := jump (.scan .done) (.seal 0 .seal) b2 p2 rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t ≤ 2*(output a b).length+5,Trace t (cfg (.seal 0 .seal) b2 p2) (cfg (.seal 0 .done) b3 p3) := by
    simpa [b2,b3,p2,p3,mk,hlen] using NativeTapeCalls.seal_call program 0 (Label.seal 0) (seal_code 0) b2 p2 (output a b) rfl
  have j2 := jump (.seal 0 .done) (.seal 1 .back) b3 p3 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t ≤ 2*a.length+4,Trace t (cfg (.seal 1 .back) b3 p3) (cfg (.seal 1 .done) b4 p4) := by
    simpa [b3,b4,p3,p4,mk] using NativeTapeCalls.rewind program 1 (Label.seal 1) (seal_code 1) b3 p3 a rfl
  have j3 := jump (.seal 1 .done) (.seal 2 .back) b4 p4 rfl
  obtain ⟨t4,h4,tr4⟩ : ∃ t ≤ 2*b.length+4,Trace t (cfg (.seal 2 .back) b4 p4) (cfg (.seal 2 .done) b5 pos) := by
    simpa [b4,b5,p4,mk] using NativeTapeCalls.rewind program 2 (Label.seal 2) (seal_code 2) b4 p4 b rfl
  have j4 := jump (.seal 2 .done) (.erase false 2) b5 pos rfl
  obtain ⟨t5,h5,tr5⟩ : ∃ t ≤ 4*a.length+4,Trace t (cfg (.erase false 2) b5 pos) (cfg (.erase false 0) b6 pos) := by
    simpa [b5,b6,scratch,z] using NativeTapeCalls.erase program 1 (Label.erase false) (erase_code false) b5 pos a rfl
  have j5 := jump (.erase false 0) (.erase true 2) b6 pos rfl
  obtain ⟨t6,h6,tr6⟩ : ∃ t ≤ 4*b.length+4,Trace t (cfg (.erase true 2) b6 pos) (cfg (.erase true 0) b7 pos) := by
    simpa [b6,b7,scratch,z] using NativeTapeCalls.erase program 2 (Label.erase true) (erase_code true) b6 pos b rfl
  have j6 := jump (.erase true 0) .done b7 pos rfl
  have seg0 := trace_trans tr0 j0
  have seg1 := trace_trans tr1 j1
  have seg2 := trace_trans tr2 j2
  have seg3 := trace_trans tr3 j3
  have seg4 := trace_trans tr4 j4
  have seg5 := trace_trans tr5 j5
  have seg6 := trace_trans tr6 j6
  have acc1 := trace_trans seg0 seg1
  have acc2 := trace_trans acc1 seg2
  have acc3 := trace_trans acc2 seg3
  have acc4 := trace_trans acc3 seg4
  have acc5 := trace_trans acc4 seg5
  have acc6 := trace_trans acc5 seg6
  refine ⟨_,?_,acc6⟩
  omega

end BitWord.NativeInterleave
