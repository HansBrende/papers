import BitWord.NativeResizeRows

/-! A reusable native width-expansion/cropping subroutine. The input and both
physical rulers are preserved; the new output and every head position are exact. -/
namespace BitWord.NativeResize
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop
open NativeResizeScan (Port Bank markedRuler inputRows outputRows positions)

inductive Label
  | init (pc : NativeBuffer.Label)
  | scan (pc : NativeResizeScan.Label)
  | seal (pc : NativeSealBack.Label)
  | rewind (pc : NativeSealBack.Label)
  | done
  deriving DecidableEq, Fintype

def allBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

@[simp] theorem all_values {A : Type*} (f g : Port → A) : allBinding.values f g=f := rfl

def start : Label := .init (.erase 0)
def program (expand : Bool) : Microcode.Program Port Label
  | .init .done => .jump (.scan .begin)
  | .init pc => (singleBinding 1).instruction Label.init (NativeBuffer.program pc)
  | .scan .done => .jump (.seal .seal)
  | .scan pc => allBinding.instruction Label.scan (NativeResizeScan.program expand pc)
  | .seal .done => .jump (.rewind .back)
  | .seal pc => (singleBinding 1).instruction Label.seal (NativeSealBack.program pc)
  | .rewind .done => .jump .done
  | .rewind pc => (singleBinding 0).instruction Label.rewind (NativeSealBack.program pc)
  | .done => .halt

abbrev cfg := workCfg (T := Port) (L := Label)
abbrev Trace (expand : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program expand)) (NativeMicrocode.Active (program expand))

theorem init_code (expand : Bool) :
    NativeTapeCalls.Code (program expand) 1 Label.init NativeBuffer.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem scan_code (expand : Bool) (pc : NativeResizeScan.Label)
    (hh : NativeResizeScan.program expand pc ≠ .halt) (_ : NativeResizeScan.program expand pc ≠ .reject) :
    program expand (.scan pc)=MicrocodeEmbedding.instruction allBinding.ports Label.scan
      (NativeResizeScan.program expand pc) := by
  cases pc <;> simp_all [program,NativeResizeScan.program,NativeResizeScan.programCore,FinitePortBinding.instruction_eq]

theorem seal_code (expand : Bool) :
    NativeTapeCalls.Code (program expand) 1 Label.seal NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem rewind_code (expand : Bool) :
    NativeTapeCalls.Code (program expand) 0 Label.rewind NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

@[simp] theorem update_four_zero {A : Type*} (a b c d x : A) :
    Function.update ![a,b,c,d] (0:Fin 4) x=![x,b,c,d] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_four_one {A : Type*} (a b c d x : A) :
    Function.update ![a,b,c,d] (1:Fin 4) x=![a,x,c,d] := by funext i; fin_cases i <;> rfl
@[simp] theorem four_eta {A : Type*} (f : Fin 4 → A) : ![f 0,f 1,f 2,f 3]=f := by
  funext i; fin_cases i <;> rfl

theorem scan_call (expand : Bool) (a e : ℕ) (ha : 0<a)
    (rows : List (List Bool × List Bool))
    (hlen : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e) (pos : Port → ℤ) :
    ∃ t ≤ 20*(rows.length*(a+e))+1,Trace expand t
      (cfg (.scan .begin) ![Counter.marked (inputRows expand rows),NativeSealBack.openWord [],
        markedRuler a,markedRuler (a+e)] pos)
      (cfg (.scan .done) ![⟨(symbols (inputRows expand rows)).reverse++[.start],[.stop]⟩,
        NativeSealBack.openWord (outputRows expand rows),markedRuler a,markedRuler (a+e)]
        (positions pos (inputRows expand rows).length (outputRows expand rows).length 0 0)) := by
  obtain ⟨t,ht,htr⟩ := NativeResizeScan.rows_trace expand a e ha rows hlen [.start] [] pos
  have hh := MicrocodeEmbedding.trace_embed allBinding.ports Label.scan (NativeResizeScan.program expand)
    (program expand) (frame (fun _ => ⟨[],[]⟩) pos) (scan_code expand) htr
  change Trace expand t
    (MicrocodeEmbedding.embed allBinding.ports Label.scan
      (workCfg .begin ![Counter.marked (inputRows expand rows),NativeSealBack.openWord [],
        markedRuler a,markedRuler (a+e)] pos) _)
    (MicrocodeEmbedding.embed allBinding.ports Label.scan
      (workCfg .done ![⟨(symbols (inputRows expand rows)).reverse++[.start],[.stop]⟩,
        NativeSealBack.openWord ([]++outputRows expand rows),markedRuler a,markedRuler (a+e)]
        (positions pos (inputRows expand rows).length (outputRows expand rows).length 0 0)) _) at hh
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht.trans (NativeResizeScan.rows_linear_budget a e rows.length ha),
    by simpa only [all_values,List.nil_append] using hh⟩

theorem jump (expand : Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program expand pc=.jump next) : Trace expand 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

/-- No input-dependent machine resources appear in this width conversion. -/
theorem complete_trace (expand : Bool) (a e : ℕ) (ha : 0<a)
    (rows : List (List Bool × List Bool))
    (hlen : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e) (pos : Port → ℤ) :
    ∃ t ≤ 24*(rows.length*(a+e))+20,Trace expand t
      (cfg start ![Counter.marked (inputRows expand rows),⟨[],[]⟩,markedRuler a,markedRuler (a+e)] pos)
      (cfg .done ![Counter.marked (inputRows expand rows),Counter.marked (outputRows expand rows),
        markedRuler a,markedRuler (a+e)] pos) := by
  let xs := inputRows expand rows
  let ys := outputRows expand rows
  let b0 : Bank := ![Counter.marked xs,⟨[],[]⟩,markedRuler a,markedRuler (a+e)]
  let b1 : Bank := ![Counter.marked xs,NativeSealBack.openWord [],markedRuler a,markedRuler (a+e)]
  let b2 : Bank := ![⟨(symbols xs).reverse++[.start],[.stop]⟩,NativeSealBack.openWord ys,markedRuler a,markedRuler (a+e)]
  let b3 : Bank := ![⟨(symbols xs).reverse++[.start],[.stop]⟩,Counter.marked ys,markedRuler a,markedRuler (a+e)]
  let b4 : Bank := ![Counter.marked xs,Counter.marked ys,markedRuler a,markedRuler (a+e)]
  let p2 := positions pos xs.length ys.length 0 0
  let p3 := positions pos xs.length 0 0 0
  obtain ⟨t0,h0,tr0⟩ : ∃ t ≤ 2,Trace expand t (cfg start b0 pos) (cfg (.init .done) b1 pos) := by
    simpa [start,b0,b1] using NativeTapeCalls.initialize_call (program expand) 1 Label.init
      (init_code expand) b0 pos rfl
  have j0 := jump expand (.init .done) (.scan .begin) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t ≤ 20*(rows.length*(a+e))+1,Trace expand t
      (cfg (.scan .begin) b1 pos) (cfg (.scan .done) b2 p2) := scan_call expand a e ha rows hlen pos
  have j1 := jump expand (.scan .done) (.seal .seal) b2 p2 rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t ≤ 2*ys.length+5,Trace expand t
      (cfg (.seal .seal) b2 p2) (cfg (.seal .done) b3 p3) := by
    simpa [b2,b3,p2,p3,positions] using NativeTapeCalls.seal_call (program expand) 1 Label.seal
      (seal_code expand) b2 p2 ys rfl
  have j2 := jump expand (.seal .done) (.rewind .back) b3 p3 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t ≤ 2*xs.length+4,Trace expand t
      (cfg (.rewind .back) b3 p3) (cfg (.rewind .done) b4 pos) := by
    simpa [b3,b4,p3,positions] using NativeTapeCalls.rewind (program expand) 0 Label.rewind
      (rewind_code expand) b3 p3 xs rfl
  have j3 := jump expand (.rewind .done) .done b4 pos rfl
  have seg0 := trace_trans tr0 j0
  have seg1 := trace_trans tr1 j1
  have seg2 := trace_trans tr2 j2
  have seg3 := trace_trans tr3 j3
  have acc1 := trace_trans seg0 seg1
  have acc2 := trace_trans acc1 seg2
  have acc3 := trace_trans acc2 seg3
  obtain ⟨hin,hout⟩ := NativeResizeScan.rows_lengths_le expand a e rows hlen
  refine ⟨_,?_,acc3⟩
  change t2≤2*(outputRows expand rows).length+5 at h2
  change t3≤2*(inputRows expand rows).length+4 at h3
  omega

end BitWord.NativeResize
