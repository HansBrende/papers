import BitWord.NativeUnsplit

namespace BitWord.NativeUnsplit
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop
open NativeResize (update_four_zero update_four_one four_eta)

@[simp] theorem update_four_two {A : Type*} (a b c d x : A) :
    Function.update ![a,b,c,d] (2:Fin 4) x=![a,b,x,d] := by funext i; fin_cases i <;> rfl

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) := NativeMicrocode.jump_trace _ _ _ h

/-- Split the two contiguous halves with a clocked copy, erase the original,
and interleave back into the same tape. All scratch and all heads are restored. -/
theorem complete_trace (a b fs : List Bool) (hab : a.length=b.length) (hfs : fs.length=a.length)
    (pos : Port → ℤ) :
    ∃ t≤50*a.length+80,Trace t
      (cfg start ![Counter.marked (a++b),⟨[],[]⟩,⟨[],[]⟩,Counter.marked fs] pos)
      (cfg .done ![Counter.marked (NativeInterleave.output a b),⟨[],[]⟩,⟨[],[]⟩,Counter.marked fs] pos) := by
  let z : Tape Bool := ⟨[],[]⟩
  let mk := Counter.marked
  let op := NativeSealBack.openWord []
  let mid : Tape Bool := ⟨(symbols a).reverse++[.start],symbols b++[.stop]⟩
  let last : Tape Bool := ⟨(symbols (a++b)).reverse++[.start],[.stop]⟩
  let b0 : Bank := ![mk (a++b),z,z,mk fs]
  let b1 : Bank := ![mk (a++b),op,z,mk fs]
  let b2 : Bank := ![mid,mk a,z,mk fs]
  let b3 : Bank := ![mid,mk a,op,mk fs]
  let b4 : Bank := ![last,mk a,mk b,mk fs]
  let b5 : Bank := ![mk (a++b),mk a,mk b,mk fs]
  let b6 : Bank := ![z,mk a,mk b,mk fs]
  let b7 : Bank := ![mk (NativeInterleave.output a b),z,z,mk fs]
  let p2 := shifted pos a.length
  let p4 := shifted pos (a++b).length
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤2,Trace t (cfg start b0 pos) (cfg (.init false .done) b1 pos) := by
    simpa [start,b0,b1,op,scratch,z] using NativeTapeCalls.initialize_call program 1 (Label.init false)
      (init_code false) b0 pos rfl
  have j0 := jump (.init false .done) (.copy false .scan) b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤6*a.length+5,Trace t
      (cfg (.copy false .scan) b1 pos) (cfg (.copy false .done) b2 p2) := by
    simpa [copyBank,b1,b2,p2,mid,mk,Counter.marked,op,symbols,List.map_append,List.append_assoc] using
      copy_call false a fs hfs [.start] (symbols b++[.stop]) z pos
  have j1 := jump (.copy false .done) (.init true (.erase 0)) b2 p2 rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤2,Trace t
      (cfg (.init true (.erase 0)) b2 p2) (cfg (.init true .done) b3 p2) := by
    simpa [b2,b3,op,scratch,z] using NativeTapeCalls.initialize_call program 2 (Label.init true)
      (init_code true) b2 p2 rfl
  have j2 := jump (.init true .done) (.copy true .scan) b3 p2 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤6*b.length+5,Trace t
      (cfg (.copy true .scan) b3 p2) (cfg (.copy true .done) b4 p4) := by
    simpa [copyBank,b3,b4,p2,p4,mid,last,mk,op,symbols,List.map_append,List.reverse_append,
      List.append_assoc,shifted_add] using copy_call true b fs (hfs.trans hab)
        ((symbols a).reverse++[.start]) [.stop] (mk a) p2
  have j3 := jump (.copy true .done) (.rewind .back) b4 p4 rfl
  obtain ⟨t4,h4,tr4⟩ : ∃ t≤2*(a++b).length+4,Trace t
      (cfg (.rewind .back) b4 p4) (cfg (.rewind .done) b5 pos) := by
    simpa [b4,b5,p4,shifted,mk] using NativeTapeCalls.rewind program 0 Label.rewind
      rewind_code b4 p4 (a++b) rfl
  have j4 := jump (.rewind .done) (.erase 2) b5 pos rfl
  obtain ⟨t5,h5,tr5⟩ : ∃ t≤4*(a++b).length+4,Trace t
      (cfg (.erase 2) b5 pos) (cfg (.erase 0) b6 pos) := by
    simpa [b5,b6,z] using NativeTapeCalls.erase program 0 Label.erase erase_code b5 pos (a++b) rfl
  have j5 := jump (.erase 0) (.shuffle NativeInterleave.start) b6 pos rfl
  obtain ⟨t6,h6,tr6⟩ : ∃ t≤20*a.length+40,Trace t
      (cfg (.shuffle NativeInterleave.start) b6 pos) (cfg (.shuffle .done) b7 pos) := shuffle_call a b hab (mk fs) pos
  have j6 := jump (.shuffle .done) .done b7 pos rfl
  have s0 := trace_trans tr0 j0
  have s1 := trace_trans tr1 j1
  have s2 := trace_trans tr2 j2
  have s3 := trace_trans tr3 j3
  have s4 := trace_trans tr4 j4
  have s5 := trace_trans tr5 j5
  have s6 := trace_trans tr6 j6
  have acc1 := trace_trans s0 s1
  have acc2 := trace_trans acc1 s2
  have acc3 := trace_trans acc2 s3
  have acc4 := trace_trans acc3 s4
  have acc5 := trace_trans acc4 s5
  have acc6 := trace_trans acc5 s6
  refine ⟨_,?_,acc6⟩
  simp only [List.length_append] at h4 h5
  omega

end BitWord.NativeUnsplit
