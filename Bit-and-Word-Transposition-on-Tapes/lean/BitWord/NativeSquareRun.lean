import BitWord.NativeSquareTail

namespace BitWord.NativeSquare
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop
open NativeResizeScan (markedRuler endRuler inputRecord outputRecord inputRows outputRows consumed tailOutput)

def inputSquare (expand : Bool) (rows : List (List Bool × List Bool)) (extras : List (List Bool)) :=
  inputRows expand rows++tailInputs expand extras

def outputSquare (expand : Bool) (rows : List (List Bool × List Bool)) (extras : List (List Bool)) :=
  outputRows expand rows++tailOutputs expand extras

theorem tails_lengths_le (expand : Bool) (b : ℕ) (extras : List (List Bool))
    (hlen : ∀ r ∈ extras,r.length=b) :
    (tailInputs expand extras).length ≤ extras.length*b ∧
    (tailOutputs expand extras).length ≤ extras.length*b := by
  induction extras with
  | nil => simp [tailInputs,tailOutputs]
  | cons r rows ih =>
    have hr := hlen r (by simp)
    have ht : ∀ r ∈ rows,r.length=b := by intro r h; exact hlen r (by simp [h])
    obtain ⟨hi,ho⟩ := ih ht
    cases expand <;> simp_all [tailInputs,tailOutputs,consumed,tailOutput,Nat.add_mul] <;> omega

theorem square_lengths_le (expand : Bool) (a e : ℕ) (rows : List (List Bool × List Bool))
    (extras : List (List Bool)) (hr : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e)
    (he : ∀ r ∈ extras,r.length=a+e) :
    (inputSquare expand rows extras).length ≤ (rows.length+extras.length)*(a+e) ∧
    (outputSquare expand rows extras).length ≤ (rows.length+extras.length)*(a+e) := by
  obtain ⟨hi,ho⟩ := NativeResizeScan.rows_lengths_le expand a e rows hr
  obtain ⟨hi',ho'⟩ := tails_lengths_le expand (a+e) extras he
  simp only [inputSquare,outputSquare,List.length_append,Nat.add_mul]
  omega

theorem scan_trace (expand : Bool) (a e : ℕ) (hb : 0<a+e)
    (rows : List (List Bool × List Bool)) (extras : List (List Bool))
    (hr : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e)
    (he : ∀ r ∈ extras,r.length=a+e) (pos : Port → ℤ) :
    ∃ t ≤ 22*((rows.length+extras.length)*(a+e))+2,Trace expand t
      (cfg .checkRows (bank (Counter.marked (inputSquare expand rows extras))
        (NativeSealBack.openWord []) a (a+e) (markedRuler rows.length)
        (markedRuler (rows.length+extras.length))) pos)
      (cfg (.seal .seal) (bank ⟨(symbols (inputSquare expand rows extras)).reverse++[.start],[.stop]⟩
        (NativeSealBack.openWord (outputSquare expand rows extras)) a (a+e)
        (endRuler rows.length) (endRuler (rows.length+extras.length)))
        (positions pos (inputSquare expand rows extras).length (outputSquare expand rows extras).length
          rows.length (rows.length+extras.length))) := by
  obtain ⟨t0,h0,tr0⟩ := rows_trace expand a e rows hr extras.length 0 0 [.start]
    (symbols (tailInputs expand extras)++[.stop]) [] pos
  obtain ⟨t1,h1,tr1⟩ := tails_trace expand a (a+e) extras he rows.length rows.length
    ((symbols (inputRows expand rows)).reverse++[.start]) [.stop] (outputRows expand rows)
    (positions pos (inputRows expand rows).length (outputRows expand rows).length rows.length rows.length)
  have tr0' : Trace expand t0
      (cfg .checkRows (bank (Counter.marked (inputSquare expand rows extras))
        (NativeSealBack.openWord []) a (a+e) (markedRuler rows.length)
        (markedRuler (rows.length+extras.length))) pos)
      (cfg .checkTail (bank ⟨(symbols (inputRows expand rows)).reverse++[.start],
        symbols (tailInputs expand extras)++[.stop]⟩ (NativeSealBack.openWord (outputRows expand rows))
        a (a+e) (cursor 0 rows.length) (cursor extras.length rows.length))
        (positions pos (inputRows expand rows).length (outputRows expand rows).length rows.length rows.length)) := by
    simpa [inputSquare,Counter.marked,symbols,List.map_append,List.append_assoc] using tr0
  have tr := trace_trans tr0' tr1
  refine ⟨t0+t1,?_,?_⟩
  · have hmain : 7*(a+e)+15≤22*(a+e) := by omega
    have htail : 5*(a+e)+14≤22*(a+e) := by omega
    have hmain' := Nat.mul_le_mul_left rows.length hmain
    have htail' := Nat.mul_le_mul_left extras.length htail
    nlinarith
  · simpa [inputSquare,outputSquare,symbols,List.map_append,List.reverse_append,List.append_assoc,
      positions_add] using tr

@[simp] theorem update_six_zero {A : Type*} (a b c d e f x : A) :
    Function.update ![a,b,c,d,e,f] (0:Fin 6) x=![x,b,c,d,e,f] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_six_one {A : Type*} (a b c d e f x : A) :
    Function.update ![a,b,c,d,e,f] (1:Fin 6) x=![a,x,c,d,e,f] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_six_four {A : Type*} (a b c d e f x : A) :
    Function.update ![a,b,c,d,e,f] (4:Fin 6) x=![a,b,c,d,x,f] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_six_five {A : Type*} (a b c d e f x : A) :
    Function.update ![a,b,c,d,e,f] (5:Fin 6) x=![a,b,c,d,e,x] := by funext i; fin_cases i <;> rfl
@[simp] theorem six_eta {A : Type*} (f : Fin 6 → A) : ![f 0,f 1,f 2,f 3,f 4,f 5]=f := by
  funext i; fin_cases i <;> rfl

theorem jump (expand : Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program expand pc=.jump next) : Trace expand 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

/-- One fixed controller performs rectangular padding or cropping, pays every
ruler traversal, and restores source, rulers, and all six heads. -/
theorem complete_trace (expand : Bool) (a e : ℕ) (hb : 0<a+e)
    (rows : List (List Bool × List Bool)) (extras : List (List Bool))
    (hr : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e)
    (he : ∀ r ∈ extras,r.length=a+e) (pos : Port → ℤ) :
    ∃ t ≤ 40*((rows.length+extras.length)*(a+e))+40,Trace expand t
      (cfg start (bank (Counter.marked (inputSquare expand rows extras)) ⟨[],[]⟩
        a (a+e) (markedRuler rows.length) (markedRuler (rows.length+extras.length))) pos)
      (cfg .done (bank (Counter.marked (inputSquare expand rows extras))
        (Counter.marked (outputSquare expand rows extras)) a (a+e)
        (markedRuler rows.length) (markedRuler (rows.length+extras.length))) pos) := by
  let xs := inputSquare expand rows extras
  let ys := outputSquare expand rows extras
  let R := rows.length
  let T := rows.length+extras.length
  let b0 := bank (Counter.marked xs) ⟨[],[]⟩ a (a+e) (markedRuler R) (markedRuler T)
  let b1 := bank (Counter.marked xs) (NativeSealBack.openWord []) a (a+e) (markedRuler R) (markedRuler T)
  let endSrc : Tape Bool := ⟨(symbols xs).reverse++[.start],[.stop]⟩
  let b2 := bank endSrc (NativeSealBack.openWord ys) a (a+e) (endRuler R) (endRuler T)
  let b3 := bank endSrc (Counter.marked ys) a (a+e) (endRuler R) (endRuler T)
  let b4 := bank (Counter.marked xs) (Counter.marked ys) a (a+e) (endRuler R) (endRuler T)
  let b5 := bank (Counter.marked xs) (Counter.marked ys) a (a+e) (markedRuler R) (endRuler T)
  let b6 := bank (Counter.marked xs) (Counter.marked ys) a (a+e) (markedRuler R) (markedRuler T)
  let p2 := positions pos xs.length ys.length R T
  let p3 := positions pos xs.length 0 R T
  let p4 := positions pos 0 0 R T
  let p5 := positions pos 0 0 0 T
  obtain ⟨t0,h0,tr0⟩ : ∃ t≤2,Trace expand t (cfg start b0 pos) (cfg (.init .done) b1 pos) := by
    simpa [start,b0,b1,bank] using NativeTapeCalls.initialize_call (program expand) 1 Label.init
      (init_code expand) b0 pos rfl
  have j0 := jump expand (.init .done) .checkRows b1 pos rfl
  obtain ⟨t1,h1,tr1⟩ : ∃ t≤22*(T*(a+e))+2,Trace expand t
      (cfg .checkRows b1 pos) (cfg (.seal .seal) b2 p2) := scan_trace expand a e hb rows extras hr he pos
  obtain ⟨t2,h2,tr2⟩ : ∃ t≤2*ys.length+5,Trace expand t
      (cfg (.seal .seal) b2 p2) (cfg (.seal .done) b3 p3) := by
    simpa [b2,b3,p2,p3,bank,positions] using NativeTapeCalls.seal_call (program expand) 1 Label.seal
      (seal_code expand) b2 p2 ys rfl
  have j2 := jump expand (.seal .done) (.rewind 0 .back) b3 p3 rfl
  obtain ⟨t3,h3,tr3⟩ : ∃ t≤2*xs.length+4,Trace expand t
      (cfg (.rewind 0 .back) b3 p3) (cfg (.rewind 0 .done) b4 p4) := by
    simpa [b3,b4,p3,p4,bank,positions] using NativeTapeCalls.rewind (program expand) 0 (Label.rewind 0)
      (rewind_code expand 0) b3 p3 xs rfl
  have j3 := jump expand (.rewind 0 .done) (.rewind 4 .back) b4 p4 rfl
  obtain ⟨t4,h4,tr4⟩ : ∃ t≤2*R+4,Trace expand t
      (cfg (.rewind 4 .back) b4 p4) (cfg (.rewind 4 .done) b5 p5) := by
    have heq : endRuler R=⟨(symbols (List.replicate R false)).reverse++[.start],[.stop]⟩ := by
      simp [endRuler,NativeResizeScan.unary,symbols,List.map_replicate]
    simpa [b4,b5,p4,p5,bank,positions,markedRuler] using NativeTapeCalls.rewind (program expand) 4 (Label.rewind 4)
      (rewind_code expand 4) b4 p4 (List.replicate R false) (by simp [b4,bank,heq])
  have j4 := jump expand (.rewind 4 .done) (.rewind 5 .back) b5 p5 rfl
  obtain ⟨t5,h5,tr5⟩ : ∃ t≤2*T+4,Trace expand t
      (cfg (.rewind 5 .back) b5 p5) (cfg (.rewind 5 .done) b6 pos) := by
    have heq : endRuler T=⟨(symbols (List.replicate T false)).reverse++[.start],[.stop]⟩ := by
      simp [endRuler,NativeResizeScan.unary,symbols,List.map_replicate]
    simpa [b5,b6,p5,bank,positions,markedRuler] using NativeTapeCalls.rewind (program expand) 5 (Label.rewind 5)
      (rewind_code expand 5) b5 p5 (List.replicate T false) (by simp [b5,bank,heq])
  have j5 := jump expand (.rewind 5 .done) .done b6 pos rfl
  have s0 := trace_trans tr0 j0
  have s2 := trace_trans tr2 j2
  have s3 := trace_trans tr3 j3
  have s4 := trace_trans tr4 j4
  have s5 := trace_trans tr5 j5
  have acc1 := trace_trans s0 tr1
  have acc2 := trace_trans acc1 s2
  have acc3 := trace_trans acc2 s3
  have acc4 := trace_trans acc3 s4
  have acc5 := trace_trans acc4 s5
  obtain ⟨hin,hout⟩ := square_lengths_le expand a e rows extras hr he
  have hT : T≤T*(a+e) := by exact Nat.le_mul_of_pos_right T hb
  have hR : R≤T := by dsimp [R,T]; omega
  refine ⟨_,?_,acc5⟩
  change xs.length ≤ T*(a+e) at hin
  change ys.length ≤ T*(a+e) at hout
  change _ ≤ 40*(T*(a+e))+40
  omega

end BitWord.NativeSquare
