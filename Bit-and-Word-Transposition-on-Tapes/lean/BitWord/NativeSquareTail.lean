import BitWord.NativeSquareRows

namespace BitWord.NativeSquare
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop
open NativeResizeScan (unary markedRuler endRuler inputRecord outputRecord inputRows outputRows consumed tailOutput)

def tailInputs (expand : Bool) (rows : List (List Bool)) : List Bool :=
  rows.flatMap (consumed expand)
def tailOutputs (expand : Bool) (rows : List (List Bool)) : List Bool :=
  rows.flatMap (tailOutput expand)

theorem tailInput_eq (expand : Bool) (xs : List Bool) (sr : List (Sym Bool)) :
    NativeResizeScan.tailInput expand xs sr = symbols (consumed expand xs)++sr := by
  cases expand <;> simp [NativeResizeScan.tailInput,consumed,symbols]

theorem tails_trace (expand : Bool) (a b : ℕ) (rows : List (List Bool))
    (hlen : ∀ r ∈ rows,r.length=b) (passedShort passedLong : ℕ)
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ rows.length*(5*b+14)+1,Trace expand t
      (cfg .checkTail (bank ⟨sl,symbols (tailInputs expand rows)++sr⟩
        (NativeSealBack.openWord pre) a b
        (cursor 0 passedShort) (cursor rows.length passedLong)) pos)
      (cfg (.seal .seal) (bank ⟨(symbols (tailInputs expand rows)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++tailOutputs expand rows)) a b
        (cursor 0 passedShort) (cursor 0 (passedLong+rows.length)))
        (positions pos (tailInputs expand rows).length (tailOutputs expand rows).length 0 rows.length)) := by
  induction rows generalizing sl pre pos passedLong with
  | nil =>
    simpa [tailInputs,tailOutputs,symbols] using
      NativeZipper.trace_of_run (program expand)
        (tail_stop expand ⟨sl,sr⟩ (NativeSealBack.openWord pre) a b passedShort passedLong pos)
  | cons r rows ih =>
    have hr := hlen r (by simp)
    have htail : ∀ r ∈ rows,r.length=b := by intro r h; exact hlen r (by simp [h])
    let srcTail := symbols (tailInputs expand rows)++sr
    let src := (⟨sl,NativeResizeScan.tailInput expand r srcTail⟩ : Tape Bool)
    let sout := NativeSealBack.openWord pre
    let short := cursor 0 passedShort
    let long := cursor (rows.length+1) passedLong
    obtain ⟨t0,h0,tr0⟩ := NativeZipper.trace_of_run (program expand)
      (tail_check expand src sout a b rows.length passedShort passedLong pos)
    obtain ⟨t1,h1,tr1⟩ := padding_call expand a r sl srcTail pre short long pos
    let nextLeft := (symbols (consumed expand r)).reverse++sl
    let nextPre := pre++tailOutput expand r
    let scanPos := positions pos (consumed expand r).length (tailOutput expand r).length 0 0
    obtain ⟨t2,h2,tr2⟩ := NativeZipper.trace_of_run (program expand)
      (tail_advance expand ⟨nextLeft,srcTail⟩ (NativeSealBack.openWord nextPre)
        a b rows.length passedShort passedLong scanPos)
    let nextPos := positions scanPos 0 0 0 1
    obtain ⟨t3,h3,tr3⟩ := ih htail (passedLong+1) nextLeft nextPre nextPos
    simp only [zcfg_denote] at tr0 tr2
    have tr01 := trace_trans tr0 (by simpa only [hr] using tr1)
    have tr012 := trace_trans tr01 tr2
    have tr3' : Trace expand t3
        (cfg .checkTail (bank ⟨nextLeft,srcTail⟩ (NativeSealBack.openWord nextPre)
          a b (cursor 0 passedShort) (cursor rows.length (passedLong+1))) nextPos)
        (cfg (.seal .seal) (bank ⟨(symbols (tailInputs expand (r::rows))).reverse++sl,sr⟩
          (NativeSealBack.openWord (pre++tailOutputs expand (r::rows))) a b
          (cursor 0 passedShort) (cursor 0 (passedLong+(r::rows).length)))
          (positions pos (tailInputs expand (r::rows)).length (tailOutputs expand (r::rows)).length
            0 (r::rows).length)) := by
      simpa [tailInputs,tailOutputs,List.flatMap_cons,symbols,List.map_append,
        List.reverse_append,List.append_assoc,nextLeft,nextPre,nextPos,scanPos,srcTail,
        positions_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tr3
    have tr := trace_trans tr012 tr3'
    refine ⟨t0+t1+t2+t3,?_,?_⟩
    · simp only [hr] at h1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa [tailInputs,List.flatMap_cons,symbols,List.map_append,List.append_assoc,
        src,srcTail,sout,short,long,tailInput_eq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tr

end BitWord.NativeSquare
