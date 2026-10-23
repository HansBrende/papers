import BitWord.NativeResizeRecord

namespace BitWord.NativeResizeScan
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeCountedLoop

def inputRows (expand : Bool) (rows : List (List Bool × List Bool)) : List Bool :=
  rows.flatMap (fun r => inputRecord expand r.1 r.2)
def outputRows (expand : Bool) (rows : List (List Bool × List Bool)) : List Bool :=
  rows.flatMap (fun r => outputRecord expand r.1 r.2)

theorem begin_run (expand : Bool) (xs extra : List Bool) (hne : xs ≠ [])
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 1 (startRecord .begin expand xs extra sl sr pre pos)=
      startRecord .copy expand xs extra sl sr pre pos := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
      program,programCore,startRecord,inputRecord,cfg,symbols,Tape.read]

theorem rows_end_run (expand : Bool) (a e : ℕ) (sl : List (Sym Bool))
    (pre : List Bool) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 1
      (cfg .begin ⟨sl,[.stop]⟩ (NativeSealBack.openWord pre)
        (markedRuler a) (markedRuler (a+e)) pos)=
      cfg .done ⟨sl,[.stop]⟩ (NativeSealBack.openWord pre)
        (markedRuler a) (markedRuler (a+e)) pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,programCore,cfg,Tape.read]

/-- The same fixed loop handles arbitrarily many records. Rulers are ordinary
marked tapes; their movement and return are charged on every iteration. -/
theorem rows_trace (expand : Bool) (a e : ℕ) (ha : 0<a)
    (rows : List (List Bool × List Bool))
    (hlen : ∀ r ∈ rows, r.1.length=a ∧ r.2.length=e)
    (sl : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ rows.length*(7*(a+e)+13)+1,Trace expand t
      (cfg .begin ⟨sl,symbols (inputRows expand rows)++[.stop]⟩ (NativeSealBack.openWord pre)
        (markedRuler a) (markedRuler (a+e)) pos).denote
      (cfg .done ⟨(symbols (inputRows expand rows)).reverse++sl,[.stop]⟩
        (NativeSealBack.openWord (pre++outputRows expand rows))
        (markedRuler a) (markedRuler (a+e))
        (positions pos (inputRows expand rows).length (outputRows expand rows).length 0 0)).denote := by
  induction rows generalizing sl pre pos with
  | nil =>
    simpa [inputRows,outputRows,symbols] using
      NativeZipper.trace_of_run (program expand) (rows_end_run expand a e sl pre pos)
  | cons r rows ih =>
    obtain ⟨hr,he⟩ := hlen r (by simp)
    have hne : r.1≠[] := by intro h; simp [h] at hr; omega
    have htail : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e := by
      intro r h; exact hlen r (by simp [h])
    let srcTail := symbols (inputRows expand rows)++[.stop]
    obtain ⟨t0,h0,tr0⟩ := NativeZipper.trace_of_run (program expand)
      (begin_run expand r.1 r.2 hne sl srcTail pre pos)
    obtain ⟨t1,h1,tr1⟩ := record_trace expand r.1 r.2 sl srcTail pre pos
    let nextLeft := (symbols (inputRecord expand r.1 r.2)).reverse++sl
    let nextPre := pre++outputRecord expand r.1 r.2
    let nextPos := positions pos (inputRecord expand r.1 r.2).length (outputRecord expand r.1 r.2).length 0 0
    obtain ⟨t2,h2,tr2⟩ := ih htail nextLeft nextPre nextPos
    have tr2' : Trace expand t2
        (endRecord .begin expand r.1 r.2 sl srcTail pre pos).denote
        (cfg .done ⟨(symbols (inputRows expand (r::rows))).reverse++sl,[.stop]⟩
          (NativeSealBack.openWord (pre++outputRows expand (r::rows)))
          (markedRuler a) (markedRuler (a+e))
          (positions pos (inputRows expand (r::rows)).length (outputRows expand (r::rows)).length 0 0)).denote := by
      simpa [endRecord,inputRows,outputRows,List.flatMap_cons,symbols,List.map_append,
        List.reverse_append,List.append_assoc,nextLeft,nextPre,nextPos,srcTail,
        positions_add,hr,he] using tr2
    have tr01 := trace_trans tr0 tr1
    have tr := trace_trans tr01 tr2'
    refine ⟨t0+t1+t2,?_,?_⟩
    · simp only [hr,he] at h1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa [startRecord,inputRows,List.flatMap_cons,symbols,List.map_append,List.append_assoc,
        srcTail,hr,he] using tr

/-- Input and output sizes are bounded by the full ruler width per record. -/
theorem rows_lengths_le (expand : Bool) (a e : ℕ) (rows : List (List Bool × List Bool))
    (hlen : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e) :
    (inputRows expand rows).length ≤ rows.length*(a+e) ∧
    (outputRows expand rows).length ≤ rows.length*(a+e) := by
  induction rows with
  | nil => simp [inputRows,outputRows]
  | cons r rows ih =>
    obtain ⟨hr,he⟩ := hlen r (by simp)
    have ht : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e := by intro r h; exact hlen r (by simp [h])
    obtain ⟨hi,ho⟩ := ih ht
    cases expand <;> simp_all [inputRows,outputRows,inputRecord,outputRecord,consumed,tailOutput,Nat.add_mul] <;> omega

theorem rows_linear_budget (a e n : ℕ) (ha : 0<a) :
    n*(7*(a+e)+13)+1 ≤ 20*(n*(a+e))+1 := by
  have hb : 1≤a+e := by omega
  have hs : 7*(a+e)+13≤20*(a+e) := by omega
  have hh := Nat.mul_le_mul_left n hs
  nlinarith

end BitWord.NativeResizeScan
