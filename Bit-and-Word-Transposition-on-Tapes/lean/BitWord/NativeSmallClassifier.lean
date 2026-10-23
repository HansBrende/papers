import TransposeFollowup.NativeSealBack

/-! Inspect at most 32 data cells, retain the bounded count in finite control,
and physically restore the marked input word and head. -/
namespace BitWord.NativeSmallClassifier
open FixedTapeCompiler CopyMachine TransposeFollowup

inductive Label
  | scan (i : Fin 33) | advance (i : Fin 32)
  | rewind (answer left : Fin 33) | done (answer : Fin 33) | reject
  deriving DecidableEq, Fintype

def program : Microcode.Program (Fin 1) Label
  | .scan i => if hi : i.val < 32 then .read 0 (fun s => match s with
      | .data _ => .advance ⟨i.val,hi⟩ | .stop => .rewind i i | _ => .reject)
    else .jump (.rewind i i)
  | .advance i => .act (fun _ => ⟨none,.right⟩) (.scan ⟨i.val+1,by have:=i.isLt; omega⟩)
  | .rewind a i => if hi : 0 < i.val then
      .act (fun _ => ⟨none,.left⟩) (.rewind a ⟨i.val-1,by have:=i.isLt; omega⟩)
    else .jump (.done a)
  | .done _ => .halt
  | .reject => .reject

def cfg (pc : Label) (tape : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => tape⟩,pos⟩

theorem scan_bit (i : ℕ) (hi : i < 32) (b : Bool) (sl sr : List (Sym Bool))
    (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg (.scan ⟨i,by omega⟩) ⟨sl,.data b::sr⟩ pos)=
      cfg (.scan ⟨i+1,by omega⟩) ⟨.data b::sl,sr⟩ (fun p => pos p+1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,hi,cfg,
    Tape.read,Microcode.Action.apply,Tape.moveRight,
    NativeMicrocode.direction,Transpose.Dir.shift]

theorem scan_stop (i : ℕ) (hi : i ≤ 32) (tail : List Bool)
    (hend : i=32 ∨ tail=[]) (sl : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 1 (cfg (.scan ⟨i,by omega⟩) ⟨sl,symbols tail++[.stop]⟩ pos)=
      cfg (.rewind ⟨i,by omega⟩ ⟨i,by omega⟩) ⟨sl,symbols tail++[.stop]⟩ pos := by
  rcases hend with rfl | rfl
  · simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg]
  · by_cases hh : i < 32 <;>
      simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,hh,symbols,Tape.read]

theorem scan_prefix (xs tail : List Bool) (i : ℕ) (hi : i+xs.length ≤ 32)
    (hend : i+xs.length=32 ∨ tail=[]) (sl : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*xs.length+1)
      (cfg (.scan ⟨i,by omega⟩) ⟨sl,symbols (xs++tail)++[.stop]⟩ pos)=
      cfg (.rewind ⟨i+xs.length,by omega⟩ ⟨i+xs.length,by omega⟩)
        ⟨(symbols xs).reverse++sl,symbols tail++[.stop]⟩ (fun p => pos p+xs.length) := by
  induction xs generalizing i sl pos with
  | nil => simpa [symbols] using scan_stop i (by simpa using hi) tail (by simpa using hend) sl pos
  | cons b xs ih =>
    have hnext : i+1+xs.length ≤ 32 := by simpa [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi
    have hnend : i+1+xs.length=32 ∨ tail=[] := by simpa [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hend
    have hb := scan_bit i (by simp only [List.length_cons] at hi; omega) b sl
      (symbols (xs++tail)++[.stop]) pos
    have hn := ih (i+1) hnext hnend (.data b::sl) (fun p => pos p+1)
    have hc := congrArg (NativeZipper.run program (2*xs.length+1)) hb
    have hrun := hc.trans hn
    conv_lhs => arg 2; rw [show 2*(b::xs).length+1=2+(2*xs.length+1) by simp; omega]
    rw [NativeZipper.run_add]
    exact hrun.trans (by
      simp only [List.length_cons, symbols, List.map_cons, List.reverse_cons,
        List.cons_append, List.append_assoc]
      congr 1
      · congr 1 <;> congr 1 <;> omega
      · funext p; omega)

theorem rewind_step (a : Fin 33) (xs : List Bool) (b : Bool) (hx : xs.length < 32)
    (sr : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 1
      (cfg (.rewind a ⟨xs.length+1,by omega⟩) ⟨symbols (b::xs)++[.start],sr⟩ pos)=
      cfg (.rewind a ⟨xs.length,by omega⟩) ⟨symbols xs++[.start],.data b::sr⟩ (fun p => pos p-1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,symbols,
    NativeMicrocode.direction,Transpose.Dir.shift]

theorem rewind_run (a : Fin 33) (xs : List Bool) (hx : xs.length ≤ 32)
    (sr : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (xs.length+1)
      (cfg (.rewind a ⟨xs.length,by omega⟩) ⟨symbols xs++[.start],sr⟩ pos)=
      cfg (.done a) ⟨[.start],symbols xs.reverse++sr⟩ (fun p => pos p-xs.length) := by
  induction xs generalizing sr pos with
  | nil => simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,symbols]
  | cons b xs ih =>
    conv_lhs => arg 2; rw [show (b::xs).length+1=1+(xs.length+1) by simp; omega]
    rw [NativeZipper.run_add]
    change NativeZipper.run program (xs.length+1)
      (NativeZipper.run program 1 (cfg (.rewind a ⟨xs.length+1,by simp only[List.length_cons] at hx; omega⟩)
        ⟨symbols (b::xs)++[.start],sr⟩ pos))=_
    rw [rewind_step a xs b (by simp only[List.length_cons] at hx; omega),ih (by simp only[List.length_cons] at hx; omega)]
    simp [symbols,List.reverse_cons,List.map_append,List.append_assoc]
    congr 1
    funext p; omega

def answer (xs : List Bool) : Fin 33 := ⟨min xs.length 32,by omega⟩

 theorem complete_run (xs : List Bool) (pos : Fin 1 → ℤ) :
     NativeZipper.run program (3*(min xs.length 32)+2)
       (cfg (.scan 0) (Counter.marked xs) pos)=cfg (.done (answer xs)) (Counter.marked xs) pos := by
   let pre := xs.take 32
   let tail := xs.drop 32
   have hp : pre.length=min xs.length 32 := by simp [pre,Nat.min_comm]
   have he : pre++tail=xs := List.take_append_drop _ _
   have hend : pre.length=32 ∨ tail=[] := by
     by_cases hh : 32 ≤ xs.length
     · left; simp [pre,Nat.min_eq_left hh]
     · right; exact List.drop_eq_nil_of_le (by omega)
   have hs := scan_prefix pre tail 0 (by omega) (by simpa using hend) [.start] pos
   have hr := rewind_run (answer xs) pre.reverse (by simpa using (show pre.length ≤ 32 by omega))
     (symbols tail++[.stop]) (fun p => pos p+pre.length)
   rw [show 3*(min xs.length 32)+2=(2*pre.length+1)+(pre.length+1) by omega,NativeZipper.run_add]
   have hs' : NativeZipper.run program (2*pre.length+1)
       (cfg (.scan 0) (Counter.marked xs) pos)=
       cfg (.rewind (answer xs) ⟨pre.length,by omega⟩)
         ⟨symbols pre.reverse++[.start],symbols tail++[.stop]⟩ (fun p => pos p+pre.length) := by
     simpa [Counter.marked,he,answer,hp,symbols,List.map_reverse] using hs
   rw [hs']
   simpa [Counter.marked,he,symbols,List.map_append,List.length_reverse,List.reverse_reverse,
     ← List.map_append,← List.append_assoc] using hr

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem complete_trace (xs : List Bool) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 98, Trace t (cfg (.scan 0) (Counter.marked xs) pos).denote
      (cfg (.done (answer xs)) (Counter.marked xs) pos).denote := by
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run program (complete_run xs pos)
  exact ⟨t,by omega,htr⟩

end BitWord.NativeSmallClassifier
