import FixedTapeCompiler.Microcode

/-! Callback-safe rewind fragments of the actual affine microcode. The
hypotheses describe finite instruction entries, not an assumed fast call.
The caller's other tapes and cells before the local START are preserved. -/
namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)
variable {T L : Type*} [DecidableEq T]

structure Rewind (p : Program T L) (t : T) (entry exit : L) where
  back : L
  finish : L
  reject : L
  read_code : p entry = .read t (fun s => match s with
    | .start => finish | .stop | .data _ => back | .blank => reject)
  back_code : p back = .act (single t ⟨none,.left⟩) entry
  finish_code : p finish = .act (single t ⟨none,.right⟩) exit

def DataOrStop (s : Sym Bool) : Prop := s = .stop ∨ ∃ b, s = .data b

theorem Rewind.advance {p : Program T L} {t : T} {entry exit : L}
    (h : Rewind p t entry exit) (word : Tape Bool) (bank : T → Tape Bool)
    (hw : DataOrStop word.read) :
    run p 2 (focus entry t word bank) = focus entry t word.moveLeft bank := by
  change step p (step p (focus entry t word bank)) = _
  rw [at_read _ _ _ _ h.read_code]
  rcases hw with hw | ⟨b,hw⟩
  · rw [hw]
    exact at_act _ _ _ _ _ h.back_code _ _
  · rw [hw]
    exact at_act _ _ _ _ _ h.back_code _ _

theorem Rewind.finish_at {p : Program T L} {t : T} {entry exit : L}
    (h : Rewind p t entry exit) (word : Tape Bool) (bank : T → Tape Bool)
    (hw : word.read = .start) :
    run p 2 (focus entry t word bank) = focus exit t word.moveRight bank := by
  change step p (step p (focus entry t word bank)) = _
  rw [at_read _ _ _ _ h.read_code,hw]
  exact at_act _ _ _ _ _ h.finish_code _ _

theorem Rewind.exact {p : Program T L} {t : T} {entry exit : L}
    (h : Rewind p t entry exit) (pre : List Bool) (cur : Sym Bool)
    (rest ancestor : List (Sym Bool)) (bank : T → Tape Bool) (hc : DataOrStop cur) :
    run p (2*pre.length+4)
      (focus entry t ⟨symbols pre++(.start::ancestor),cur::rest⟩ bank) =
      focus exit t ⟨.start::ancestor,symbols pre.reverse++(cur::rest)⟩ bank := by
  induction pre generalizing cur rest with
  | nil =>
    rw [show 2*([].length)+4 = 2+2 by rfl,run_add,
      h.advance _ _ (by simpa [Tape.read] using hc)]
    simpa [symbols,Tape.moveLeft,Tape.moveRight,Tape.read] using
      h.finish_at (⟨ancestor,.start::cur::rest⟩ : Tape Bool) bank rfl
  | cons b pre ih =>
    rw [show 2*(b::pre).length+4 = 2+(2*pre.length+4) by simp; omega,run_add,
      h.advance _ _ (by simpa [Tape.read] using hc)]
    simpa [symbols,Tape.moveLeft,List.reverse_cons,List.map_append,List.append_assoc]
      using ih (.data b) (cur::rest) (Or.inr ⟨b,rfl⟩)

theorem Rewind.from_end {p : Program T L} {t : T} {entry exit : L}
    (h : Rewind p t entry exit) (xs : List Bool) (ancestor : List (Sym Bool))
    (bank : T → Tape Bool) :
    run p (2*xs.length+4)
      (focus entry t ⟨(symbols xs).reverse++(.start::ancestor),[.stop]⟩ bank) =
      focus exit t ⟨.start::ancestor,symbols xs++[.stop]⟩ bank := by
  simpa [symbols,List.map_reverse] using
    h.exact xs.reverse .stop [] ancestor bank (Or.inl rfl)

theorem Rewind.actual_from_end {p : Program T L} {t : T} {entry exit : L}
    (h : Rewind p t entry exit) (xs : List Bool) (ancestor : List (Sym Bool))
    (bank : T → Tape Bool) :
    actualRun p (2*xs.length+4)
      (focus entry t ⟨(symbols xs).reverse++(.start::ancestor),[.stop]⟩ bank).denote =
      (focus exit t ⟨.start::ancestor,symbols xs++[.stop]⟩ bank).denote := by
  rw [← run_refines,h.from_end]

theorem Rewind.after_left {p : Program T L} {t : T} {entry exit : L}
    (h : Rewind p t entry exit) (pre : List Bool) (suffix ancestor : List (Sym Bool))
    (bank : T → Tape Bool) :
    run p (2*pre.length+2)
      (focus entry t (⟨symbols pre++(.start::ancestor),suffix⟩ : Tape Bool).moveLeft bank) =
      focus exit t ⟨.start::ancestor,symbols pre.reverse++suffix⟩ bank := by
  cases pre with
  | nil =>
    simpa [symbols,Tape.moveLeft,Tape.moveRight,Tape.read] using
      h.finish_at (⟨ancestor,.start::suffix⟩ : Tape Bool) bank rfl
  | cons b pre =>
    simpa [symbols,Tape.moveLeft,List.reverse_cons,List.map_append,List.append_assoc,
      Nat.mul_add,Nat.add_assoc] using
      h.exact pre (.data b) suffix ancestor bank (Or.inr ⟨b,rfl⟩)

structure NewStream (p : Program T L) (t : T) (entry exit : L) where
  mark : L
  left_code : p entry = .act (single t ⟨none,.left⟩) mark
  mark_code : p mark = .act (single t ⟨some .start,.right⟩) exit

theorem NewStream.exact {p : Program T L} {t : T} {entry exit : L}
    (h : NewStream p t entry exit) (bank : T → Tape Bool) :
    run p 2 (focus entry t ⟨[],[]⟩ bank) = focus exit t ⟨[.start],[]⟩ bank := by
  change step p (step p (focus entry t ⟨[],[]⟩ bank)) = _
  rw [at_act _ _ _ _ _ h.left_code,at_act _ _ _ _ _ h.mark_code]
  rfl

end FixedTapeCompiler.Microcode
