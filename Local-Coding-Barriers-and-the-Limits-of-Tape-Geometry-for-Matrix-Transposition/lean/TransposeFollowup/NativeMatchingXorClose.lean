import TransposeFollowup.MatchingXorMasksSemantics

/-! Seal and rewind equal-length mask banks synchronously. One fixed page
port supplies the stopping marker; the other tapes move in lockstep. -/
namespace TransposeFollowup.NativeMatchingXorClose
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
inductive Label | seal | back | read | restore | done | reject deriving DecidableEq
instance : Fintype Label where
  elems := {.seal,.back,.read,.restore,.done,.reject}
  complete := by intro pc;cases pc <;> simp

def program (pivot : Fin q) : Microcode.Program (Fin q) Label
  | .seal => .act (fun _ => ⟨some .stop,.stay⟩) .back
  | .back => .act (fun _ => ⟨none,.left⟩) .read
  | .read => .read pivot (fun s => match s with
      | .data _ => .back | .start => .restore | _ => .reject)
  | .restore => .act (fun _ => ⟨none,.right⟩) .done
  | .done => .halt | .reject => .reject

def cfg (pc : Label) (s : Fin q → Tape Bool) (pos : Fin q → ℤ) : NativeZipper.Config (Fin q) Label := ⟨⟨pc,s⟩,pos⟩

theorem back_step (pivot : Fin q) (bits : Fin q → Bool)
    (ls rs : Fin q → List (Sym Bool)) (pos : Fin q → ℤ) :
    NativeZipper.run (program pivot) 2 (cfg .back (fun j => ⟨.data (bits j)::ls j,rs j⟩) pos)=
      cfg .back (fun j => ⟨ls j,.data (bits j)::rs j⟩) (fun j => pos j-1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem start_step (pivot : Fin q) (ls rs : Fin q → List (Sym Bool)) (pos : Fin q → ℤ) :
    NativeZipper.run (program pivot) 3 (cfg .back (fun j => ⟨.start::ls j,rs j⟩) pos)=
      cfg .done (fun j => ⟨.start::ls j,rs j⟩) pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem back_run (pivot : Fin q) (rows : List (Fin q → Bool))
    (ls rs : Fin q → List (Sym Bool)) (pos : Fin q → ℤ) :
    NativeZipper.run (program pivot) (2*rows.length+3)
      (cfg .back (fun j => ⟨symbols (rows.map (fun f => f j))++.start::ls j,rs j⟩) pos)=
      cfg .done (fun j => ⟨.start::ls j,(symbols (rows.map (fun f => f j))).reverse++rs j⟩)
        (fun j => pos j-rows.length) := by
  induction rows generalizing rs pos with
  | nil => simpa [symbols] using start_step pivot ls rs pos
  | cons bits rows ih =>
    rw [show 2*(bits::rows).length+3=2+(2*rows.length+3) by simp;omega,NativeZipper.run_add]
    simp only [List.map_cons,symbols,List.cons_append]
    rw [back_step]
    have ht := ih (fun j => .data (bits j)::rs j) (fun j => pos j-1)
    simpa only [List.map_cons,symbols,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,
      List.length_cons,Nat.cast_add,Nat.cast_one,sub_sub,add_comm] using ht

theorem complete_run (pivot : Fin q) (rows : List (Fin q → Bool)) (pos : Fin q → ℤ) :
    NativeZipper.run (program pivot) (2*rows.length+4)
      (cfg .seal (fun j => NativeSealBack.openWord (rows.map (fun f => f j))) pos)=
      cfg .done (fun j => Counter.marked (rows.map (fun f => f j))) (fun j => pos j-rows.length) := by
  rw [show 2*rows.length+4=1+(2*rows.length+3) by omega,NativeZipper.run_add]
  have hs : NativeZipper.run (program pivot) 1
      (cfg .seal (fun j => NativeSealBack.openWord (rows.map (fun f => f j))) pos)=
      cfg .back (fun j => ⟨(symbols (rows.map (fun f => f j))).reverse++[.start],[.stop]⟩) pos := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
      Microcode.Action.apply,NativeSealBack.openWord,Tape.write,NativeMicrocode.direction,Transpose.Dir.shift]
  rw [hs]
  have ht := back_run pivot rows.reverse (fun _ => []) (fun _ => [.stop]) pos
  simpa [List.map_reverse,Counter.marked,symbols] using ht

abbrev Trace (pivot : Fin q) := OperationalTrace.Trace (NativeMicrocode.step (program pivot))
  (NativeMicrocode.Active (program pivot))

theorem complete_trace (pivot : Fin q) (rows : List (Fin q → Bool)) (pos : Fin q → ℤ) :
    ∃ t ≤ 2*rows.length+4, Trace pivot t
      (cfg .seal (fun j => NativeSealBack.openWord (rows.map (fun f => f j))) pos).denote
      (cfg .done (fun j => Counter.marked (rows.map (fun f => f j)))
        (fun j => pos j-rows.length)).denote :=
  NativeZipper.trace_of_run (program pivot) (complete_run pivot rows pos)

end TransposeFollowup.NativeMatchingXorClose
