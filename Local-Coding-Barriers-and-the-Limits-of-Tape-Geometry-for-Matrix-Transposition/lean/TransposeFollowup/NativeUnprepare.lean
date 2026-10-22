import TransposeFollowup.NativeErase

/-! Remove a lone START marker from a prepared scratch tape. Two physical
transitions suffice, with the original absolute head position restored. -/
namespace TransposeFollowup.NativeUnprepare
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

abbrev Label := Fin 3

def program : Microcode.Program (Fin 1) Label
  | 0 => .act (Microcode.single 0 ⟨none,.left⟩) 1
  | 1 => .act (Microcode.single 0 ⟨some .blank,.right⟩) 2
  | _ => .halt

def cfg (pc : Label) (w : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => w⟩,pos⟩

def cleared : Tape Bool := ⟨[.blank],[]⟩

theorem unprepare_run (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg 0 BinaryCarry.preparedOutput pos)=cfg 2 cleared pos := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,
    cfg,BinaryCarry.preparedOutput,Microcode.single,Microcode.Action.apply,
    NativeMicrocode.direction,Transpose.Dir.shift]
  congr 2
  · funext t; fin_cases t; rfl
  · funext t; fin_cases t; simp

theorem cleared_denote : cleared.denote=(⟨[],[]⟩ : Tape Bool).denote := by
  simp [cleared,Tape.denote,Turing.Tape.mk₂]
  exact congrArg (fun a => Turing.Tape.mk' a (Turing.ListBlank.mk [])) (EraseStream.blanks_eq_nil 1)

theorem complete_trace (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2, OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
      (cfg 0 BinaryCarry.preparedOutput pos).denote (cfg 2 ⟨[],[]⟩ pos).denote := by
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run program (unprepare_run pos)
  have he : (cfg 2 cleared pos).denote=(cfg 2 ⟨[],[]⟩ pos).denote := by
    unfold NativeZipper.Config.denote Microcode.Config.denote cfg
    simp only [cleared_denote]
  exact ⟨t,ht,by simpa only [he] using htr⟩

end TransposeFollowup.NativeUnprepare
