import FixedTapeCompiler.MicroErase
import FixedTapeCompiler.Counter

namespace FixedTapeCompiler.Microcode.EraseFamily
open CopyMachine (Sym Tape)
abbrev Label := Fin 8
def instruction {T L : Type*} [DecidableEq T] (s : T) (label : Label → L) : Label → Instruction T L
  | ⟨0,_⟩ => .halt
  | ⟨1,_⟩ => .reject
  | ⟨2,_⟩ => .read s (fun a => match a with
      | .data _ => label 3 | .stop => label 4 | _ => label 1)
  | ⟨3,_⟩ => .act (single s ⟨none,.right⟩) (label 2)
  | ⟨4,_⟩ => .act (single s ⟨some .blank,.left⟩) (label 5)
  | ⟨5,_⟩ => .read s (fun a => match a with
      | .start => label 7 | .data _ => label 6 | _ => label 1)
  | ⟨6,_⟩ => .act (single s ⟨some .blank,.left⟩) (label 5)
  | ⟨7,_⟩ => .act (single s ⟨some .blank,.right⟩) (label 0)

def assemble {T L : Type*} [DecidableEq T] (p : Program T L) (s : T) (label : Label → L)
    (hc : ∀ pc,pc≠0 → p (label pc)=instruction s label pc) : Erase p s (label 2) (label 0) where
  forward := label 3
  tailEntry := label 4
  reject := label 1
  read_code := hc 2 (by decide)
  forward_code := hc 3 (by decide)
  tailCode := ⟨label 5,label 6,label 7,label 1,
    hc 4 (by decide),hc 5 (by decide),hc 6 (by decide),hc 7 (by decide)⟩

def program : Program (Fin 1) Label := instruction 0 id
def fragment : Erase program 0 2 0 := assemble program 0 id (by intro _ _; rfl)
theorem all_inputs (xs : List Bool) (bank : Fin 1 → Tape Bool) (hs : bank 0=Counter.marked xs) :
    actualRun program (4*xs.length+4) (⟨2,bank⟩ : Config (Fin 1) Label).denote=
      (⟨0,Function.update bank 0 ⟨[],[]⟩⟩ : Config (Fin 1) Label).denote := by
  have h := fragment.actual_to_blank xs bank
  change actualRun program (4*xs.length+4)
    (focus 2 0 (Counter.marked xs) bank).denote =
    (focus 0 0 (⟨[],[]⟩ : Tape Bool) bank).denote at h
  simpa only [focus, ← hs, Function.update_eq_self] using h
theorem fixed_resources : Fintype.card (Fin 1)=1 ∧ Fintype.card (Sym Bool)=5 ∧ Fintype.card Label=8 := by decide
end FixedTapeCompiler.Microcode.EraseFamily
