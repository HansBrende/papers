import FixedTapeCompiler.MicroCounter

namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape)

theorem Decrement.actual_on_bank {T L : Type*} [DecidableEq T] {p : Program T L}
    {t : T} {entry success underflow : L} (h : Decrement p t entry success underflow)
    (xs : List Bool) (bank : T → Tape Bool) (ht : bank t=Counter.marked xs) :
    actualRun p (2*Counter.stepCost xs) (⟨entry,bank⟩ : Config T L).denote=
      (⟨if Counter.isZero xs then underflow else success,
        Function.update bank t (Counter.marked (Counter.decrement xs))⟩ : Config T L).denote := by
  have he := h.actual_exact xs bank
  simpa only [focus,← ht,Function.update_eq_self] using he

namespace DecrementFamily
abbrev Label := Fin 13

def instruction {T L : Type*} [DecidableEq T] (t : T) (label : Label → L) : Label → Instruction T L
  | ⟨0,_⟩ => .read t (fun a => match a with
      | .data false => label 1 | .data true => label 2 | .stop => label 3 | _ => label 10)
  | ⟨1,_⟩ => .act (single t ⟨some (.data true),.right⟩) (label 0)
  | ⟨2,_⟩ => .act (single t ⟨some (.data false),.left⟩) (label 4)
  | ⟨3,_⟩ => .act (single t ⟨none,.left⟩) (label 7)
  | ⟨4,_⟩ => .read t (fun a => match a with
      | .start => label 6 | .stop | .data _ => label 5 | .blank => label 10)
  | ⟨5,_⟩ => .act (single t ⟨none,.left⟩) (label 4)
  | ⟨6,_⟩ => .act (single t ⟨none,.right⟩) (label 11)
  | ⟨7,_⟩ => .read t (fun a => match a with
      | .start => label 9 | .stop | .data _ => label 8 | .blank => label 10)
  | ⟨8,_⟩ => .act (single t ⟨none,.left⟩) (label 7)
  | ⟨9,_⟩ => .act (single t ⟨none,.right⟩) (label 12)
  | ⟨10,_⟩ => .reject
  | ⟨11,_⟩ | ⟨12,_⟩ => .halt

def assemble {T L : Type*} [DecidableEq T] (p : Program T L) (t : T) (label : Label → L)
    (hc : ∀ pc,pc≠11 → pc≠12 → p (label pc)=instruction t label pc) :
    Decrement p t (label 0) (label 11) (label 12) where
  zero := label 1
  one := label 2
  stop := label 3
  backFalse := label 4
  backTrue := label 7
  reject := label 10
  read_code := hc 0 (by decide) (by decide)
  zero_code := hc 1 (by decide) (by decide)
  one_code := hc 2 (by decide) (by decide)
  stop_code := hc 3 (by decide) (by decide)
  rewindFalse := ⟨label 5,label 6,label 10,hc 4 (by decide) (by decide),
    hc 5 (by decide) (by decide),hc 6 (by decide) (by decide)⟩
  rewindTrue := ⟨label 8,label 9,label 10,hc 7 (by decide) (by decide),
    hc 8 (by decide) (by decide),hc 9 (by decide) (by decide)⟩

def program : Program (Fin 1) Label := instruction 0 id
def fragment : Decrement program 0 0 11 12 := assemble program 0 id (by intro _ _ _; rfl)

theorem all_inputs (xs : List Bool) (bank : Fin 1 → Tape Bool) (ht : bank 0=Counter.marked xs) :
    actualRun program (2*Counter.stepCost xs) (⟨0,bank⟩ : Config (Fin 1) Label).denote=
      (⟨if Counter.isZero xs then 12 else 11,
        Function.update bank 0 (Counter.marked (Counter.decrement xs))⟩ : Config (Fin 1) Label).denote :=
  fragment.actual_on_bank xs bank ht

theorem fixed_resources : Fintype.card (Fin 1)=1 ∧ Fintype.card (Sym Bool)=5 ∧
    Fintype.card Label=13 := by decide
end DecrementFamily
end FixedTapeCompiler.Microcode
