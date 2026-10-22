import FixedTapeCompiler.MicroScan

namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)
variable {T L : Type*} [DecidableEq T]

/-- Append a fixed Boolean map of a marked source onto an open target,
then restore the source. The existing target prefix is never traversed. -/
structure MappedAppend (p : Program T L) (s t : T) (f : Bool → Bool) (entry exit : L) where
  zero : L
  one : L
  backEntry : L
  reject : L
  read_code : p entry=.read s (fun a => match a with
    | .data false => zero | .data true => one | .stop => backEntry | _ => reject)
  zero_code : p zero=.act (twins s t ⟨none,.right⟩ (emitBit (f false))) entry
  one_code : p one=.act (twins s t ⟨none,.right⟩ (emitBit (f true))) entry
  rewindCode : Rewind p s backEntry exit

theorem MappedAppend.forward {p : Program T L} {s t : T} {f : Bool → Bool} {entry exit : L}
    (h : MappedAppend p s t f entry exit) (hs : s≠t)
    (xs : List Bool) (srcPre dstPre : List (Sym Bool)) (bank : T → Tape Bool) :
    run p (2*xs.length)
      (focus2 entry s t ⟨srcPre,symbols xs++[.stop]⟩ ⟨dstPre,[]⟩ bank)=
      focus2 entry s t ⟨(symbols xs).reverse++srcPre,[.stop]⟩
        ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank := by
  induction xs generalizing srcPre dstPre with
  | nil => rfl
  | cons b xs ih =>
    rw [show 2*(b::xs).length=2+2*xs.length by simp; omega,run_add]
    have hh : run p 2 (focus2 entry s t ⟨srcPre,symbols (b::xs)++[.stop]⟩ ⟨dstPre,[]⟩ bank)=
        focus2 entry s t ⟨.data b::srcPre,symbols xs++[.stop]⟩ ⟨.data (f b)::dstPre,[]⟩ bank := by
      change step p (step p _)=_
      rw [at2_read_source _ _ _ _ hs _ h.read_code]
      cases b
      · change step p (focus2 h.zero s t _ _ bank)=_
        rw [at2_act _ _ _ _ _ hs _ _ h.zero_code]
        rfl
      · change step p (focus2 h.one s t _ _ bank)=_
        rw [at2_act _ _ _ _ _ hs _ _ h.one_code]
        rfl
    rw [hh,ih]
    simp [symbols,List.reverse_cons,List.append_assoc]

theorem MappedAppend.exact {p : Program T L} {s t : T} {f : Bool → Bool} {entry exit : L}
    (h : MappedAppend p s t f entry exit) (hs : s≠t)
    (xs : List Bool) (dstPre : List (Sym Bool)) (bank : T → Tape Bool) :
    run p (4*xs.length+5) (focus2 entry s t (Counter.marked xs) ⟨dstPre,[]⟩ bank)=
      focus2 exit s t (Counter.marked xs) ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank := by
  have hf := h.forward hs xs [.start] dstPre bank
  have he : run p 1
      (focus2 entry s t ⟨(symbols xs).reverse++[.start],[.stop]⟩
        ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank)=
      focus2 h.backEntry s t ⟨(symbols xs).reverse++[.start],[.stop]⟩
        ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank := by
    change step p _=_
    rw [at2_read_source _ _ _ _ hs _ h.read_code]
    rfl
  have hr : run p (2*xs.length+4)
      (focus2 h.backEntry s t ⟨(symbols xs).reverse++[.start],[.stop]⟩
        ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank)=
      focus2 exit s t (Counter.marked xs) ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank := by
    rw [focus2_swap _ _ _ hs,focus2_swap _ _ _ hs]
    exact h.rewindCode.from_end xs [] _
  dsimp only [Counter.marked] at hr ⊢
  rw [show 4*xs.length+5=2*xs.length+(1+(2*xs.length+4)) by omega,
    run_add,hf,run_add,he,hr]

theorem MappedAppend.actual_exact {p : Program T L} {s t : T} {f : Bool → Bool} {entry exit : L}
    (h : MappedAppend p s t f entry exit) (hs : s≠t)
    (xs : List Bool) (dstPre : List (Sym Bool)) (bank : T → Tape Bool) :
    actualRun p (4*xs.length+5) (focus2 entry s t (Counter.marked xs) ⟨dstPre,[]⟩ bank).denote=
      (focus2 exit s t (Counter.marked xs) ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩ bank).denote := by
  rw [← run_refines,h.exact hs]

theorem MappedAppend.actual_on_bank {p : Program T L} {s t : T} {f : Bool → Bool} {entry exit : L}
    (h : MappedAppend p s t f entry exit) (hs : s≠t)
    (xs : List Bool) (dstPre : List (Sym Bool)) (bank : T → Tape Bool)
    (hsrc : bank s=Counter.marked xs) (hdst : bank t=⟨dstPre,[]⟩) :
    actualRun p (4*xs.length+5) (⟨entry,bank⟩ : Config T L).denote=
      (⟨exit,Function.update bank t ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩⟩ : Config T L).denote := by
  have he := h.actual_exact hs xs dstPre bank
  have hi : focus2 entry s t (Counter.marked xs) ⟨dstPre,[]⟩ bank=⟨entry,bank⟩ := by
    simp only [focus2,focus,← hsrc,← hdst,Function.update_eq_self]
  rw [hi] at he
  simpa only [focus2,focus,← hsrc,Function.update_eq_self] using he

namespace MappedAppendFamily
abbrev Label := Fin 8

def instruction (s t : T) (f : Bool → Bool) (label : Label → L) : Label → Instruction T L
  | ⟨0,_⟩ => .read s (fun a => match a with
      | .data false => label 1 | .data true => label 2 | .stop => label 3 | _ => label 6)
  | ⟨1,_⟩ => .act (twins s t ⟨none,.right⟩ (emitBit (f false))) (label 0)
  | ⟨2,_⟩ => .act (twins s t ⟨none,.right⟩ (emitBit (f true))) (label 0)
  | ⟨3,_⟩ => .read s (fun a => match a with
      | .start => label 5 | .stop | .data _ => label 4 | .blank => label 6)
  | ⟨4,_⟩ => .act (single s ⟨none,.left⟩) (label 3)
  | ⟨5,_⟩ => .act (single s ⟨none,.right⟩) (label 7)
  | ⟨6,_⟩ => .reject
  | ⟨7,_⟩ => .halt

def assemble (p : Program T L) (s t : T) (f : Bool → Bool) (label : Label → L)
    (hc : ∀ pc,pc≠7 → p (label pc)=instruction s t f label pc) :
    MappedAppend p s t f (label 0) (label 7) where
  zero := label 1
  one := label 2
  backEntry := label 3
  reject := label 6
  read_code := hc 0 (by decide)
  zero_code := hc 1 (by decide)
  one_code := hc 2 (by decide)
  rewindCode := ⟨label 4,label 5,label 6,hc 3 (by decide),hc 4 (by decide),hc 5 (by decide)⟩

def program (f : Bool → Bool) : Program (Fin 2) Label := instruction 0 1 f id
def fragment (f : Bool → Bool) : MappedAppend (program f) 0 1 f 0 7 :=
  assemble (program f) 0 1 f id (by intro _ _; rfl)

theorem all_inputs (f : Bool → Bool) (xs : List Bool) (dstPre : List (Sym Bool)) (bank : Fin 2 → Tape Bool)
    (hs : bank 0=Counter.marked xs) (ht : bank 1=⟨dstPre,[]⟩) :
    actualRun (program f) (4*xs.length+5) (⟨0,bank⟩ : Config (Fin 2) Label).denote=
      (⟨7,Function.update bank 1 ⟨(symbols (xs.map f)).reverse++dstPre,[]⟩⟩ : Config (Fin 2) Label).denote :=
  (fragment f).actual_on_bank (by decide) xs dstPre bank hs ht

theorem fixed_resources : Fintype.card (Fin 2)=2 ∧ Fintype.card (Sym Bool)=5 ∧
    Fintype.card Label=8 := by decide
end MappedAppendFamily
end FixedTapeCompiler.Microcode
