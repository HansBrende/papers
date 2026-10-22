import FixedTapeCompiler.MicroRewind
import FixedTapeCompiler.EraseStream

namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)
variable {T L : Type*} [DecidableEq T]

structure EraseEnd (p : Program T L) (t : T) (entry exit : L) where
  back : L
  erase : L
  finish : L
  reject : L
  entry_code : p entry = .act (single t ⟨some .blank,.left⟩) back
  read_code : p back = .read t (fun s => match s with
    | .start => finish | .data _ => erase | _ => reject)
  erase_code : p erase = .act (single t ⟨some .blank,.left⟩) back
  finish_code : p finish = .act (single t ⟨some .blank,.right⟩) exit

theorem EraseEnd.back_exact {p : Program T L} {t : T} {entry exit : L}
    (h : EraseEnd p t entry exit) (pre : List Bool)
    (ancestor suffix : List (Sym Bool)) (bank : T → Tape Bool) :
    run p (2*pre.length+2)
      (focus h.back t (⟨symbols pre++(.start::ancestor),suffix⟩ : Tape Bool).moveLeft bank) =
      focus exit t ⟨.blank::ancestor,List.replicate pre.length .blank++suffix⟩ bank := by
  induction pre generalizing suffix with
  | nil =>
    change step p (step p _) = _
    rw [at_read _ _ _ _ h.read_code]
    change step p (focus h.finish t _ bank) = _
    rw [at_act _ _ _ _ _ h.finish_code]
    rfl
  | cons b pre ih =>
    rw [show 2*(b::pre).length+2 = 2+(2*pre.length+2) by simp; omega,run_add]
    have hs : run p 2
        (focus h.back t (⟨symbols (b::pre)++(.start::ancestor),suffix⟩ : Tape Bool).moveLeft bank) =
        focus h.back t (⟨symbols pre++(.start::ancestor),.blank::suffix⟩ : Tape Bool).moveLeft bank := by
      change step p (step p _) = _
      rw [at_read _ _ _ _ h.read_code]
      change step p (focus h.erase t _ bank) = _
      rw [at_act _ _ _ _ _ h.erase_code]
      simp [Action.apply,symbols,Tape.moveLeft,Tape.write]
    rw [hs,ih]
    simp [List.replicate_succ',List.append_assoc]

theorem EraseEnd.exact {p : Program T L} {t : T} {entry exit : L}
    (h : EraseEnd p t entry exit) (xs : List Bool) (ancestor : List (Sym Bool))
    (bank : T → Tape Bool) :
    run p (2*xs.length+3)
      (focus entry t ⟨(symbols xs).reverse++(.start::ancestor),[.stop]⟩ bank) =
      focus exit t ⟨.blank::ancestor,List.replicate (xs.length+1) .blank⟩ bank := by
  rw [show 2*xs.length+3 = 1+(2*xs.length+2) by omega,run_add]
  change run p (2*xs.length+2) (step p _) = _
  rw [at_act _ _ _ _ _ h.entry_code]
  simpa [symbols,Action.apply,List.map_reverse,Tape.write,List.replicate_succ'] using
    h.back_exact xs.reverse ancestor [.blank] bank

structure Erase (p : Program T L) (t : T) (entry exit : L) where
  forward : L
  tailEntry : L
  reject : L
  read_code : p entry = .read t (fun s => match s with
    | .data _ => forward | .stop => tailEntry | _ => reject)
  forward_code : p forward = .act (single t ⟨none,.right⟩) entry
  tailCode : EraseEnd p t tailEntry exit

theorem Erase.scan {p : Program T L} {t : T} {entry exit : L}
    (h : Erase p t entry exit) (xs : List Bool) (pre : List (Sym Bool))
    (bank : T → Tape Bool) :
    run p (2*xs.length)
      (focus entry t ⟨pre,symbols xs++[.stop]⟩ bank) =
      focus entry t ⟨(symbols xs).reverse++pre,[.stop]⟩ bank := by
  induction xs generalizing pre with
  | nil => simp [OperationalTrace.run,symbols]
  | cons b xs ih =>
    rw [show 2*(b::xs).length = 2+2*xs.length by simp; omega,run_add]
    have hs : run p 2 (focus entry t ⟨pre,symbols (b::xs)++[.stop]⟩ bank) =
        focus entry t ⟨.data b::pre,symbols xs++[.stop]⟩ bank := by
      change step p (step p _) = _
      rw [at_read _ _ _ _ h.read_code]
      change step p (focus h.forward t _ bank) = _
      rw [at_act _ _ _ _ _ h.forward_code]
      rfl
    rw [hs,ih]
    simp [symbols,List.reverse_cons,List.append_assoc]

theorem Erase.exact {p : Program T L} {t : T} {entry exit : L}
    (h : Erase p t entry exit) (xs : List Bool) (ancestor : List (Sym Bool))
    (bank : T → Tape Bool) :
    run p (4*xs.length+4)
      (focus entry t ⟨.start::ancestor,symbols xs++[.stop]⟩ bank) =
      focus exit t ⟨.blank::ancestor,List.replicate (xs.length+1) .blank⟩ bank := by
  rw [show 4*xs.length+4 = 2*xs.length+(1+(2*xs.length+3)) by omega,run_add,h.scan,run_add]
  change run p (2*xs.length+3) (step p _) = _
  rw [at_read _ _ _ _ h.read_code]
  exact h.tailCode.exact xs ancestor bank

theorem erased_denote (pc : L) (t : T) (n : ℕ) (bank : T → Tape Bool) :
    (focus pc t ⟨[.blank],List.replicate (n+1) .blank⟩ bank).denote =
      (focus pc t ⟨[],[]⟩ bank).denote := by
  have ht : (⟨[Sym.blank],List.replicate (n+1) .blank⟩ : Tape Bool).denote =
      (⟨[],[]⟩ : Tape Bool).denote := by
    have hh := congrArg EraseStream.ConcreteConfig.tape (EraseStream.finished_denote n [])
    simpa [EraseStream.finished,EraseStream.Config.denote,EraseStream.blank_origin] using hh
  unfold Config.denote focus
  congr 1
  funext i
  by_cases hi : i=t
  · subst i; simpa [Config.denote,focus] using ht
  · simp [hi]

theorem EraseEnd.actual_to_blank {p : Program T L} {t : T} {entry exit : L}
    (h : EraseEnd p t entry exit) (xs : List Bool) (bank : T → Tape Bool) :
    actualRun p (2*xs.length+3)
      (focus entry t ⟨(symbols xs).reverse++[.start],[.stop]⟩ bank).denote =
      (focus exit t ⟨[],[]⟩ bank).denote := by
  rw [← run_refines,h.exact xs [],erased_denote]

theorem Erase.actual_to_blank {p : Program T L} {t : T} {entry exit : L}
    (h : Erase p t entry exit) (xs : List Bool) (bank : T → Tape Bool) :
    actualRun p (4*xs.length+4)
      (focus entry t ⟨[.start],symbols xs++[.stop]⟩ bank).denote =
      (focus exit t ⟨[],[]⟩ bank).denote := by
  rw [← run_refines,h.exact,erased_denote]

end FixedTapeCompiler.Microcode
