import FixedTapeCompiler.MicroRewind
import FixedTapeCompiler.Counter

namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)
variable {T L : Type*} [DecidableEq T]

def focus2 (pc : L) (s t : T) (x y : Tape Bool) (bank : T → Tape Bool) : Config T L :=
  focus pc t y (Function.update bank s x)

def twins (s t : T) (a b : Action) : T → Action :=
  fun i => if i=t then b else if i=s then a else ⟨none,.stay⟩

theorem focus2_swap (pc : L) (s t : T) (hs : s ≠ t) (x y : Tape Bool) (bank : T → Tape Bool) :
    focus2 pc s t x y bank = focus pc s x (Function.update bank t y) := by
  unfold focus2 focus
  congr 1
  funext i
  by_cases hi : i=s
  · subst i; simp [hs]
  · by_cases hj : i=t
    · subst i; simp [Ne.symm hs]
    · simp [hi,hj]

theorem at2_read_source (p : Program T L) (pc : L) (s t : T) (hs : s ≠ t)
    (next : Sym Bool → L) (hp : p pc = .read s next)
    (x y : Tape Bool) (bank : T → Tape Bool) :
    step p (focus2 pc s t x y bank) = focus2 (next x.read) s t x y bank := by
  simp [step,focus2,focus,hp,hs]

theorem twins_apply (s t : T) (hs : s ≠ t) (a b : Action)
    (x y : Tape Bool) (bank : T → Tape Bool) :
    (fun i => (twins s t a b i).apply (Function.update (Function.update bank s x) t y i)) =
      Function.update (Function.update bank s (a.apply x)) t (b.apply y) := by
  funext i
  by_cases ht : i=t
  · subst i; simp [twins]
  · by_cases hi : i=s
    · subst i; simp [twins,hs]
    · simp [twins,hi,ht,Action.apply]

theorem at2_act (p : Program T L) (pc next : L) (s t : T) (hs : s ≠ t)
    (a b : Action) (hp : p pc = .act (twins s t a b) next)
    (x y : Tape Bool) (bank : T → Tape Bool) :
    step p (focus2 pc s t x y bank) = focus2 next s t (a.apply x) (b.apply y) bank := by
  simp [step,focus2,focus,hp,twins_apply s t hs]

structure Copy (p : Program T L) (s t : T) (entry exit : L) where
  scan : L
  zero : L
  one : L
  sealer : L
  backSource : L
  backTarget : L
  reject : L
  create : NewStream p t entry scan
  read_code : p scan = .read s (fun a => match a with
    | .data false => zero | .data true => one | .stop => sealer | _ => reject)
  zero_code : p zero = .act (twins s t ⟨none,.right⟩ ⟨some (.data false),.right⟩) scan
  one_code : p one = .act (twins s t ⟨none,.right⟩ ⟨some (.data true),.right⟩) scan
  seal_code : p sealer = .act (single t ⟨some .stop,.stay⟩) backSource
  rewindSource : Rewind p s backSource backTarget
  rewindTarget : Rewind p t backTarget exit

theorem Copy.forward {p : Program T L} {s t : T} {entry exit : L}
    (h : Copy p s t entry exit) (hs : s ≠ t) (xs : List Bool)
    (preSource preTarget : List (Sym Bool)) (bank : T → Tape Bool) :
    run p (2*xs.length)
      (focus2 h.scan s t ⟨preSource,symbols xs++[.stop]⟩ ⟨preTarget,[]⟩ bank) =
      focus2 h.scan s t ⟨(symbols xs).reverse++preSource,[.stop]⟩
        ⟨(symbols xs).reverse++preTarget,[]⟩ bank := by
  induction xs generalizing preSource preTarget with
  | nil => simp [OperationalTrace.run,symbols]
  | cons b xs ih =>
    rw [show 2*(b::xs).length = 2+2*xs.length by simp; omega,run_add]
    have hh : run p 2
        (focus2 h.scan s t ⟨preSource,symbols (b::xs)++[.stop]⟩ ⟨preTarget,[]⟩ bank) =
        focus2 h.scan s t ⟨.data b::preSource,symbols xs++[.stop]⟩ ⟨.data b::preTarget,[]⟩ bank := by
      change step p (step p _) = _
      rw [at2_read_source _ _ _ _ hs _ h.read_code]
      cases b
      · change step p (focus2 h.zero s t _ _ bank) = _
        rw [at2_act _ _ _ _ _ hs _ _ h.zero_code]
        rfl
      · change step p (focus2 h.one s t _ _ bank) = _
        rw [at2_act _ _ _ _ _ hs _ _ h.one_code]
        rfl
    rw [hh,ih]
    simp [symbols,List.reverse_cons,List.append_assoc]

theorem Copy.exact {p : Program T L} {s t : T} {entry exit : L}
    (h : Copy p s t entry exit) (hs : s ≠ t) (xs : List Bool) (bank : T → Tape Bool) :
    run p (6*xs.length+12)
      (focus2 entry s t (Counter.marked xs) ⟨[],[]⟩ bank) =
      focus2 exit s t (Counter.marked xs) (Counter.marked xs) bank := by
  have hc : run p 2 (focus2 entry s t (Counter.marked xs) ⟨[],[]⟩ bank) =
      focus2 h.scan s t (Counter.marked xs) ⟨[.start],[]⟩ bank :=
    h.create.exact (Function.update bank s (Counter.marked xs))
  have hf := h.forward hs xs [.start] [.start] bank
  have hseal : run p 2
      (focus2 h.scan s t ⟨(symbols xs).reverse++[.start],[.stop]⟩
        ⟨(symbols xs).reverse++[.start],[]⟩ bank) =
      focus2 h.backSource s t ⟨(symbols xs).reverse++[.start],[.stop]⟩
        ⟨(symbols xs).reverse++[.start],[.stop]⟩ bank := by
    change step p (step p _) = _
    rw [at2_read_source _ _ _ _ hs _ h.read_code]
    change step p (focus h.sealer t _ _) = _
    rw [at_act _ _ _ _ _ h.seal_code]
    rfl
  have hr1 : run p (2*xs.length+4)
      (focus2 h.backSource s t ⟨(symbols xs).reverse++[.start],[.stop]⟩
        ⟨(symbols xs).reverse++[.start],[.stop]⟩ bank) =
      focus2 h.backTarget s t (Counter.marked xs)
        ⟨(symbols xs).reverse++[.start],[.stop]⟩ bank := by
    rw [focus2_swap _ _ _ hs,focus2_swap _ _ _ hs]
    exact h.rewindSource.from_end xs [] _
  have hr2 : run p (2*xs.length+4)
      (focus2 h.backTarget s t (Counter.marked xs)
        ⟨(symbols xs).reverse++[.start],[.stop]⟩ bank) =
      focus2 exit s t (Counter.marked xs) (Counter.marked xs) bank :=
    h.rewindTarget.from_end xs [] _
  dsimp only [Counter.marked] at hc hr1 hr2 ⊢
  rw [show 6*xs.length+12 = 2+(2*xs.length+(2+((2*xs.length+4)+(2*xs.length+4)))) by omega,
    run_add,hc,run_add,hf,run_add,hseal,run_add,hr1,hr2]

theorem Copy.actual_exact {p : Program T L} {s t : T} {entry exit : L}
    (h : Copy p s t entry exit) (hs : s ≠ t) (xs : List Bool) (bank : T → Tape Bool) :
    actualRun p (6*xs.length+12)
      (focus2 entry s t (Counter.marked xs) ⟨[],[]⟩ bank).denote =
      (focus2 exit s t (Counter.marked xs) (Counter.marked xs) bank).denote := by
  rw [← run_refines,h.exact hs]

end FixedTapeCompiler.Microcode
