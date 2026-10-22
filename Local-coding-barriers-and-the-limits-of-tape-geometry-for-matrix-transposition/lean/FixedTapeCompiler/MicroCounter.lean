import FixedTapeCompiler.MicroRewind
import FixedTapeCompiler.Counter

/-! The exact read/action-split binary decrement fragment. Its two return
labels are arbitrary caller continuations, not padded halting states. -/
namespace FixedTapeCompiler.Microcode
open CopyMachine (Sym Tape symbols)
variable {T L : Type*} [DecidableEq T]

structure Decrement (p : Program T L) (t : T) (entry success underflow : L) where
  zero : L
  one : L
  stop : L
  backFalse : L
  backTrue : L
  reject : L
  read_code : p entry = .read t (fun s => match s with
    | .data false => zero | .data true => one | .stop => stop | _ => reject)
  zero_code : p zero = .act (single t ⟨some (.data true),.right⟩) entry
  one_code : p one = .act (single t ⟨some (.data false),.left⟩) backFalse
  stop_code : p stop = .act (single t ⟨none,.left⟩) backTrue
  rewindFalse : Rewind p t backFalse success
  rewindTrue : Rewind p t backTrue underflow

theorem Decrement.zeros {p : Program T L} {t : T} {entry success underflow : L}
    (h : Decrement p t entry success underflow) (n : ℕ)
    (left suffix : List (Sym Bool)) (bank : T → Tape Bool) :
    run p (2*n) (focus entry t ⟨left,List.replicate n (.data false)++suffix⟩ bank) =
      focus entry t ⟨List.replicate n (.data true)++left,suffix⟩ bank := by
  induction n generalizing left with
  | zero => simp [OperationalTrace.run]
  | succ n ih =>
    rw [show 2*(n+1) = 2+2*n by omega,run_add]
    have hs : run p 2
        (focus entry t ⟨left,List.replicate (n+1) (.data false)++suffix⟩ bank) =
        focus entry t ⟨.data true::left,List.replicate n (.data false)++suffix⟩ bank := by
      change step p (step p _) = _
      rw [at_read _ _ _ _ h.read_code]
      simp only [List.replicate_succ,List.cons_append,Tape.read,List.headD_cons]
      rw [at_act _ _ _ _ _ h.zero_code]
      rfl
    rw [hs,ih]
    have he : List.replicate n (.data true) ++ (.data true::left) =
        List.replicate (n+1) (Sym.data true) ++ left := by
      rw [List.replicate_succ']
      simp
    rw [he]

theorem Decrement.nonzero {p : Program T L} {t : T} {entry success underflow : L}
    (h : Decrement p t entry success underflow) (n : ℕ) (xs : List Bool)
    (bank : T → Tape Bool) :
    run p (4*n+4)
      (focus entry t (Counter.marked (List.replicate n false++true::xs)) bank) =
      focus success t (Counter.marked (List.replicate n true++false::xs)) bank := by
  have hz := h.zeros n [.start] (.data true::(symbols xs++[.stop])) bank
  have hz' : run p (2*n)
      (focus entry t (Counter.marked (List.replicate n false++true::xs)) bank) =
      focus entry t ⟨List.replicate n (.data true)++[.start],.data true::(symbols xs++[.stop])⟩ bank := by
    simpa [Counter.marked,symbols,List.map_append,List.map_replicate] using hz
  rw [show 4*n+4 = 2*n+(2+(2*n+2)) by omega,run_add,hz',run_add]
  have hone : run p 2
      (focus entry t ⟨List.replicate n (.data true)++[.start],.data true::(symbols xs++[.stop])⟩ bank) =
      focus h.backFalse t
        (⟨List.replicate n (.data true)++[.start],.data false::(symbols xs++[.stop])⟩ : Tape Bool).moveLeft bank := by
    change step p (step p _) = _
    rw [at_read _ _ _ _ h.read_code]
    change step p (focus h.one t _ bank) = _
    rw [at_act _ _ _ _ _ h.one_code]
    rfl
  rw [hone]
  simpa [Counter.marked,symbols,List.map_append,List.map_replicate,List.reverse_replicate] using
    h.rewindFalse.after_left (List.replicate n true) (.data false::(symbols xs++[.stop])) [] bank

theorem Decrement.zero_word {p : Program T L} {t : T} {entry success underflow : L}
    (h : Decrement p t entry success underflow) (n : ℕ) (bank : T → Tape Bool) :
    run p (4*n+4) (focus entry t (Counter.marked (List.replicate n false)) bank) =
      focus underflow t (Counter.marked (List.replicate n true)) bank := by
  have hz := h.zeros n [.start] [.stop] bank
  have hz' : run p (2*n) (focus entry t (Counter.marked (List.replicate n false)) bank) =
      focus entry t ⟨List.replicate n (.data true)++[.start],[.stop]⟩ bank := by
    simpa [Counter.marked,symbols,List.map_replicate] using hz
  rw [show 4*n+4 = 2*n+(2+(2*n+2)) by omega,run_add,hz',run_add]
  have hs : run p 2
      (focus entry t ⟨List.replicate n (.data true)++[.start],[.stop]⟩ bank) =
      focus h.backTrue t
        (⟨List.replicate n (.data true)++[.start],[.stop]⟩ : Tape Bool).moveLeft bank := by
    change step p (step p _) = _
    rw [at_read _ _ _ _ h.read_code]
    change step p (focus h.stop t _ bank) = _
    exact at_act _ _ _ _ _ h.stop_code _ _
  rw [hs]
  simpa [Counter.marked,symbols,List.map_replicate,List.reverse_replicate] using
    h.rewindTrue.after_left (List.replicate n true) [.stop] [] bank

theorem Decrement.exact {p : Program T L} {t : T} {entry success underflow : L}
    (h : Decrement p t entry success underflow) (xs : List Bool) (bank : T → Tape Bool) :
    run p (2*Counter.stepCost xs) (focus entry t (Counter.marked xs) bank) =
      focus (if Counter.isZero xs then underflow else success) t
        (Counter.marked (Counter.decrement xs)) bank := by
  cases hz : Counter.isZero xs with
  | false =>
    rcases Counter.nonzero_prefix xs hz with ⟨n,ys,rfl⟩
    have hp := Counter.prefix_functions n ys
    simpa only [hz,Bool.false_eq_true,ite_false,Counter.stepCost,hp.1,hp.2,
      show 2*(2*n+2) = 4*n+4 by omega] using h.nonzero n ys bank
  | true =>
    have he := Counter.zero_replicate xs hz
    rw [he]
    simp only [Counter.stepCost,(Counter.zero_functions xs.length).1,
      (Counter.zero_functions xs.length).2]
    simpa [show 2*(2*xs.length+2) = 4*xs.length+4 by omega] using h.zero_word xs.length bank

theorem Decrement.actual_exact {p : Program T L} {t : T} {entry success underflow : L}
    (h : Decrement p t entry success underflow) (xs : List Bool) (bank : T → Tape Bool) :
    actualRun p (2*Counter.stepCost xs) (focus entry t (Counter.marked xs) bank).denote =
      (focus (if Counter.isZero xs then underflow else success) t
        (Counter.marked (Counter.decrement xs)) bank).denote := by
  rw [← run_refines,h.exact]

end FixedTapeCompiler.Microcode
