import TransposeFollowup.FusedPageClock

namespace TransposeFollowup.FusedPageClock
open FixedTapeCompiler CopyMachine
open ReusablePageClock (Port Label program cfg)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

theorem prefix_trace (ops : Fin q → PageOpcode) (xs : List Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops xs.length (cfg (.inl .read) ⟨pre,symbols xs++post⟩ pos)
      (cfg (.inl .read) ⟨(symbols xs).reverse++pre,post⟩ (PageClock.advance ops pos xs.length (xs.count true))) := by
  induction xs generalizing pre pos with
  | nil => simpa only [List.length_nil,symbols,List.map_nil,List.nil_append,List.reverse_nil,
      List.count_nil,PageClock.advance_zero] using (OperationalTrace.Trace.refl (step:=step ops)
        (active:=Active ops) (cfg (.inl .read) ⟨pre,post⟩ pos))
  | cons b xs ih =>
    have ha:=forward_trace ops b pre (symbols xs++post) pos
    have hb:=ih (.data b::pre) (PageClock.advance ops pos 1 (if b then 1 else 0))
    have hc:(if b then 1 else 0)+xs.count true=(b::xs).count true:=by cases b <;> simp [Nat.add_comm]
    have hn:1+xs.length=(b::xs).length:=by simp;omega
    simpa only [symbols,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,PageClock.advance_add,hc,hn] using trace_trans ha hb

theorem scan_trace (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (xs.length+1) (cfg (.inl .read) (Counter.marked xs) pos)
      (cfg (.inr .back) (RowStream.closedTape xs) (PageClock.advance ops pos xs.length (xs.count true))) := by
  have ha:=prefix_trace ops xs [.start] [.stop] pos
  have hb:=stop_trace ops ((symbols xs).reverse++[.start]) [] (PageClock.advance ops pos xs.length (xs.count true))
  simpa only [Counter.marked,RowStream.closedTape,symbols,List.map_reverse] using trace_trans ha hb

theorem prefix_run (ops : Fin q → PageOpcode) (xs : List Bool) (i : ℕ) (hi : i ≤ xs.length) (pos : Port q → ℤ) :
    run ops i (cfg (.inl .read) (Counter.marked xs) pos)=
      cfg (.inl .read) ⟨(symbols (xs.take i)).reverse++[.start],symbols (xs.drop i)++[.stop]⟩
        (PageClock.advance ops pos i ((xs.take i).count true)) := by
  have h:=OperationalTrace.trace_run (prefix_trace ops (xs.take i) [.start] (symbols (xs.drop i)++[.stop]) pos)
  have hl:(xs.take i).length=i:=List.length_take_of_le hi
  simpa only [hl,symbols,← List.map_append,← List.append_assoc,List.take_append_drop,Counter.marked] using h

end TransposeFollowup.FusedPageClock
