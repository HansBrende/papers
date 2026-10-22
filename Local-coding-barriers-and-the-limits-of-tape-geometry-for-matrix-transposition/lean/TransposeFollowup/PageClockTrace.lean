import TransposeFollowup.PageClockMachine
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.TracePrefix

namespace TransposeFollowup.PageClock
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

theorem prefix_trace (ops : Fin q → PageOpcode) (xs : List Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops (2*xs.length) (cfg .read ⟨pre,symbols xs++post⟩ pos)
      (cfg .read ⟨(symbols xs).reverse++pre,post⟩ (advance ops pos xs.length (xs.count true))) := by
  induction xs generalizing pre pos with
  | nil => simpa only [List.length_nil,mul_zero,symbols,List.map_nil,List.nil_append,List.reverse_nil,
      List.count_nil,advance_zero] using (OperationalTrace.Trace.refl (step:=NativeMicrocode.step (program ops))
        (active:=NativeMicrocode.Active (program ops)) (cfg .read ⟨pre,post⟩ pos))
  | cons b xs ih =>
    have ha:=two_trace ops b pre (symbols xs++post) pos
    have hb:=ih (.data b::pre) (advance ops pos 1 (if b then 1 else 0))
    have hlen:2+2*xs.length=2*(b::xs).length:=by simp;omega
    have hc:(if b then 1 else 0)+xs.count true=(b::xs).count true:=by cases b <;> simp [Nat.add_comm]
    have hn:1+xs.length=(b::xs).length:=by simp;omega
    simpa only [symbols,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,advance_add,hlen,hc,hn] using trace_trans ha hb

theorem complete_trace (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (2*xs.length+1) (cfg .read (Counter.marked xs) pos)
      (cfg .done (RowStream.closedTape xs) (advance ops pos xs.length (xs.count true))) := by
  have ha:=prefix_trace ops xs [.start] [.stop] pos
  have hb:=stop_trace ops ((symbols xs).reverse++[.start]) [] (advance ops pos xs.length (xs.count true))
  simpa only [Counter.marked,RowStream.closedTape,symbols,List.map_reverse] using trace_trans ha hb

theorem prefix_run (ops : Fin q → PageOpcode) (xs : List Bool) (i : ℕ) (hi:i≤xs.length) (pos : Port q → ℤ) :
    NativeMicrocode.run (program ops) (2*i) (cfg .read (Counter.marked xs) pos)=
      cfg .read ⟨(symbols (xs.take i)).reverse++[.start],symbols (xs.drop i)++[.stop]⟩
        (advance ops pos i ((xs.take i).count true)) := by
  have h:=OperationalTrace.trace_run (prefix_trace ops (xs.take i) [.start] (symbols (xs.drop i)++[.stop]) pos)
  have hl:(xs.take i).length=i:=List.length_take_of_le hi
  simpa only [hl,symbols,← List.map_append,← List.append_assoc,List.take_append_drop,Counter.marked] using h

theorem forward_positions (ops : Fin q → PageOpcode) (xs : List Bool) (s : ℕ) (hs:s≤2*xs.length+1) (pos : Port q → ℤ) :
    (NativeMicrocode.run (program ops) s (cfg .read (Counter.marked xs) pos)).pos=
      advance ops pos (s/2) ((xs.take (s/2)).count true) := by
  have hi:s/2≤xs.length:=by omega
  have hr:=prefix_run ops xs (s/2) hi pos
  have hm:s%2=0 ∨ s%2=1:=by omega
  rcases hm with hm|hm
  · have he:s=2*(s/2):=by omega
    conv_lhs => rw [he,hr]
    rfl
  · have he:s=2*(s/2)+1:=by omega
    conv_lhs => rw [he,show NativeMicrocode.run (program ops) (2*(s/2)+1) _=
      NativeMicrocode.run (program ops) 1 (NativeMicrocode.run (program ops) (2*(s/2)) _) from
      OperationalTrace.run_add _ _ _ _,hr]
    rfl

end TransposeFollowup.PageClock
