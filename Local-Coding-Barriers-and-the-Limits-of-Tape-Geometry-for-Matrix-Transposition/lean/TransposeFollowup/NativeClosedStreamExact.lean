import TransposeFollowup.NativeClosedStream
import TransposeFollowup.NativeCountedLoop

/-! Exact active transition count for the existing rewind program. The
program and tape convention are reused; no additional clock is assumed. -/
namespace TransposeFollowup.NativeClosedStream
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
abbrev ExactTrace := OperationalTrace.Trace (NativeMicrocode.step NativeSealBack.program)
  (NativeMicrocode.Active NativeSealBack.program)

theorem rewind_pair (s a : Sym Bool) (hs:s≠.start) (hb:s≠.blank)
    (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ExactTrace 2 (NativeSealBack.cfg .back ⟨a::pre,s::post⟩ pos).denote
      (NativeSealBack.cfg .back ⟨pre,a::s::post⟩ (fun p => pos p-1)).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,NativeSealBack.program]
  · have he:NativeMicrocode.step NativeSealBack.program (NativeSealBack.cfg .back ⟨a::pre,s::post⟩ pos).denote=
        (NativeSealBack.cfg .left ⟨a::pre,s::post⟩ pos).denote := by
      rw [← NativeZipper.step_denote]
      cases s <;> simp_all [NativeZipper.step,Microcode.step,NativeSealBack.program,NativeSealBack.cfg,Microcode.focus,Tape.read]
    rw [he]
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,NativeSealBack.program]
    · have he':NativeMicrocode.step NativeSealBack.program (NativeSealBack.cfg .left ⟨a::pre,s::post⟩ pos).denote=
          (NativeSealBack.cfg .back ⟨pre,a::s::post⟩ (fun p => pos p-1)).denote := by
        rw [← NativeZipper.step_denote]
        congr 1
        simp only [NativeZipper.step,Microcode.step,NativeSealBack.program,NativeSealBack.cfg,Microcode.focus]
        congr 1
        · congr 1;funext p;fin_cases p;simp [Microcode.single,Microcode.Action.apply,Tape.moveLeft]
        · funext p;fin_cases p;simp [Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift]
      rw [he'];exact .refl _

theorem rewind_finish (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ExactTrace 2 (NativeSealBack.cfg .back ⟨pre,.start::post⟩ pos).denote
      (NativeSealBack.cfg .done ⟨.start::pre,post⟩ (fun p => pos p+1)).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,NativeSealBack.program]
  · have he:NativeMicrocode.step NativeSealBack.program (NativeSealBack.cfg .back ⟨pre,.start::post⟩ pos).denote=
        (NativeSealBack.cfg .right ⟨pre,.start::post⟩ pos).denote := by
      rw [← NativeZipper.step_denote]
      simp [NativeZipper.step,Microcode.step,NativeSealBack.program,NativeSealBack.cfg,Microcode.focus,Tape.read]
    rw [he]
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,NativeSealBack.cfg,NativeZipper.Config.denote,Microcode.Config.denote,Microcode.focus,NativeSealBack.program]
    · have he':NativeMicrocode.step NativeSealBack.program (NativeSealBack.cfg .right ⟨pre,.start::post⟩ pos).denote=
          (NativeSealBack.cfg .done ⟨.start::pre,post⟩ (fun p => pos p+1)).denote := by
        rw [← NativeZipper.step_denote]
        congr 1
        simp only [NativeZipper.step,Microcode.step,NativeSealBack.program,NativeSealBack.cfg,Microcode.focus]
        congr 1
        · congr 1;funext p;fin_cases p;simp [Microcode.single,Microcode.Action.apply,Tape.moveRight,Tape.read]
        · funext p;fin_cases p;simp [Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift]
      rw [he'];exact .refl _

theorem rewind_tail_exact (xs : List Bool) (s : Sym Bool) (hs:s≠.start) (hb:s≠.blank)
    (post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ExactTrace (2*xs.length+4)
      (NativeSealBack.cfg .back ⟨symbols xs++[.start],s::post⟩ pos).denote
      (NativeSealBack.cfg .done ⟨[.start],(symbols xs).reverse++s::post⟩ (fun p => pos p-xs.length)).denote := by
  induction xs generalizing s post pos with
  | nil =>
    have ha:=rewind_pair s .start hs hb [] post pos
    have hb':=rewind_finish [] (s::post) (fun p => pos p-1)
    simpa only [List.length_nil,mul_zero,zero_add,symbols,List.map_nil,List.reverse_nil,List.nil_append,Nat.cast_zero,
      sub_zero,sub_add_cancel] using trace_trans ha hb'
  | cons b xs ih =>
    have ha:=rewind_pair s (.data b) hs hb (symbols xs++[.start]) post pos
    have ht:=ih (.data b) (by simp) (by simp) (s::post) (fun p => pos p-1)
    have hc:2+(2*xs.length+4)=2*(b::xs).length+4:=by simp;omega
    have hp:(fun p:Fin 1 => pos p-1-xs.length)=(fun p => pos p-(b::xs).length):=by funext p;simp;ring
    simpa only [symbols,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.nil_append,hc,hp] using trace_trans ha ht

theorem rewind_exact (xs : List Bool) (pos : Fin 1 → ℤ) :
    ExactTrace (2*xs.length+4)
      (NativeSealBack.cfg .back (RowStream.closedTape xs) pos).denote
      (NativeSealBack.cfg .done (Counter.marked xs) (fun p => pos p-xs.length)).denote := by
  simpa only [List.length_reverse,symbols,List.map_reverse,List.reverse_reverse,RowStream.closedTape,Counter.marked]
    using rewind_tail_exact xs.reverse .stop (by simp) (by simp) [] pos

end TransposeFollowup.NativeClosedStream
