import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.NativeCountedLoop

/-! Paid erasure of a contiguous nonblank span, including arbitrary START
and STOP data. Entry may be at its first cell or just past its last cell.
The erased tape is wholly blank and the head returns to the span's origin. -/
namespace TransposeFollowup.NativeSpanErase
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | scan | advance | left | read | clear | restore | done
  deriving DecidableEq

instance : Fintype Label where
  elems:={.scan,.advance,.left,.read,.clear,.restore,.done}
  complete:=by intro pc;cases pc <;> simp

def program : Microcode.Program (Fin 1) Label
  | .scan => .read 0 (fun s => if s=.blank then .left else .advance)
  | .advance => .act (fun _ => ⟨none,.right⟩) .scan
  | .left => .act (fun _ => ⟨none,.left⟩) .read
  | .read => .read 0 (fun s => if s=.blank then .restore else .clear)
  | .clear => .act (fun _ => ⟨some .blank,.stay⟩) .left
  | .restore => .act (fun _ => ⟨none,.right⟩) .done
  | .done => .halt

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => word⟩,pos⟩

theorem scan_pair (a : Sym Bool) (left right : List (Sym Bool)) (ha : a≠.blank) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg .scan ⟨left,a::right⟩ pos)=
      cfg .scan ⟨a::left,right⟩ (fun p => pos p+1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveRight,Tape.read,ha,NativeMicrocode.direction,Transpose.Dir.shift]

theorem scan_run (left right : List (Sym Bool)) (h : ∀ s ∈ right,s≠.blank) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*right.length+1) (cfg .scan ⟨left,right⟩ pos)=
      cfg .left ⟨right.reverse++left,[]⟩ (fun p => pos p+right.length) := by
  induction right generalizing left pos with
  | nil =>
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Tape.read]
  | cons a right ih =>
    have ha : a≠.blank:=h a (by simp)
    have hr : ∀ s ∈ right,s≠.blank:=by intro s hs;exact h s (by simp [hs])
    rw [show 2*(a::right).length+1=2+(2*right.length+1) by simp;omega,
      NativeZipper.run_add,scan_pair a left right ha,ih _ hr]
    congr 1
    · simp [List.reverse_cons,List.append_assoc]
    · funext p;simp;ring

theorem erase_triple (a : Sym Bool) (left right : List (Sym Bool)) (ha : a≠.blank) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 3 (cfg .left ⟨a::left,right⟩ pos)=
      cfg .left ⟨left,.blank::right⟩ (fun p => pos p-1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.write,Tape.read,ha,NativeMicrocode.direction,Transpose.Dir.shift]

theorem empty_run (right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 3 (cfg .left ⟨[],right⟩ pos)=cfg .done ⟨[.blank],right⟩ pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem erase_run (left right : List (Sym Bool)) (h : ∀ s ∈ left,s≠.blank) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (3*left.length+3) (cfg .left ⟨left,right⟩ pos)=
      cfg .done ⟨[.blank],List.replicate left.length .blank++right⟩ (fun p => pos p-left.length) := by
  induction left generalizing right pos with
  | nil => simpa only [List.length_nil,mul_zero,zero_add,List.replicate_zero,List.nil_append,Nat.cast_zero,sub_zero] using empty_run right pos
  | cons a left ih =>
    have ha : a≠.blank:=h a (by simp)
    have hl : ∀ s ∈ left,s≠.blank:=by intro s hs;exact h s (by simp [hs])
    rw [show 3*(a::left).length+3=3+(3*left.length+3) by simp;omega,
      NativeZipper.run_add,erase_triple a left right ha,ih _ hl]
    congr 1
    · simp [List.replicate_succ',List.append_assoc]
    · funext p;simp;ring

theorem erased_denote (m : ℕ) :
    (⟨[.blank],List.replicate m .blank⟩ : Tape Bool).denote=(⟨[],[]⟩ : Tape Bool).denote := by
  unfold Tape.denote Turing.Tape.mk₂
  change Turing.Tape.mk' (Turing.ListBlank.mk (List.replicate 1 (Sym.blank : Sym Bool)))
    (Turing.ListBlank.mk (List.replicate m (Sym.blank : Sym Bool)))=
    Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk [])
  rw [EraseStream.blanks_eq_nil 1,EraseStream.blanks_eq_nil m]

theorem cfg_erased_denote (m : ℕ) (pos : Fin 1 → ℤ) :
    (cfg .done ⟨[.blank],List.replicate m .blank⟩ pos).denote=(cfg .done ⟨[],[]⟩ pos).denote := by
  unfold NativeZipper.Config.denote Microcode.Config.denote cfg
  congr 2
  funext p;exact erased_denote m

theorem from_end_trace (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 3*xs.length+3,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .left ⟨xs.reverse,[]⟩ pos).denote
        (cfg .done ⟨[],[]⟩ (fun p => pos p-xs.length)).denote := by
  have hr : ∀ s ∈ xs.reverse,s≠.blank:=by intro s hs;exact h s (List.mem_reverse.mp hs)
  obtain ⟨t,ht,htr⟩:=NativeZipper.trace_of_run program (erase_run xs.reverse [] hr pos)
  exact ⟨t,by simpa only [List.length_reverse] using ht,by
    simpa only [List.length_reverse,List.append_nil,cfg_erased_denote] using htr⟩

theorem from_start_trace (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 5*xs.length+4,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .scan ⟨[],xs⟩ pos).denote (cfg .done ⟨[],[]⟩ pos).denote := by
  obtain ⟨a,ha,ta⟩:=NativeZipper.trace_of_run program (scan_run [] xs h pos)
  simp only [List.append_nil] at ta
  obtain ⟨b,hb,tb⟩:=from_end_trace xs h (fun p => pos p+xs.length)
  have hp : (fun p => pos p+(xs.length:ℤ)-xs.length)=pos:=by funext p;ring
  rw [hp] at tb
  exact ⟨a+b,by omega,NativeCountedLoop.trace_trans ta tb⟩

end TransposeFollowup.NativeSpanErase
