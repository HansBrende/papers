import TransposeFollowup.NativeErase
import TransposeFollowup.MicrocodeEmbedding

/-! Rewind a mixed-symbol span to its left blank boundary. There is no
START marker and STOP is ordinary nonblank data for this routine. Every
read and movement is paid. The scan also handles an empty span. -/
namespace TransposeFollowup.NativeSpanRewind
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label | left | read | restore | done
  deriving DecidableEq

instance : Fintype Label where
  elems:={.left,.read,.restore,.done}
  complete:=by intro pc;cases pc <;> simp

def program : Microcode.Program (Fin 1) Label
  | .left => .act (fun _ => ⟨none,.left⟩) .read
  | .read => .read 0 (fun s => if s=.blank then .restore else .left)
  | .restore => .act (fun _ => ⟨none,.right⟩) .done
  | .done => .halt

def cfg (pc : Label) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) Label :=
  ⟨⟨pc,fun _ => word⟩,pos⟩

theorem two_steps (a : Sym Bool) (left right : List (Sym Bool)) (ha : a≠.blank) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 2 (cfg .left ⟨a::left,right⟩ pos)=
      cfg .left ⟨left,a::right⟩ (fun p => pos p-1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.read,ha,NativeMicrocode.direction,Transpose.Dir.shift]

theorem empty_run (right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run program 3 (cfg .left ⟨[],right⟩ pos)=cfg .done ⟨[.blank],right⟩ pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem rewind_run (left right : List (Sym Bool)) (h : ∀ s ∈ left,s≠.blank) (pos : Fin 1 → ℤ) :
    NativeZipper.run program (2*left.length+3) (cfg .left ⟨left,right⟩ pos)=
      cfg .done ⟨[.blank],left.reverse++right⟩ (fun p => pos p-left.length) := by
  induction left generalizing right pos with
  | nil => simpa only [List.length_nil,mul_zero,zero_add,List.reverse_nil,List.nil_append,Nat.cast_zero,sub_zero] using empty_run right pos
  | cons a left ih =>
    have ha : a≠.blank := h a (by simp)
    have hl : ∀ s ∈ left,s≠.blank := by intro s hs; exact h s (by simp [hs])
    rw [show 2*(a::left).length+3=2+(2*left.length+3) by simp;omega,
      NativeZipper.run_add,two_steps a left right ha,ih _ hl]
    congr 1
    · simp [List.reverse_cons,List.append_assoc]
    · funext p;simp;ring

theorem blank_left_denote (right : List (Sym Bool)) :
    (⟨[.blank],right⟩ : Tape Bool).denote=(⟨[],right⟩ : Tape Bool).denote := by
  unfold Tape.denote Turing.Tape.mk₂
  exact congrArg (fun a => Turing.Tape.mk' a (Turing.ListBlank.mk right)) (EraseStream.blanks_eq_nil 1)

theorem cfg_blank_left (right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    (cfg .done ⟨[.blank],right⟩ pos).denote=(cfg .done ⟨[],right⟩ pos).denote := by
  unfold NativeZipper.Config.denote Microcode.Config.denote cfg
  congr 2
  funext p;exact blank_left_denote right

theorem rewind_trace (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 2*xs.length+3,
      OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program) t
        (cfg .left ⟨xs.reverse,[]⟩ pos).denote
        (cfg .done ⟨[],xs⟩ (fun p => pos p-xs.length)).denote := by
  have hr : ∀ s ∈ xs.reverse,s≠.blank := by intro s hs;exact h s (List.mem_reverse.mp hs)
  obtain ⟨t,ht,htr⟩ := NativeZipper.trace_of_run program (rewind_run xs.reverse [] hr pos)
  exact ⟨t,by simpa only [List.length_reverse] using ht,by
    simpa only [List.length_reverse,List.reverse_reverse,List.append_nil,cfg_blank_left] using htr⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 1) Label.left
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=1 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=4 ∧ nativeEncoding.label .left=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_rewind (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank) (pos : Fin 1 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*xs.length+3,
      Transpose.stepN nativeMachine input t ((cfg .left ⟨xs.reverse,[]⟩ pos).denote.denote nativeEncoding program inputPos outRev)=
        some ((cfg .done ⟨[],xs⟩ (fun p => pos p-xs.length)).denote.denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input ((cfg .done ⟨[],xs⟩ (fun p => pos p-xs.length)).denote.denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := rewind_trace xs h pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 1 ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List (Sym Bool)) (h : ∀ s ∈ xs,s≠.blank) (pos : Fin 1 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*xs.length+3,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .left ⟨xs.reverse,[]⟩ pos).denote outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done ⟨[],xs⟩ (fun p => pos p-xs.length)).denote outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := rewind_trace xs h pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeSpanRewind
