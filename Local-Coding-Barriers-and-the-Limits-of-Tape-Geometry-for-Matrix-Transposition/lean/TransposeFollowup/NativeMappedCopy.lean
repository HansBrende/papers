import TransposeFollowup.NativeMappedAppend
import TransposeFollowup.NativeSealBack
import TransposeFollowup.NativeBuffer
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop

/-! A paid caller composes blank-target preparation, archived mapped append,
and seal/rewind. Two real linking jumps are included. The source word and
both absolute heads are restored; the target receives a marked mapped word. -/

namespace TransposeFollowup.NativeMappedCopy

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
set_option autoImplicit false

def targetBinding : FinitePortBinding (Fin 1) (Fin 2) where
  ports := ⟨fun _ => 1, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun t => if t = 1 then some 0 else none
  decode_spec := by
    intro p t
    change (if p = 1 then some (0 : Fin 1) else none) = some t ↔ (1 : Fin 2) = p
    fin_cases p <;> fin_cases t <;> decide

def bothBinding : FinitePortBinding (Fin 2) (Fin 2) where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

inductive Label
  | init (pc : NativeBuffer.Label)
  | append (pc : Microcode.MappedAppendFamily.Label)
  | seal (pc : NativeSealBack.Label)
  deriving DecidableEq, Fintype

def program (f : Bool → Bool) : Microcode.Program (Fin 2) Label
  | .init .done => .jump (.append 0)
  | .init pc => targetBinding.instruction Label.init (NativeBuffer.program pc)
  | .append pc => if pc = 7 then .jump (.seal .seal)
      else bothBinding.instruction Label.append (Microcode.MappedAppendFamily.program f pc)
  | .seal pc => targetBinding.instruction Label.seal (NativeSealBack.program pc)

theorem init_code (f : Bool → Bool) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program f (.init pc) = MicrocodeEmbedding.instruction targetBinding.ports
      Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program, NativeBuffer.program, FinitePortBinding.instruction_eq]

theorem append_code (f : Bool → Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program f pc ≠ .halt)
    (_ : Microcode.MappedAppendFamily.program f pc ≠ .reject) :
    program f (.append pc) = MicrocodeEmbedding.instruction bothBinding.ports
      Label.append (Microcode.MappedAppendFamily.program f pc) := by
  have hp : pc ≠ 7 := by intro h; subst pc; exact hh rfl
  simp [program, hp, FinitePortBinding.instruction_eq]

theorem seal_code (f : Bool → Bool) (pc : NativeSealBack.Label) :
    program f (.seal pc) = MicrocodeEmbedding.instruction targetBinding.ports
      Label.seal (NativeSealBack.program pc) :=
  targetBinding.instruction_eq _ _

def bank (source target : Tape Bool) (t : Fin 2) : Tape Bool := if t = 0 then source else target

def cfg (pc : Label) (source target : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeMicrocode.Config (Fin 2) Label :=
  ⟨⟨pc, fun t => (bank source target t).denote⟩, pos⟩

def zipperCfg (pc : Label) (source target : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeZipper.Config (Fin 2) Label := ⟨⟨pc, bank source target⟩, pos⟩

def frame (source : Tape Bool) (pos : Fin 2 → ℤ) : MicrocodeEmbedding.Frame (Fin 2) :=
  ⟨fun t => (bank source ⟨[], []⟩ t).denote, pos⟩

theorem embed_init (pc : NativeBuffer.Label) (source word : Tape Bool)
    (pos : Fin 2 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports Label.init
      (NativeBuffer.cfg pc word (fun _ => z)).denote (frame source pos) =
      cfg (.init pc) source word (Function.update pos 1 z) := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus cfg frame
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext t <;> fin_cases t <;> rfl

theorem embed_append (pc : Microcode.MappedAppendFamily.Label) (source word : Tape Bool)
    (pos framePos : Fin 2 → ℤ) :
    MicrocodeEmbedding.embed bothBinding.ports Label.append
      (NativeMappedAppend.cfg pc source word pos).denote (frame source framePos) =
      cfg (.append pc) source word pos := by
  unfold MicrocodeEmbedding.embed NativeMappedAppend.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus2 Microcode.focus cfg frame
  simp only [← bothBinding.values_eq_extend]
  congr 2
  funext t
  fin_cases t <;> rfl

theorem embed_seal (pc : NativeSealBack.Label) (source word : Tape Bool)
    (pos : Fin 2 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports Label.seal
      (NativeSealBack.cfg pc word (fun _ => z)).denote (frame source pos) =
      cfg (.seal pc) source word (Function.update pos 1 z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus cfg frame
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext t <;> fin_cases t <;> rfl

abbrev Trace (f : Bool → Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program f)) (NativeMicrocode.Active (program f))

theorem jump_trace (f : Bool → Bool) (pc next : Label) (source target : Tape Bool)
    (pos : Fin 2 → ℤ) (h : program f pc = .jump next) :
    Trace f 1 (cfg pc source target pos) (cfg next source target pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem initialize_call (f : Bool → Bool) (source : Tape Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2, Trace f t (cfg (.init (.erase 0)) source ⟨[], []⟩ pos)
      (cfg (.init .done) source BinaryCarry.preparedOutput pos) := by
  obtain ⟨t, ht, htr⟩ := NativeBuffer.initialize_trace (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports Label.init
    NativeBuffer.program (program f) (frame source pos) (init_code f) htr
  exact ⟨t, ht, by simpa only [embed_init, Function.update_eq_self] using he⟩

theorem append_call (f : Bool → Bool) (xs : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 4*xs.length+5,
      Trace f t (cfg (.append 0) (Counter.marked xs) BinaryCarry.preparedOutput pos)
        (cfg (.append 7) (Counter.marked xs) (NativeSealBack.openWord (xs.map f))
          (NativeMappedAppend.finalPositions pos xs.length)) := by
  obtain ⟨t, ht, htr⟩ := NativeMappedAppend.append_trace f xs [.start] pos
  have he := MicrocodeEmbedding.trace_embed bothBinding.ports Label.append
    (Microcode.MappedAppendFamily.program f) (program f) (frame (Counter.marked xs) pos)
      (append_code f) htr
  refine ⟨t, ht, ?_⟩
  simpa only [embed_append, NativeSealBack.openWord, BinaryCarry.preparedOutput] using he

theorem seal_call (f : Bool → Bool) (source : Tape Bool) (xs : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*xs.length+5,
      Trace f t (cfg (.seal .seal) source (NativeSealBack.openWord xs) pos)
        (cfg (.seal .done) source (Counter.marked xs) (Function.update pos 1 (pos 1-xs.length))) := by
  obtain ⟨t, ht, htr⟩ := NativeSealBack.seal_trace xs (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports Label.seal
    NativeSealBack.program (program f) (frame source pos) (fun pc _ _ => seal_code f pc) htr
  exact ⟨t, ht, by simpa only [embed_seal, Function.update_eq_self] using he⟩

theorem copy_trace (f : Bool → Bool) (xs : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 6*xs.length+14,
      Trace f t (cfg (.init (.erase 0)) (Counter.marked xs) ⟨[], []⟩ pos)
        (cfg (.seal .done) (Counter.marked xs) (Counter.marked (xs.map f)) pos) := by
  obtain ⟨a, ha, hinit⟩ := initialize_call f (Counter.marked xs) pos
  have j1 := jump_trace f (.init .done) (.append 0) (Counter.marked xs)
    BinaryCarry.preparedOutput pos rfl
  obtain ⟨b, hb, happ⟩ := append_call f xs pos
  have j2 := jump_trace f (.append 7) (.seal .seal) (Counter.marked xs)
    (NativeSealBack.openWord (xs.map f)) (NativeMappedAppend.finalPositions pos xs.length) rfl
  obtain ⟨c, hc, hseal⟩ := seal_call f (Counter.marked xs) (xs.map f)
    (NativeMappedAppend.finalPositions pos xs.length)
  have hpos : Function.update (NativeMappedAppend.finalPositions pos xs.length) 1
      (NativeMappedAppend.finalPositions pos xs.length 1-(xs.map f).length) = pos := by
    funext t; fin_cases t <;> simp [NativeMappedAppend.finalPositions]
  rw [hpos] at hseal
  refine ⟨a+(1+(b+(1+c))), ?_, NativeCountedLoop.trace_trans hinit
    (NativeCountedLoop.trace_trans j1 (NativeCountedLoop.trace_trans happ
      (NativeCountedLoop.trace_trans j2 hseal)))⟩
  simp only [List.length_map] at hc
  omega

noncomputable def nativeEncoding :=
  NativeMicrocode.initialEncoding (T := Fin 2) (Label.init (.erase 0))
noncomputable def nativeMachine (f : Bool → Bool) := NativeMicrocode.machine nativeEncoding (program f)

theorem fixed_resources (f : Bool → Bool) : (nativeMachine f).k = 2 ∧
    (nativeMachine f).g+1 = 5 ∧ (nativeMachine f).q+1 = 24 ∧
    nativeEncoding.label (.init (.erase 0)) = 0 := by
  refine ⟨rfl, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label - 1 + 1 = 24
  decide +kernel

theorem native_copy (f : Bool → Bool) (xs : List Bool) (pos : Fin 2 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*xs.length+14,
      Transpose.stepN (nativeMachine f) input t
        ((cfg (.init (.erase 0)) (Counter.marked xs) ⟨[], []⟩ pos).denote
          nativeEncoding (program f) inputPos outRev) =
        some ((cfg (.seal .done) (Counter.marked xs) (Counter.marked (xs.map f)) pos).denote
          nativeEncoding (program f) inputPos outRev) ∧
      Transpose.step (nativeMachine f) input
        ((cfg (.seal .done) (Counter.marked xs) (Counter.marked (xs.map f)) pos).denote
          nativeEncoding (program f) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := copy_trace f xs pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding (program f) input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding (program f) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Fin 2 ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (f : Bool → Bool)
    (hc : ∀ pc, program f pc ≠ .halt → program f pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program f pc))
    (xs : List Bool) (pos : Fin 2 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*xs.length+14,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.init (.erase 0)) (Counter.marked xs) ⟨[], []⟩ pos) frame).denote
            encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.seal .done) (Counter.marked xs) (Counter.marked (xs.map f)) pos) frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := copy_trace f xs pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program f) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeMappedCopy
