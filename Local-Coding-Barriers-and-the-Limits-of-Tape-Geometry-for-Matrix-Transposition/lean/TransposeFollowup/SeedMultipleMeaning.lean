import TransposeFollowup.NativeMappedCopy
import TransposeFollowup.RowStreamBudget
import TransposeFollowup.FixedMultipleRun

/-! The specification of a paid common-width word: map the source bits and
append one source-length block of zeroes plus a fixed machine constant. -/

namespace TransposeFollowup.PaddedWord

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
set_option autoImplicit false

def word (C : ℕ) (f : Bool → Bool) (xs : List Bool) : List Bool :=
  xs.map f ++ List.replicate (xs.length+C) false

theorem word_length (C : ℕ) (f : Bool → Bool) (xs : List Bool) :
    (word C f xs).length = 2*xs.length+C := by simp [word]; omega

theorem value_zeroes (k : ℕ) : Counter.value (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Counter.value, List.replicate_succ, ih]

theorem value_append_zeroes (xs : List Bool) (k : ℕ) :
    Counter.value (xs ++ List.replicate k false) = Counter.value xs := by
  induction xs with
  | nil => exact value_zeroes k
  | cons b xs ih => cases b <;> simp [Counter.value, ih]

theorem word_value (C : ℕ) (f : Bool → Bool) (xs : List Bool) :
    Counter.value (word C f xs) = Counter.value (xs.map f) := value_append_zeroes _ _

theorem identity_value (C : ℕ) (xs : List Bool) :
    Counter.value (word C id xs) = Counter.value xs := by simp [word_value]

theorem zero_word (C : ℕ) (xs : List Bool) :
    word C (fun _ => false) xs = List.replicate (2*xs.length+C) false := by
  simp [word, two_mul, Nat.add_assoc]

theorem open_append_zero (xs : List Bool) :
    ((NativeSealBack.openWord xs).write (.data false)).moveRight =
      NativeSealBack.openWord (xs ++ [false]) := by
  simp [NativeSealBack.openWord, Tape.write, Tape.moveRight, Tape.read, symbols,
    List.reverse_append]

theorem open_append (xs ys : List Bool) :
    (symbols ys).reverse ++ (NativeSealBack.openWord xs).left =
      (NativeSealBack.openWord (xs ++ ys)).left := by
  simp [NativeSealBack.openWord, symbols, List.reverse_append, List.append_assoc]

theorem positions_add (pos : Fin 2 → ℤ) (a b : ℕ) :
    NativeMappedAppend.finalPositions (NativeMappedAppend.finalPositions pos a) b =
      NativeMappedAppend.finalPositions pos (a+b) := by
  funext t
  fin_cases t <;> simp [NativeMappedAppend.finalPositions, add_assoc]

theorem positions_zero (pos : Fin 2 → ℤ) : NativeMappedAppend.finalPositions pos 0 = pos := by
  funext t
  simp [NativeMappedAppend.finalPositions]

end TransposeFollowup.PaddedWord


/-! C is fixed when the finite machine is chosen. Its tail states each
perform one real zero write; the source length is obtained by two scans. -/

namespace TransposeFollowup.PaddedWord

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeMappedCopy (targetBinding bothBinding bank frame)
set_option autoImplicit false

inductive Label (C : ℕ)
  | init (pc : NativeBuffer.Label)
  | append (zero : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | fill (pc : Fin (C+1))
  | seal (pc : NativeSealBack.Label)
  deriving DecidableEq, Fintype

def mapFor (f : Bool → Bool) (zero : Bool) : Bool → Bool := if zero then (fun _ => false) else f

def program (C : ℕ) (f : Bool → Bool) : Microcode.Program (Fin 2) (Label C)
  | .init .done => .jump (.append false 0)
  | .init pc => targetBinding.instruction Label.init (NativeBuffer.program pc)
  | .append zero pc => if pc = 7 then
      if zero then .jump (.fill ⟨C, Nat.lt_succ_self C⟩) else .jump (.append true 0)
      else bothBinding.instruction (Label.append zero) (Microcode.MappedAppendFamily.program (mapFor f zero) pc)
  | .fill pc => if h : pc.val = 0 then .jump (.seal .seal)
      else .act (Microcode.single 1 ⟨some (.data false), .right⟩)
        (.fill ⟨pc.val-1, by omega⟩)
  | .seal pc => targetBinding.instruction Label.seal (NativeSealBack.program pc)

theorem init_code (C : ℕ) (f : Bool → Bool) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program C f (.init pc) = MicrocodeEmbedding.instruction targetBinding.ports
      Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program, NativeBuffer.program, FinitePortBinding.instruction_eq]

theorem append_code (C : ℕ) (f : Bool → Bool) (zero : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program (mapFor f zero) pc ≠ .halt)
    (_ : Microcode.MappedAppendFamily.program (mapFor f zero) pc ≠ .reject) :
    program C f (.append zero pc) = MicrocodeEmbedding.instruction bothBinding.ports
      (Label.append zero) (Microcode.MappedAppendFamily.program (mapFor f zero) pc) := by
  have hp : pc ≠ 7 := by intro h; subst pc; exact hh rfl
  simp [program, hp, FinitePortBinding.instruction_eq]

theorem seal_code (C : ℕ) (f : Bool → Bool) (pc : NativeSealBack.Label) :
    program C f (.seal pc) = MicrocodeEmbedding.instruction targetBinding.ports
      Label.seal (NativeSealBack.program pc) := targetBinding.instruction_eq _ _

def cfg {C : ℕ} (pc : Label C) (source target : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeMicrocode.Config (Fin 2) (Label C) :=
  ⟨⟨pc, fun t => (bank source target t).denote⟩, pos⟩

def zipperCfg {C : ℕ} (pc : Label C) (source target : Tape Bool) (pos : Fin 2 → ℤ) :
    NativeZipper.Config (Fin 2) (Label C) := ⟨⟨pc, bank source target⟩, pos⟩

def labelEquiv (C : ℕ) : Label C ≃
    NativeBuffer.Label ⊕ (Bool × Microcode.MappedAppendFamily.Label) ⊕ Fin (C+1) ⊕ NativeSealBack.Label where
  toFun
    | .init p => .inl p
    | .append b p => .inr (.inl (b,p))
    | .fill p => .inr (.inr (.inl p))
    | .seal p => .inr (.inr (.inr p))
  invFun
    | .inl p => .init p
    | .inr (.inl (b,p)) => .append b p
    | .inr (.inr (.inl p)) => .fill p
    | .inr (.inr (.inr p)) => .seal p
  left_inv := by intro p; cases p <;> rfl
  right_inv := by rintro (p | ⟨b,p⟩ | p | p) <;> rfl

theorem label_card (C : ℕ) : Fintype.card (Label C) = C+33 := by
  have h := Fintype.card_congr (labelEquiv C)
  have hb : Fintype.card NativeBuffer.Label = 10 := by decide +kernel
  have hs : Fintype.card NativeSealBack.Label = 6 := by decide +kernel
  simpa [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hb, hs,
    Microcode.MappedAppendFamily.Label, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

noncomputable def nativeEncoding (C : ℕ) :=
  NativeMicrocode.initialEncoding (T := Fin 2) (Label.init (C := C) (.erase 0))
noncomputable def nativeMachine (C : ℕ) (f : Bool → Bool) :=
  NativeMicrocode.machine (nativeEncoding C) (program C f)

theorem fixed_resources (C : ℕ) (f : Bool → Bool) : (nativeMachine C f).k = 2 ∧
    (nativeMachine C f).g+1 = 5 ∧ (nativeMachine C f).q+1 = C+33 ∧
    (nativeEncoding C).label (.init (.erase 0)) = 0 := by
  refine ⟨rfl, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label C)-1+1 = C+33
  rw [label_card]
  omega

end TransposeFollowup.PaddedWord


/-! Bind the existing setup/append/rewind routines to the padding caller,
and verify each of the fixed tail's zero writes as a native transition. -/

namespace TransposeFollowup.PaddedWord

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
open NativeMappedCopy (targetBinding bothBinding bank frame)
set_option autoImplicit false

theorem embed_init {C : ℕ} (pc : NativeBuffer.Label) (source word : Tape Bool)
    (pos : Fin 2 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports (Label.init (C := C))
      (NativeBuffer.cfg pc word (fun _ => z)).denote (frame source pos) =
      cfg (.init pc) source word (Function.update pos 1 z) := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus cfg frame
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext t <;> fin_cases t <;> rfl

theorem embed_append {C : ℕ} (zero : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (source word : Tape Bool) (pos framePos : Fin 2 → ℤ) :
    MicrocodeEmbedding.embed bothBinding.ports (Label.append (C := C) zero)
      (NativeMappedAppend.cfg pc source word pos).denote (frame source framePos) =
      cfg (.append zero pc) source word pos := by
  unfold MicrocodeEmbedding.embed NativeMappedAppend.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus2 Microcode.focus cfg frame
  simp only [← bothBinding.values_eq_extend]
  congr 2
  funext t
  fin_cases t <;> rfl

theorem embed_seal {C : ℕ} (pc : NativeSealBack.Label) (source word : Tape Bool)
    (pos : Fin 2 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports (Label.seal (C := C))
      (NativeSealBack.cfg pc word (fun _ => z)).denote (frame source pos) =
      cfg (.seal pc) source word (Function.update pos 1 z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus cfg frame
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext t <;> fin_cases t <;> rfl

abbrev Trace (C : ℕ) (f : Bool → Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program C f)) (NativeMicrocode.Active (program C f))

theorem jump_trace (C : ℕ) (f : Bool → Bool) (pc next : Label C) (source target : Tape Bool)
    (pos : Fin 2 → ℤ) (h : program C f pc = .jump next) :
    Trace C f 1 (cfg pc source target pos) (cfg next source target pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem initialize_call (C : ℕ) (f : Bool → Bool) (source : Tape Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2, Trace C f t (cfg (.init (.erase 0)) source ⟨[], []⟩ pos)
      (cfg (.init .done) source (NativeSealBack.openWord []) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeBuffer.initialize_trace (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports Label.init
    NativeBuffer.program (program C f) (frame source pos) (init_code C f) htr
  exact ⟨t, ht, by simpa [embed_init, Function.update_eq_self,
    NativeSealBack.openWord, BinaryCarry.preparedOutput, symbols] using he⟩

theorem append_call (C : ℕ) (f : Bool → Bool) (zero : Bool) (xs pre : List Bool)
    (pos : Fin 2 → ℤ) :
    ∃ t ≤ 4*xs.length+5,
      Trace C f t (cfg (.append zero 0) (Counter.marked xs) (NativeSealBack.openWord pre) pos)
        (cfg (.append zero 7) (Counter.marked xs) (NativeSealBack.openWord (pre ++ xs.map (mapFor f zero)))
          (NativeMappedAppend.finalPositions pos xs.length)) := by
  obtain ⟨t, ht, htr⟩ := NativeMappedAppend.append_trace (mapFor f zero) xs
    (NativeSealBack.openWord pre).left pos
  have he := MicrocodeEmbedding.trace_embed bothBinding.ports (Label.append zero)
    (Microcode.MappedAppendFamily.program (mapFor f zero)) (program C f)
    (frame (Counter.marked xs) pos) (append_code C f zero) htr
  have hout : (⟨(symbols (xs.map (mapFor f zero))).reverse ++ (NativeSealBack.openWord pre).left, []⟩ : Tape Bool) =
      NativeSealBack.openWord (pre ++ xs.map (mapFor f zero)) := by
    congr 1
    exact open_append pre _
  rw [hout] at he
  exact ⟨t, ht, by simpa only [embed_append, NativeSealBack.openWord] using he⟩

theorem seal_call (C : ℕ) (f : Bool → Bool) (source : Tape Bool) (xs : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*xs.length+5,
      Trace C f t (cfg (.seal .seal) source (NativeSealBack.openWord xs) pos)
        (cfg (.seal .done) source (Counter.marked xs) (Function.update pos 1 (pos 1-xs.length))) := by
  obtain ⟨t, ht, htr⟩ := NativeSealBack.seal_trace xs (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports Label.seal
    NativeSealBack.program (program C f) (frame source pos) (fun pc _ _ => seal_code C f pc) htr
  exact ⟨t, ht, by simpa only [embed_seal, Function.update_eq_self] using he⟩

theorem write_step (C : ℕ) (f : Bool → Bool) (pc next : Label C) (source : Tape Bool)
    (pre : List Bool) (pos : Fin 2 → ℤ)
    (h : program C f pc = .act (Microcode.single 1 ⟨some (.data false), .right⟩) next) :
    NativeZipper.step (program C f) (zipperCfg pc source (NativeSealBack.openWord pre) pos) =
      zipperCfg next source (NativeSealBack.openWord (pre ++ [false]))
        (NativeMappedAppend.finalPositions pos 1) := by
  simp only [NativeZipper.step, Microcode.step, zipperCfg, h]
  congr 2
  · funext t
    fin_cases t
    · rfl
    · exact open_append_zero pre
  · funext t
    fin_cases t <;> simp [Microcode.single, NativeMicrocode.direction, Transpose.Dir.shift,
      NativeMappedAppend.finalPositions]

theorem write_trace (C : ℕ) (f : Bool → Bool) (pc next : Label C) (source : Tape Bool)
    (pre : List Bool) (pos : Fin 2 → ℤ)
    (h : program C f pc = .act (Microcode.single 1 ⟨some (.data false), .right⟩) next) :
    Trace C f 1 (cfg pc source (NativeSealBack.openWord pre) pos)
      (cfg next source (NativeSealBack.openWord (pre ++ [false]))
        (NativeMappedAppend.finalPositions pos 1)) := by
  have he := congrArg NativeZipper.Config.denote (write_step C f pc next source pre pos h)
  rw [NativeZipper.step_denote] at he
  change NativeMicrocode.step (program C f) (cfg pc source (NativeSealBack.openWord pre) pos) =
    cfg next source (NativeSealBack.openWord (pre ++ [false]))
      (NativeMappedAppend.finalPositions pos 1) at he
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active, cfg, h]
  · rw [he]
    exact .refl _

theorem fill_trace (C : ℕ) (f : Bool → Bool) (k : ℕ) (hk : k ≤ C)
    (source : Tape Bool) (pre : List Bool) (pos : Fin 2 → ℤ) :
    Trace C f (k+1) (cfg (.fill ⟨k, by omega⟩) source (NativeSealBack.openWord pre) pos)
      (cfg (.seal .seal) source (NativeSealBack.openWord (pre ++ List.replicate k false))
        (NativeMappedAppend.finalPositions pos k)) := by
  induction k generalizing pre pos with
  | zero =>
    simpa only [List.replicate_zero, List.append_nil, positions_zero] using
      jump_trace C f (.fill ⟨0, by omega⟩) (.seal .seal) source (NativeSealBack.openWord pre) pos
        (by simp [program])
  | succ k ih =>
    have hw := write_trace C f (.fill ⟨k+1, by omega⟩) (.fill ⟨k, by omega⟩) source pre pos
      (by simp [program])
    have he := NativeCountedLoop.trace_trans hw
      (ih (by omega) (pre ++ [false]) (NativeMappedAppend.finalPositions pos 1))
    simpa [List.replicate_succ, List.append_assoc, positions_add, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using he

end TransposeFollowup.PaddedWord


/-! Exact blank-target construction of a word of width 2l+C. Every scan,
tail write, marker, linking jump and rewind is included in the native bound. -/

namespace TransposeFollowup.PaddedWord

open FixedTapeCompiler
open CopyMachine (Sym Tape symbols)
set_option autoImplicit false

theorem padded_trace (C : ℕ) (f : Bool → Bool) (xs : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 12*xs.length+3*C+21,
      Trace C f t (cfg (.init (.erase 0)) (Counter.marked xs) ⟨[], []⟩ pos)
        (cfg (.seal .done) (Counter.marked xs) (Counter.marked (word C f xs)) pos) := by
  let u := xs.map f
  let v := u ++ List.replicate xs.length false
  let pos₁ := NativeMappedAppend.finalPositions pos xs.length
  let pos₂ := NativeMappedAppend.finalPositions pos₁ xs.length
  let pos₃ := NativeMappedAppend.finalPositions pos₂ C
  obtain ⟨a, ha, hi⟩ := initialize_call C f (Counter.marked xs) pos
  have j1 := jump_trace C f (.init .done) (.append false 0) (Counter.marked xs)
    (NativeSealBack.openWord []) pos rfl
  obtain ⟨b, hb, h1⟩ := append_call C f false xs [] pos
  have h1' : Trace C f b (cfg (.append false 0) (Counter.marked xs) (NativeSealBack.openWord []) pos)
      (cfg (.append false 7) (Counter.marked xs) (NativeSealBack.openWord u) pos₁) := by
    simpa [mapFor, u, pos₁] using h1
  have j2 := jump_trace C f (.append false 7) (.append true 0) (Counter.marked xs)
    (NativeSealBack.openWord u) pos₁ rfl
  obtain ⟨c, hc, h2⟩ := append_call C f true xs u pos₁
  have h2' : Trace C f c (cfg (.append true 0) (Counter.marked xs) (NativeSealBack.openWord u) pos₁)
      (cfg (.append true 7) (Counter.marked xs) (NativeSealBack.openWord v) pos₂) := by
    simpa [mapFor, v, pos₂] using h2
  have j3 := jump_trace C f (.append true 7) (.fill ⟨C, Nat.lt_succ_self C⟩)
    (Counter.marked xs) (NativeSealBack.openWord v) pos₂ rfl
  have htail := fill_trace C f C le_rfl (Counter.marked xs) v pos₂
  have hw : v ++ List.replicate C false = word C f xs := by
    simp only [v, u, word, List.replicate_add, List.append_assoc]
  rw [hw] at htail
  obtain ⟨d, hd, hs⟩ := seal_call C f (Counter.marked xs) (word C f xs) pos₃
  have hp : Function.update pos₃ 1 (pos₃ 1-(word C f xs).length) = pos := by
    funext t
    fin_cases t <;> simp [pos₃, pos₂, pos₁, NativeMappedAppend.finalPositions, word_length]
    all_goals omega
  rw [hp] at hs
  refine ⟨a+(1+(b+(1+(c+(1+((C+1)+d)))))), ?_,
    NativeCountedLoop.trace_trans hi (NativeCountedLoop.trace_trans j1
      (NativeCountedLoop.trace_trans h1' (NativeCountedLoop.trace_trans j2
        (NativeCountedLoop.trace_trans h2' (NativeCountedLoop.trace_trans j3
          (NativeCountedLoop.trace_trans htail hs))))))⟩
  rw [word_length] at hd
  omega

theorem native_padded (C : ℕ) (f : Bool → Bool) (xs : List Bool) (pos : Fin 2 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 12*xs.length+3*C+21,
      Transpose.stepN (nativeMachine C f) input t
        ((cfg (.init (.erase 0)) (Counter.marked xs) ⟨[], []⟩ pos).denote
          (nativeEncoding C) (program C f) inputPos outRev) =
        some ((cfg (.seal .done) (Counter.marked xs) (Counter.marked (word C f xs)) pos).denote
          (nativeEncoding C) (program C f) inputPos outRev) ∧
      Transpose.step (nativeMachine C f) input
        ((cfg (.seal .done) (Counter.marked xs) (Counter.marked (word C f xs)) pos).denote
          (nativeEncoding C) (program C f) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := padded_trace C f xs pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding C) (program C f) input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding C) (program C f) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (C : ℕ)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Fin 2 ↪ U) (labels : Label C → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (f : Bool → Bool)
    (hc : ∀ pc, program C f pc ≠ .halt → program C f pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program C f pc))
    (xs : List Bool) (pos : Fin 2 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 12*xs.length+3*C+21,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.init (.erase 0)) (Counter.marked xs) ⟨[], []⟩ pos) frame).denote
            encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.seal .done) (Counter.marked xs) (Counter.marked (word C f xs)) pos) frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := padded_trace C f xs pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program C f) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.PaddedWord


/-! The physically constructed common width is sufficient for the exact
row computation. Larger words are allowed; no free canonical-width conversion
is assumed. A logarithmic source-length hypothesis is explicit in budgets. -/

namespace TransposeFollowup

open FixedTapeCompiler
set_option autoImplicit false

namespace RowCell

theorem comparisonFits_wide (F : RationalMobius) {n m : ℕ} (hm : F.componentWidth n ≤ m)
    (i : Fin n) (j : ℕ) (hj : j ≤ n) (w : Words)
    (h : Represents m w (F.componentRow i) j) : ComparisonFits m w := by
  have hf := F.componentRow_comparison_fit i j hj
  have hp : 2^F.componentWidth n ≤ 2^m := Nat.pow_le_pow_right (by decide) hm
  dsimp only at hf
  intro second
  have hv := compare_values m w _ j h second
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  cases second <;> constructor
  all_goals
    apply lt_of_lt_of_le _ hp
    apply hf <;> simp [compareLeft, compareRight]

theorem updateFits_wide (F : RationalMobius) {n m : ℕ} (hm : F.componentWidth n ≤ m)
    (i : Fin n) (j : ℕ) (hj : j < n) (w : Words)
    (h : Represents m w (F.componentRow i) j) : UpdateFits m w := by
  let r := F.componentRow i
  have hf := F.componentRow_comparison_fit i (j+1) (by omega)
  have hp : 2^F.componentWidth n ≤ 2^m := Nat.pow_le_pow_right (by decide) hm
  dsimp only at hf
  rintro ⟨side, sign⟩
  have hmass : (pairAt r (j+1) .crossing side).mass < 2^F.componentWidth n := by
    cases side
    · exact hf _ (by simp [pairAt, r]) _ (by simp [pairAt, r])
    · exact hf _ (by simp [pairAt, r]) _ (by simp [pairAt, r])
  have hc := ((component_le_mass (pairAt r (j+1) .crossing side) sign).trans_lt hmass).trans_le hp
  change expected r (j+1) (.crossing, side, sign) < _ at hc
  rw [expected_next] at hc
  simpa only [h.2 (.crossing, side, sign), h.2 (.delta, side, sign)] using hc

end RowCell

namespace RowStream

theorem flags_exact_wide (F : RationalMobius) {n m : ℕ} (hm : F.componentWidth n ≤ m)
    (i : Fin n) (k j : ℕ) (hj : j+k ≤ n) (w : RowCell.Words)
    (h : RowCell.Represents m w (F.componentRow i) j) :
    flags (rowGuard F i) k w = (List.range k).map (fun x => F.denseHit i (j+x)) := by
  induction k generalizing j w with
  | zero => rfl
  | succ k ih =>
    have hlt : j < n := by omega
    have hnext := RowCell.updateAll_represents m w _ j h (RowCell.updateFits_wide F hm i j hlt w h)
    rw [flags, show RowCell.answer (rowGuard F i) w = F.denseHit i j from
      (RowCell.answer_exact m w _ j h (RowCell.comparisonFits_wide F hm i j hlt.le w h)).trans
        (F.componentRow_hit i j),
      ih (j+1) (by omega) _ hnext, List.range_succ_eq_map]
    simp only [List.map_cons, Nat.add_zero, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    omega

theorem process_represents_wide (F : RationalMobius) {n m : ℕ} (hm : F.componentWidth n ≤ m)
    (i : Fin n) (k j : ℕ) (hj : j+k ≤ n) (s : State m)
    (h : RowCell.Represents m s.words (F.componentRow i) j) :
    RowCell.Represents m (process (rowGuard F i) k s).words (F.componentRow i) (j+k) := by
  induction k generalizing j s with
  | zero => exact h
  | succ k ih =>
    have hnext := RowCell.updateAll_represents m s.words _ j h
      (RowCell.updateFits_wide F hm i j (by omega) s.words h)
    have he := ih (j+1) (by omega) (advance (rowGuard F i) s) hnext
    simpa only [process, Nat.add_assoc, Nat.add_comm 1 k] using he

theorem process_row_written_wide (F : RationalMobius) {n m : ℕ} (hm : F.componentWidth n ≤ m)
    (i : Fin n) (s : State m) (h : RowCell.Represents m s.words (F.componentRow i) 0) :
    (process (rowGuard F i) n s).written = s.written ++ F.denseRow i := by
  rw [process_written, flags_exact_wide F hm i n 0 (by omega) s.words h, F.denseRow_eq_range]
  simp only [Nat.zero_add]

theorem native_rational_row_wide (F : RationalMobius) {n m : ℕ} (hm : F.componentWidth n ≤ m)
    (i : Fin n) (fuel : List Bool) (hf : Counter.value fuel = n) (s : State m)
    (h : RowCell.Represents m s.words (F.componentRow i) 0) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget m fuel,
      Transpose.stepN nativeMachine input t
        ((cfg (.counter (rowGuard F i) 0) fuel s pos).denote nativeEncoding program inputPos outRev) =
        some ((finishedCfg (.done (rowGuard F i)) (List.replicate fuel.length true)
          (process (rowGuard F i) n s) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((finishedCfg (.done (rowGuard F i)) (List.replicate fuel.length true)
          (process (rowGuard F i) n s) pos).denote nativeEncoding program inputPos outRev) = none ∧
      (process (rowGuard F i) n s).written = s.written ++ F.denseRow i ∧
      RowCell.Represents m (process (rowGuard F i) n s).words (F.componentRow i) n := by
  obtain ⟨t, ht, hrun, hhalt⟩ := native_row (rowGuard F i) fuel s pos input inputPos outRev
  rw [hf] at hrun hhalt
  exact ⟨t, ht, hrun, hhalt, process_row_written_wide F hm i s h,
    by simpa only [Nat.zero_add] using process_represents_wide F hm i n 0 (by omega) s h⟩

end RowStream

namespace PaddedWord

def commonConstant (F : RationalMobius) : ℕ := (F.integerOperandConstant^2).size+4

theorem dimension_size_bound (xs : List Bool) : (Counter.value xs+1).size ≤ xs.length+1 := by
  have hn : Counter.value xs < 2^xs.length := by
    rw [NativeCounter.word_value]
    exact BinaryCarry.value_lt xs
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < 2^xs.length := by positivity
  omega

theorem common_width_sufficient (F : RationalMobius) (xs : List Bool) :
    F.componentWidth (Counter.value xs) ≤ (word (commonConstant F) id xs).length := by
  have h := dimension_size_bound xs
  rw [word_length]
  unfold RationalMobius.componentWidth commonConstant
  omega

theorem common_value (F : RationalMobius) (xs : List Bool) :
    Counter.value (word (commonConstant F) id xs) = Counter.value xs := identity_value _ _

theorem common_zero (F : RationalMobius) (xs : List Bool) :
    word (commonConstant F) (fun _ => false) xs =
      List.replicate (word (commonConstant F) id xs).length false := by
  rw [zero_word, word_length]

theorem padding_total_budget (F : RationalMobius) (n : ℕ) (xs : List Bool) (hn : 1 ≤ n)
    (hl : xs.length ≤ (n+1).size) :
    n*(n*(12*xs.length+3*commonConstant F+21)) ≤
      (6*(F.integerOperandConstant^2).size+138)*Transpose.inputLength n := by
  have h := dense_scan_budget (3*commonConstant F+21) 12 n hn
  calc
    _ ≤ n*(n*((3*commonConstant F+21)+12*(n+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      omega
    _ ≤ _ := by
      convert h using 1
      unfold commonConstant
      ring

theorem common_row_total_budget (F : RationalMobius) (n : ℕ) (xs : List Bool) (hn : 1 ≤ n)
    (hv : Counter.value xs = n) (hl : xs.length ≤ (n+1).size) :
    n * RowStream.budget (word (commonConstant F) id xs).length (word (commonConstant F) id xs) ≤
      (244*(F.integerOperandConstant^2).size+3048)*Transpose.inputLength n := by
  have hm : (word (commonConstant F) id xs).length ≤
      (F.integerOperandConstant^2).size+4+2*(n+1).size := by
    rw [word_length]
    unfold commonConstant
    omega
  have h := RowStream.total_budget_le_input ((F.integerOperandConstant^2).size+4) 2 n
    (word (commonConstant F) id xs).length (word (commonConstant F) id xs) hn
    ((common_value F xs).trans hv) hm hm
  have he : 2*((122*((F.integerOperandConstant^2).size+4)+304)+3*(122*2)) =
      244*(F.integerOperandConstant^2).size+3048 := by omega
  simpa only [he] using h

end PaddedWord
end TransposeFollowup


/-! Literal contents of the arithmetic seed bank. The only supplied word is
the marked source; the subsequent controller pays for all seven work tapes. -/

namespace TransposeFollowup.ArithmeticSeed

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

def zeros (m : ℕ) : List Bool := List.replicate m false
def one (m : ℕ) : List Bool := true :: zeros (m-1)

theorem add_zeros (m : ℕ) : BinaryCarry.result false false (zeros m) (zeros m) =
    (zeros m, false) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simpa [zeros, List.replicate_succ, BinaryCarry.result, BinaryCarry.digit,
      BinaryCarry.carry, BinaryCarry.operandBit] using congrArg (fun r => (false :: r.1, r.2)) ih

theorem add_carry_zeros (m : ℕ) (hm : 0 < m) :
    BinaryCarry.result false true (zeros m) (zeros m) = (one m, false) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp only [zeros, List.replicate_succ, BinaryCarry.result]
  change (true :: (BinaryCarry.result false false (zeros k) (zeros k)).1,
    (BinaryCarry.result false false (zeros k) (zeros k)).2) = _
  rw [add_zeros]
  rfl

theorem one_length (m : ℕ) (hm : 0 < m) : (one m).length = m := by
  simp [one, zeros]
  omega

theorem one_value (m : ℕ) : Counter.value (one m) = 1 := by
  simp [one, zeros, Counter.value, PaddedWord.value_zeroes]

inductive Port | source | number | zeroA | zeroB | one | fuel | left | right
  deriving DecidableEq

instance : Fintype Port where
  elems := {.source, .number, .zeroA, .zeroB, .one, .fuel, .left, .right}
  complete := by intro p; cases p <;> simp

structure Bank where
  source : Tape Bool
  number : Tape Bool
  zeroA : Tape Bool
  zeroB : Tape Bool
  one : Tape Bool
  fuel : Tape Bool
  left : Tape Bool
  right : Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .source => s.source | .number => s.number | .zeroA => s.zeroA | .zeroB => s.zeroB
  | .one => s.one | .fuel => s.fuel | .left => s.left | .right => s.right

def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank :=
  match p with
  | .source => {s with source := w} | .number => {s with number := w}
  | .zeroA => {s with zeroA := w} | .zeroB => {s with zeroB := w}
  | .one => {s with one := w} | .fuel => {s with fuel := w}
  | .left => {s with left := w} | .right => {s with right := w}

def initial (xs : List Bool) : Bank :=
  ⟨Counter.marked xs, ⟨[], []⟩, ⟨[], []⟩, ⟨[], []⟩,
    ⟨[], []⟩, ⟨[], []⟩, ⟨[], []⟩, ⟨[], []⟩⟩

def ready (C : ℕ) (xs : List Bool) : Bank :=
  ⟨Counter.marked xs, Counter.marked (PaddedWord.word C id xs),
    Counter.marked (zeros (2*xs.length+C)), Counter.marked (zeros (2*xs.length+C)),
    Counter.marked (one (2*xs.length+C)), Counter.marked [true],
    BinaryCarry.preparedOutput, BinaryCarry.preparedOutput⟩

end TransposeFollowup.ArithmeticSeed


/-! Eight fixed tapes. Padding, copying, addition and buffer preparation
are reused by static wiring. The last two actions emit and seal one-bit fuel. -/

namespace TransposeFollowup.ArithmeticSeed

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

def padPort (zero : Bool) : Port := if zero then .zeroA else .number

def padBinding (zero : Bool) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![.source, padPort zero], by cases zero <;> decide +kernel⟩
  decode := fun p => if p = .source then some 0 else if p = padPort zero then some 1 else none
  decode_spec := by intro p i; cases zero <;> cases p <;> fin_cases i <;> decide +kernel

def copyBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![.number, .zeroB], by decide +kernel⟩
  decode := fun p => match p with | .number => some 0 | .zeroB => some 1 | _ => none
  decode_spec := by intro p i; cases p <;> fin_cases i <;> decide +kernel

def bufferPort : Fin 4 → Port := ![.one, .left, .right, .fuel]

def bufferBinding (i : Fin 4) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => bufferPort i, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p = bufferPort i then some 0 else none
  decode_spec := by intro p j; fin_cases i <;> cases p <;> fin_cases j <;> decide +kernel

def addBinding : FinitePortBinding (Fin 3) Port where
  ports := ⟨![.zeroA, .zeroB, .one], by decide +kernel⟩
  decode := fun p => match p with
    | .zeroA => some 0 | .zeroB => some 1 | .one => some 2 | _ => none
  decode_spec := by intro p i; cases p <;> fin_cases i <;> decide +kernel

inductive Label (C : ℕ)
  | pad (zero : Bool) (pc : PaddedWord.Label C)
  | copy (pc : NativeMappedCopy.Label)
  | init (i : Fin 4) (pc : NativeBuffer.Label)
  | add (pc : BinaryCarry.Label)
  | emit (sealBit : Bool)
  | done
  deriving DecidableEq, Fintype

def mapFor (zero : Bool) : Bool → Bool := if zero then (fun _ => false) else id

def afterInit {C : ℕ} (i : Fin 4) : Label C :=
  if i = 0 then .add (.scan false true)
  else if i = 1 then .init 2 (.erase 0)
  else if i = 2 then .init 3 (.erase 0) else .emit false

def program (C : ℕ) : Microcode.Program Port (Label C)
  | .pad false (.seal .done) => .jump (.pad true (.init (.erase 0)))
  | .pad true (.seal .done) => .jump (.copy (.init (.erase 0)))
  | .pad zero pc => (padBinding zero).instruction (Label.pad zero) (PaddedWord.program C (mapFor zero) pc)
  | .copy (.seal .done) => .jump (.init 0 (.erase 0))
  | .copy pc => copyBinding.instruction Label.copy (NativeMappedCopy.program (fun _ => false) pc)
  | .init i .done => .jump (afterInit i)
  | .init i pc => (bufferBinding i).instruction (Label.init i) (NativeBuffer.program pc)
  | .add (.done _) => .jump (.init 1 (.erase 0))
  | .add pc => addBinding.instruction Label.add (BinaryCarry.program pc)
  | .emit false => .act (Microcode.single .fuel ⟨some (.data true), .right⟩) (.emit true)
  | .emit true => .act (Microcode.single .fuel ⟨some .stop, .left⟩) .done
  | .done => .halt

theorem pad_code (C : ℕ) (zero : Bool) (pc : PaddedWord.Label C)
    (hh : PaddedWord.program C (mapFor zero) pc ≠ .halt)
    (_hr : PaddedWord.program C (mapFor zero) pc ≠ .reject) :
    program C (.pad zero pc) = MicrocodeEmbedding.instruction (padBinding zero).ports
      (Label.pad zero) (PaddedWord.program C (mapFor zero) pc) := by
  have hp : pc ≠ .seal .done := by intro h; subst pc; exact hh rfl
  cases zero <;> cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem copy_code (C : ℕ) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program (fun _ => false) pc ≠ .halt)
    (_hr : NativeMappedCopy.program (fun _ => false) pc ≠ .reject) :
    program C (.copy pc) = MicrocodeEmbedding.instruction copyBinding.ports
      Label.copy (NativeMappedCopy.program (fun _ => false) pc) := by
  have hp : pc ≠ .seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem init_code (C : ℕ) (i : Fin 4) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc ≠ .halt) (_ : NativeBuffer.program pc ≠ .reject) :
    program C (.init i pc) = MicrocodeEmbedding.instruction (bufferBinding i).ports
      (Label.init i) (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program, NativeBuffer.program, FinitePortBinding.instruction_eq]

theorem add_code (C : ℕ) (pc : BinaryCarry.Label)
    (hh : BinaryCarry.program pc ≠ .halt) (_ : BinaryCarry.program pc ≠ .reject) :
    program C (.add pc) = MicrocodeEmbedding.instruction addBinding.ports
      Label.add (BinaryCarry.program pc) := by
  cases pc <;> simp_all [program, BinaryCarry.program, FinitePortBinding.instruction_eq]

def cfg {C : ℕ} (pc : Label C) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label C) :=
  ⟨⟨pc, fun t => (s.tapes t).denote⟩, pos⟩
def zipperCfg {C : ℕ} (pc : Label C) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label C) :=
  ⟨⟨pc, s.tapes⟩, pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun t => (s.tapes t).denote, pos⟩

def labelEquiv (C : ℕ) : Label C ≃
    (Bool × PaddedWord.Label C) ⊕ NativeMappedCopy.Label ⊕
    (Fin 4 × NativeBuffer.Label) ⊕ BinaryCarry.Label ⊕ Bool ⊕ Unit where
  toFun
    | .pad z p => .inl (z,p)
    | .copy p => .inr (.inl p)
    | .init i p => .inr (.inr (.inl (i,p)))
    | .add p => .inr (.inr (.inr (.inl p)))
    | .emit b => .inr (.inr (.inr (.inr (.inl b))))
    | .done => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl (z,p) => .pad z p
    | .inr (.inl p) => .copy p
    | .inr (.inr (.inl (i,p))) => .init i p
    | .inr (.inr (.inr (.inl p))) => .add p
    | .inr (.inr (.inr (.inr (.inl b)))) => .emit b
    | .inr (.inr (.inr (.inr (.inr ())))) => .done
  left_inv := by intro p; cases p <;> rfl
  right_inv := by rintro (⟨z,p⟩ | p | ⟨i,p⟩ | p | b | ⟨⟩) <;> rfl

theorem label_card (C : ℕ) : Fintype.card (Label C) = 2*C+166 := by
  have h := Fintype.card_congr (labelEquiv C)
  have hb : Fintype.card NativeBuffer.Label = 10 := by decide +kernel
  have hc : Fintype.card NativeMappedCopy.Label = 24 := by decide +kernel
  have ha : Fintype.card BinaryCarry.Label = 33 := by decide +kernel
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_unit, PaddedWord.label_card, hb, hc, ha] at h
  omega

noncomputable def nativeEncoding (C : ℕ) :=
  NativeMicrocode.initialEncoding (T := Port) (Label.pad (C := C) false (.init (.erase 0)))
noncomputable def nativeMachine (C : ℕ) := NativeMicrocode.machine (nativeEncoding C) (program C)

theorem fixed_resources (C : ℕ) : (nativeMachine C).k = 8 ∧
    (nativeMachine C).g+1 = 5 ∧ (nativeMachine C).q+1 = 2*C+166 ∧
    (nativeEncoding C).label (.pad false (.init (.erase 0))) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 8
    decide +kernel
  · change Fintype.card (Label C)-1+1 = 2*C+166
    rw [label_card]
    omega

end TransposeFollowup.ArithmeticSeed


/-! Exact framed calls in the seed controller. Each call is embedded from
the existing native trace and preserves all ports outside its static wiring. -/

namespace TransposeFollowup.ArithmeticSeed

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_pad (C : ℕ) (zero : Bool) (pc : PaddedWord.Label C)
    (source target : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (padBinding zero).ports (Label.pad zero)
      (PaddedWord.cfg pc source target (fun i => pos ((padBinding zero).ports i))) (frame s pos) =
      cfg (.pad zero pc) (({s with source := source}).set (padPort zero) target) pos := by
  unfold MicrocodeEmbedding.embed PaddedWord.cfg cfg frame
  simp only [← (padBinding zero).values_eq_extend]
  cases zero <;> congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_copy (C : ℕ) (pc : NativeMappedCopy.Label)
    (source target : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports (Label.copy (C := C))
      (NativeMappedCopy.cfg pc source target (fun i => pos (copyBinding.ports i))) (frame s pos) =
      cfg (.copy pc) {s with number := source, zeroB := target} pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_init (C : ℕ) (i : Fin 4) (pc : NativeBuffer.Label)
    (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (bufferBinding i).ports (Label.init (C := C) i)
      (NativeBuffer.cfg pc word (fun _ => pos (bufferPort i))).denote (frame s pos) =
      cfg (.init i pc) (s.set (bufferPort i) word) pos := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (bufferBinding i).values_eq_extend]
  fin_cases i <;> congr 2 <;> funext t <;> cases t <;> rfl

theorem embed_add (C : ℕ) (pc : BinaryCarry.Label)
    (a b out : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports (Label.add (C := C))
      (BinaryCarry.cfg pc a b out (fun i => pos (addBinding.ports i))).denote (frame s pos) =
      cfg (.add pc) {s with zeroA := a, zeroB := b, one := out} pos := by
  unfold MicrocodeEmbedding.embed BinaryCarry.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext t <;> cases t <;> rfl

abbrev Trace (C : ℕ) :=
  OperationalTrace.Trace (NativeMicrocode.step (program C)) (NativeMicrocode.Active (program C))

theorem jump_trace (C : ℕ) (pc next : Label C) (s : Bank) (pos : Port → ℤ)
    (h : program C pc = .jump next) : Trace C 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem pad_call (C : ℕ) (zero : Bool) (xs : List Bool) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 12*xs.length+3*C+21,
      Trace C t
        (cfg (.pad zero (.init (.erase 0)))
          (({s with source := Counter.marked xs}).set (padPort zero) ⟨[], []⟩) pos)
        (cfg (.pad zero (.seal .done))
          (({s with source := Counter.marked xs}).set (padPort zero)
            (Counter.marked (PaddedWord.word C (mapFor zero) xs))) pos) := by
  obtain ⟨t, ht, htr⟩ := PaddedWord.padded_trace C (mapFor zero) xs
    (fun i => pos ((padBinding zero).ports i))
  have he := MicrocodeEmbedding.trace_embed (padBinding zero).ports (Label.pad zero)
    (PaddedWord.program C (mapFor zero)) (program C) (frame s pos) (pad_code C zero) htr
  exact ⟨t, ht, by simpa only [embed_pad] using he⟩

theorem copy_call (C : ℕ) (xs : List Bool) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 6*xs.length+14,
      Trace C t (cfg (.copy (.init (.erase 0)))
        {s with number := Counter.marked xs, zeroB := ⟨[], []⟩} pos)
        (cfg (.copy (.seal .done))
          {s with number := Counter.marked xs, zeroB := Counter.marked (zeros xs.length)} pos) := by
  obtain ⟨t, ht, htr⟩ := NativeMappedCopy.copy_trace (fun _ => false) xs
    (fun i => pos (copyBinding.ports i))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports (Label.copy (C := C))
    (NativeMappedCopy.program (fun _ => false)) (program C) (frame s pos) (copy_code C) htr
  refine ⟨t, ht, ?_⟩
  simpa only [embed_copy, List.map_const', zeros] using he

theorem init_call (C : ℕ) (i : Fin 4) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 2,
      Trace C t (cfg (.init i (.erase 0)) (s.set (bufferPort i) ⟨[], []⟩) pos)
        (cfg (.init i .done) (s.set (bufferPort i) BinaryCarry.preparedOutput) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeBuffer.initialize_trace (fun _ => pos (bufferPort i))
  have he := MicrocodeEmbedding.trace_embed (bufferBinding i).ports (Label.init (C := C) i)
    NativeBuffer.program (program C) (frame s pos) (init_code C i) htr
  exact ⟨t, ht, by simpa only [embed_init] using he⟩

theorem add_call (C m : ℕ) (hm : 0 < m) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 5*m+7,
      Trace C t (cfg (.add (.scan false true))
        {s with zeroA := Counter.marked (zeros m), zeroB := Counter.marked (zeros m), one := BinaryCarry.preparedOutput} pos)
        (cfg (.add (.done false))
          {s with zeroA := Counter.marked (zeros m), zeroB := Counter.marked (zeros m), one := Counter.marked (one m)} pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCarry.arithmetic_trace false true (zeros m) (zeros m) rfl
    (fun i => pos (addBinding.ports i))
  rw [add_carry_zeros m hm] at htr
  have he := MicrocodeEmbedding.trace_embed addBinding.ports (Label.add (C := C))
    BinaryCarry.program (program C) (frame s pos) (add_code C) htr
  exact ⟨t, by simpa [zeros] using ht, by simpa only
    [embed_add, Counter.marked, BinaryCarry.marked, BinaryCompare.marked] using he⟩

theorem fuel_run (C : ℕ) (s : Bank) (pos : Port → ℤ) :
    NativeZipper.run (program C) 2
      (zipperCfg (.emit false) {s with fuel := BinaryCarry.preparedOutput} pos) =
      zipperCfg .done {s with fuel := Counter.marked [true]} pos := by
  simp only [NativeZipper.run, OperationalTrace.run, NativeZipper.step, Microcode.step,
    program, zipperCfg, Microcode.Action.apply, Microcode.single,
    NativeMicrocode.direction, Transpose.Dir.shift]
  congr 2
  · funext t; cases t <;> rfl
  · funext t; cases t <;> simp

theorem fuel_trace (C : ℕ) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 2,
      Trace C t (cfg (.emit false) {s with fuel := BinaryCarry.preparedOutput} pos)
        (cfg .done {s with fuel := Counter.marked [true]} pos) :=
  NativeZipper.trace_of_run (program C) (fuel_run C s pos)

end TransposeFollowup.ArithmeticSeed


/-! Integrated initialization from a marked source and seven blank work
tapes. All eight call transfers, markers, fuel writes and head resets are paid. -/

namespace TransposeFollowup.ArithmeticSeed

open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def budget (C : ℕ) (xs : List Bool) : ℕ := 46*xs.length+17*C+81

theorem seed_trace (C : ℕ) (xs : List Bool) (hm : 0 < 2*xs.length+C) (pos : Port → ℤ) :
    ∃ t ≤ budget C xs,
      Trace C t (cfg (.pad false (.init (.erase 0))) (initial xs) pos)
        (cfg .done (ready C xs) pos) := by
  let m := 2*xs.length+C
  let s0 := initial xs
  let s1 := {s0 with number := Counter.marked (PaddedWord.word C id xs)}
  let s2 := {s1 with zeroA := Counter.marked (zeros m)}
  let s3 := {s2 with zeroB := Counter.marked (zeros m)}
  let s4 := {s3 with one := BinaryCarry.preparedOutput}
  let s5 := {s4 with one := Counter.marked (one m)}
  let s6 := {s5 with left := BinaryCarry.preparedOutput}
  let s7 := {s6 with right := BinaryCarry.preparedOutput}
  let s8 := {s7 with fuel := BinaryCarry.preparedOutput}
  obtain ⟨a, ha, h1⟩ := pad_call C false xs s0 pos
  change Trace C a (cfg (.pad false (.init (.erase 0))) s0 pos)
    (cfg (.pad false (.seal .done)) s1 pos) at h1
  have j1 := jump_trace C (.pad false (.seal .done)) (.pad true (.init (.erase 0))) s1 pos rfl
  obtain ⟨b, hb, h2⟩ := pad_call C true xs s1 pos
  simp only [mapFor, ite_true, PaddedWord.zero_word] at h2
  change Trace C b (cfg (.pad true (.init (.erase 0))) s1 pos)
    (cfg (.pad true (.seal .done)) s2 pos) at h2
  have j2 := jump_trace C (.pad true (.seal .done)) (.copy (.init (.erase 0))) s2 pos rfl
  obtain ⟨c, hc, h3⟩ := copy_call C (PaddedWord.word C id xs) s2 pos
  rw [PaddedWord.word_length] at hc h3
  change Trace C c (cfg (.copy (.init (.erase 0))) s2 pos)
    (cfg (.copy (.seal .done)) s3 pos) at h3
  have j3 := jump_trace C (.copy (.seal .done)) (.init 0 (.erase 0)) s3 pos rfl
  obtain ⟨d, hd, h4⟩ := init_call C 0 s3 pos
  change Trace C d (cfg (.init 0 (.erase 0)) s3 pos) (cfg (.init 0 .done) s4 pos) at h4
  have j4 := jump_trace C (.init 0 .done) (.add (.scan false true)) s4 pos rfl
  obtain ⟨e, he, h5⟩ := add_call C m hm s4 pos
  change Trace C e (cfg (.add (.scan false true)) s4 pos) (cfg (.add (.done false)) s5 pos) at h5
  have j5 := jump_trace C (.add (.done false)) (.init 1 (.erase 0)) s5 pos rfl
  obtain ⟨f, hf, h6⟩ := init_call C 1 s5 pos
  change Trace C f (cfg (.init 1 (.erase 0)) s5 pos) (cfg (.init 1 .done) s6 pos) at h6
  have j6 := jump_trace C (.init 1 .done) (.init 2 (.erase 0)) s6 pos rfl
  obtain ⟨g, hg, h7⟩ := init_call C 2 s6 pos
  change Trace C g (cfg (.init 2 (.erase 0)) s6 pos) (cfg (.init 2 .done) s7 pos) at h7
  have j7 := jump_trace C (.init 2 .done) (.init 3 (.erase 0)) s7 pos rfl
  obtain ⟨h, hh, h8⟩ := init_call C 3 s7 pos
  change Trace C h (cfg (.init 3 (.erase 0)) s7 pos) (cfg (.init 3 .done) s8 pos) at h8
  have j8 := jump_trace C (.init 3 .done) (.emit false) s8 pos rfl
  obtain ⟨u, hu, h9⟩ := fuel_trace C s8 pos
  change Trace C u (cfg (.emit false) s8 pos) (cfg .done (ready C xs) pos) at h9
  refine ⟨a+(1+(b+(1+(c+(1+(d+(1+(e+(1+(f+(1+(g+(1+(h+(1+u))))))))))))))), ?_,
    trace_trans h1 (trace_trans j1 (trace_trans h2 (trace_trans j2
      (trace_trans h3 (trace_trans j3 (trace_trans h4 (trace_trans j4
        (trace_trans h5 (trace_trans j5 (trace_trans h6 (trace_trans j6
          (trace_trans h7 (trace_trans j7 (trace_trans h8 (trace_trans j8 h9)))))))))))))))⟩
  dsimp [budget, m] at *
  omega

theorem native_seed (C : ℕ) (xs : List Bool) (hm : 0 < 2*xs.length+C) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget C xs,
      Transpose.stepN (nativeMachine C) input t
        ((cfg (.pad false (.init (.erase 0))) (initial xs) pos).denote
          (nativeEncoding C) (program C) inputPos outRev) =
        some ((cfg .done (ready C xs) pos).denote (nativeEncoding C) (program C) inputPos outRev) ∧
      Transpose.step (nativeMachine C) input
        ((cfg .done (ready C xs) pos).denote (nativeEncoding C) (program C) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := seed_trace C xs hm pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding C) (program C) input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding C) (program C) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (C : ℕ)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label C → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program C pc ≠ .halt → program C pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program C pc))
    (xs : List Bool) (hm : 0 < 2*xs.length+C) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget C xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.pad false (.init (.erase 0))) (initial xs) pos) frame).denote
            encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (ready C xs) pos) frame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := seed_trace C xs hm pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program C) target
    frame input inputPos outRev hc htr⟩

theorem common_seed_trace (F : RationalMobius) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ budget (PaddedWord.commonConstant F) xs,
      Trace (PaddedWord.commonConstant F) t
        (cfg (.pad false (.init (.erase 0))) (initial xs) pos)
        (cfg .done (ready (PaddedWord.commonConstant F) xs) pos) := by
  apply seed_trace
  unfold PaddedWord.commonConstant
  omega

theorem total_budget (F : RationalMobius) (n : ℕ) (xs : List Bool) (hn : 1 ≤ n)
    (hl : xs.length ≤ (n+1).size) :
    n*(n*budget (PaddedWord.commonConstant F) xs) ≤
      (34*(F.integerOperandConstant^2).size+574)*Transpose.inputLength n := by
  have h := dense_scan_budget (17*PaddedWord.commonConstant F+81) 46 n hn
  calc
    _ ≤ n*(n*((17*PaddedWord.commonConstant F+81)+46*(n+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      dsimp [budget]
      omega
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.ArithmeticSeed


/-! Compose paid seed initialization with a fixed multiplier on its zeroA
accumulator. Static wiring selects the dimension or the prepared unit word. -/

namespace TransposeFollowup.SeedMultiple

open FixedTapeCompiler
open ArithmeticSeed (Port Bank)
set_option autoImplicit false

def factorPort (constant : Bool) : Port := if constant then .one else .number

def seedBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

def multiplyPort (constant : Bool) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .zeroA | .factor => factorPort constant
  | .scratch => .left | .zero => .zeroB

def multiplyBinding (constant : Bool) : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨multiplyPort constant, by cases constant <;> decide +kernel⟩
  decode := fun p => if p = .fuel then some .fuel else
    if p = .zeroA then some .acc else if p = factorPort constant then some .factor else
    if p = .left then some .scratch else if p = .zeroB then some .zero else none
  decode_spec := by intro p t; cases constant <;> cases p <;> cases t <;> decide +kernel

inductive Label (C K : ℕ)
  | seed (pc : ArithmeticSeed.Label C)
  | multiply (pc : FixedMultiple.Label K)
  deriving DecidableEq, Fintype

def program (C K : ℕ) (constant : Bool) : Microcode.Program Port (Label C K)
  | .seed .done => .jump (.multiply (FixedMultiple.start K))
  | .seed pc => seedBinding.instruction Label.seed (ArithmeticSeed.program C pc)
  | .multiply pc => (multiplyBinding constant).instruction Label.multiply (FixedMultiple.program K pc)

theorem seed_code (C K : ℕ) (constant : Bool) (pc : ArithmeticSeed.Label C)
    (hh : ArithmeticSeed.program C pc ≠ .halt) (_ : ArithmeticSeed.program C pc ≠ .reject) :
    program C K constant (.seed pc) = MicrocodeEmbedding.instruction seedBinding.ports
      Label.seed (ArithmeticSeed.program C pc) := by
  have hp : pc ≠ .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem multiply_code (C K : ℕ) (constant : Bool) (pc : FixedMultiple.Label K) :
    program C K constant (.multiply pc) = MicrocodeEmbedding.instruction
      (multiplyBinding constant).ports Label.multiply (FixedMultiple.program K pc) :=
  (multiplyBinding constant).instruction_eq _ _

def cfg {C K : ℕ} (pc : Label C K) (b : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label C K) :=
  ⟨⟨pc, fun t => (b.tapes t).denote⟩, pos⟩
def zipperCfg {C K : ℕ} (pc : Label C K) (b : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label C K) :=
  ⟨⟨pc, b.tapes⟩, pos⟩

def factor (C : ℕ) (xs : List Bool) (constant : Bool) : List Bool :=
  if constant then ArithmeticSeed.one (2*xs.length+C) else PaddedWord.word C id xs

theorem factor_length (C : ℕ) (xs : List Bool) (constant : Bool) (hm : 0 < 2*xs.length+C) :
    (factor C xs constant).length = 2*xs.length+C := by
  cases constant <;> simp [factor, PaddedWord.word_length, ArithmeticSeed.one_length _ hm]

def output (C K : ℕ) (xs : List Bool) (constant : Bool) : List Bool :=
  RepeatedAdd.repeatWord (factor C xs constant) K (ArithmeticSeed.zeros (2*xs.length+C))

def final (C K : ℕ) (xs : List Bool) (constant : Bool) : Bank :=
  {ArithmeticSeed.ready C xs with zeroA := Counter.marked (output C K xs constant)}

def labelEquiv (C K : ℕ) : Label C K ≃ ArithmeticSeed.Label C ⊕ FixedMultiple.Label K where
  toFun | .seed p => .inl p | .multiply p => .inr p
  invFun | .inl p => .seed p | .inr p => .multiply p
  left_inv := by intro p; cases p <;> rfl
  right_inv := by rintro (p | p) <;> rfl

theorem label_card (C K : ℕ) : Fintype.card (Label C K) = 2*C+99*(K+1)+167 := by
  have h := Fintype.card_congr (labelEquiv C K)
  simp only [Fintype.card_sum, ArithmeticSeed.label_card, FixedMultiple.label_card] at h
  omega

noncomputable def nativeEncoding (C K : ℕ) :=
  NativeMicrocode.initialEncoding (T := Port) (Label.seed (K := K) (C := C) (.pad false (.init (.erase 0))))
noncomputable def nativeMachine (C K : ℕ) (constant : Bool) :=
  NativeMicrocode.machine (nativeEncoding C K) (program C K constant)

theorem fixed_resources (C K : ℕ) (constant : Bool) : (nativeMachine C K constant).k = 8 ∧
    (nativeMachine C K constant).g+1 = 5 ∧
    (nativeMachine C K constant).q+1 = 2*C+99*(K+1)+167 ∧
    (nativeEncoding C K).label (.seed (.pad false (.init (.erase 0)))) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 8
    decide +kernel
  · change Fintype.card (Label C K)-1+1 = 2*C+99*(K+1)+167
    rw [label_card]
    omega

end TransposeFollowup.SeedMultiple


/-! The complete controller starts with seven blank work tapes. Its only
supplied word is the marked dimension source. No coefficient word is assumed. -/

namespace TransposeFollowup.SeedMultiple

open FixedTapeCompiler
open ArithmeticSeed (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem embed_seed (C K : ℕ) (pc : ArithmeticSeed.Label C) (s : Bank)
    (pos : Port → ℤ) (frame : MicrocodeEmbedding.Frame Port) :
    MicrocodeEmbedding.embed seedBinding.ports (Label.seed (K := K))
      (ArithmeticSeed.cfg pc s pos) frame = cfg (.seed pc) s pos := by
  unfold MicrocodeEmbedding.embed ArithmeticSeed.cfg cfg
  simp only [← seedBinding.values_eq_extend]
  rfl

theorem embed_multiply (C K : ℕ) (constant : Bool) (pc : FixedMultiple.Label K)
    (b : RepeatedAdd.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (multiplyBinding constant).ports (Label.multiply (C := C))
      (FixedMultiple.cfg pc b (fun t => pos ((multiplyBinding constant).ports t)))
        (ArithmeticSeed.frame s pos) =
      cfg (.multiply pc)
        (({s with fuel := b.fuel, zeroA := b.acc, zeroB := b.zero, left := b.scratch}).set
          (factorPort constant) b.factor) pos := by
  unfold MicrocodeEmbedding.embed FixedMultiple.cfg cfg ArithmeticSeed.frame
  simp only [← (multiplyBinding constant).values_eq_extend]
  cases constant <;> congr 2 <;> funext t <;> cases t <;> rfl

abbrev Trace (C K : ℕ) (constant : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program C K constant))
    (NativeMicrocode.Active (program C K constant))

theorem seed_call (C K : ℕ) (constant : Bool) (xs : List Bool)
    (hm : 0 < 2*xs.length+C) (pos : Port → ℤ) :
    ∃ t ≤ ArithmeticSeed.budget C xs,
      Trace C K constant t
        (cfg (.seed (.pad false (.init (.erase 0)))) (ArithmeticSeed.initial xs) pos)
        (cfg (.seed .done) (ArithmeticSeed.ready C xs) pos) := by
  obtain ⟨t, ht, htr⟩ := ArithmeticSeed.seed_trace C xs hm pos
  have he := MicrocodeEmbedding.trace_embed seedBinding.ports (Label.seed (K := K))
    (ArithmeticSeed.program C) (program C K constant)
    (ArithmeticSeed.frame (ArithmeticSeed.initial xs) pos) (seed_code C K constant) htr
  exact ⟨t, ht, by simpa only [embed_seed] using he⟩

theorem multiply_call (C K : ℕ) (constant : Bool) (xs : List Bool)
    (hm : 0 < 2*xs.length+C) (pos : Port → ℤ) :
    ∃ t ≤ FixedMultiple.budget K (2*xs.length+C),
      Trace C K constant t
        (cfg (.multiply (FixedMultiple.start K)) (ArithmeticSeed.ready C xs) pos)
        (cfg (.multiply .done) (final C K xs constant) pos) := by
  have hl := factor_length C xs constant hm
  have hz : (ArithmeticSeed.zeros (2*xs.length+C)).length = (factor C xs constant).length := by
    simp [ArithmeticSeed.zeros, hl]
  obtain ⟨t, ht, htr⟩ := FixedMultiple.multiple_trace K (ArithmeticSeed.zeros (2*xs.length+C))
    (factor C xs constant) hz (fun t => pos ((multiplyBinding constant).ports t))
  have he := MicrocodeEmbedding.trace_embed (multiplyBinding constant).ports (Label.multiply (C := C))
    (FixedMultiple.program K) (program C K constant) (ArithmeticSeed.frame (ArithmeticSeed.ready C xs) pos)
    (fun pc _ _ => multiply_code C K constant pc) htr
  refine ⟨t, by simpa only [hl] using ht, ?_⟩
  simp only [embed_multiply, RepeatedAdd.ready, hl] at he
  cases constant <;>
    simpa [ArithmeticSeed.ready, ArithmeticSeed.Bank.set, ArithmeticSeed.zeros,
      factorPort, factor, final, output, Counter.marked, BinaryCarry.marked,
      BinaryCompare.marked] using he

theorem jump_trace (C K : ℕ) (constant : Bool) (s : Bank) (pos : Port → ℤ) :
    Trace C K constant 1 (cfg (.seed .done) s pos)
      (cfg (.multiply (FixedMultiple.start K)) s pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active, cfg, program]
  · change Trace C K constant 0
      (NativeMicrocode.step (program C K constant) (cfg (.seed .done) s pos)) _
    have he : NativeMicrocode.step (program C K constant) (cfg (.seed .done) s pos) =
        cfg (.multiply (FixedMultiple.start K)) s pos := by
      simp [NativeMicrocode.step, Microcode.actualStep, cfg, program]
    rw [he]
    exact .refl _

def budget (C K : ℕ) (xs : List Bool) : ℕ :=
  ArithmeticSeed.budget C xs + 1 + FixedMultiple.budget K (2*xs.length+C)

theorem complete_trace (C K : ℕ) (constant : Bool) (xs : List Bool)
    (hm : 0 < 2*xs.length+C) (pos : Port → ℤ) :
    ∃ t ≤ budget C K xs,
      Trace C K constant t
        (cfg (.seed (.pad false (.init (.erase 0)))) (ArithmeticSeed.initial xs) pos)
        (cfg (.multiply .done) (final C K xs constant) pos) := by
  obtain ⟨a, ha, hs⟩ := seed_call C K constant xs hm pos
  obtain ⟨b, hb, hm⟩ := multiply_call C K constant xs hm pos
  exact ⟨a+(1+b), by dsimp [budget]; omega,
    trace_trans hs (trace_trans (jump_trace C K constant _ pos) hm)⟩

theorem native_complete (C K : ℕ) (constant : Bool) (xs : List Bool)
    (hm : 0 < 2*xs.length+C) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget C K xs,
      Transpose.stepN (nativeMachine C K constant) input t
        ((cfg (.seed (.pad false (.init (.erase 0)))) (ArithmeticSeed.initial xs) pos).denote
          (nativeEncoding C K) (program C K constant) inputPos outRev) =
        some ((cfg (.multiply .done) (final C K xs constant) pos).denote
          (nativeEncoding C K) (program C K constant) inputPos outRev) ∧
      Transpose.step (nativeMachine C K constant) input
        ((cfg (.multiply .done) (final C K xs constant) pos).denote
          (nativeEncoding C K) (program C K constant) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := complete_trace C K constant xs hm pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding C K) (program C K constant)
    input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding C K) (program C K constant)
    input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (C K : ℕ) (constant : Bool)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label C K → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program C K constant pc ≠ .halt → program C K constant pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program C K constant pc))
    (xs : List Bool) (hm : 0 < 2*xs.length+C) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget C K xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.seed (.pad false (.init (.erase 0)))) (ArithmeticSeed.initial xs) pos) frame).denote
            encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.multiply .done) (final C K xs constant) pos) frame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := complete_trace C K constant xs hm pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program C K constant) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.SeedMultiple


/-! Numeric exactness and input-size budgets for the paid coefficient
controller. The common width prevents overflow for every K at most E squared. -/

namespace TransposeFollowup.SeedMultiple

open FixedTapeCompiler
open ArithmeticSeed (Port)
set_option autoImplicit false

theorem factor_value (C : ℕ) (xs : List Bool) (constant : Bool) :
    Counter.value (factor C xs constant) = if constant then 1 else Counter.value xs := by
  cases constant <;> simp [factor, ArithmeticSeed.one_value, PaddedWord.identity_value]

theorem output_length (C K : ℕ) (xs : List Bool) (constant : Bool)
    (hm : 0 < 2*xs.length+C) : (output C K xs constant).length = 2*xs.length+C := by
  have hl := factor_length C xs constant hm
  exact (RepeatedAdd.repeatWord_length _ K _ (by simp [ArithmeticSeed.zeros, hl])).trans hl

theorem output_value (C K : ℕ) (xs : List Bool) (constant : Bool)
    (hm : 0 < 2*xs.length+C) :
    Counter.value (output C K xs constant) =
      (K*(if constant then 1 else Counter.value xs)) % 2^(2*xs.length+C) := by
  have hl := factor_length C xs constant hm
  have h := RepeatedAdd.repeatWord_value (factor C xs constant) K
    (ArithmeticSeed.zeros (2*xs.length+C)) (by simp [ArithmeticSeed.zeros, hl])
  simpa only [← NativeCounter.word_value, ArithmeticSeed.zeros, PaddedWord.value_zeroes,
    Nat.zero_add, factor_value, hl, output] using h

theorem output_value_exact (C K : ℕ) (xs : List Bool) (constant : Bool)
    (hm : 0 < 2*xs.length+C)
    (hf : K*(if constant then 1 else Counter.value xs) < 2^(2*xs.length+C)) :
    Counter.value (output C K xs constant) = K*(if constant then 1 else Counter.value xs) := by
  rw [output_value C K xs constant hm, Nat.mod_eq_of_lt hf]

theorem common_small_multiple_fits (F : RationalMobius) (xs : List Bool) (K y : ℕ)
    (hK : K ≤ F.integerOperandConstant^2) (hy : y ≤ Counter.value xs+1) :
    K*y < 2^(2*xs.length+PaddedWord.commonConstant F) := by
  have hn : Counter.value xs < 2^xs.length := by
    rw [NativeCounter.word_value]
    exact BinaryCarry.value_lt xs
  have hk := hK.trans_lt (Nat.lt_size_self (F.integerOperandConstant^2))
  calc
    K*y ≤ K*2^xs.length := Nat.mul_le_mul_left K (by omega)
    _ < 2^(F.integerOperandConstant^2).size*2^xs.length :=
      Nat.mul_lt_mul_of_pos_right hk (by positivity)
    _ = 2^((F.integerOperandConstant^2).size+xs.length) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold PaddedWord.commonConstant; omega)

theorem common_output_exact (F : RationalMobius) (xs : List Bool) (K : ℕ) (constant : Bool)
    (hK : K ≤ F.integerOperandConstant^2) :
    Counter.value (output (PaddedWord.commonConstant F) K xs constant) =
      K*(if constant then 1 else Counter.value xs) := by
  apply output_value_exact
  · unfold PaddedWord.commonConstant
    omega
  · apply common_small_multiple_fits F xs K _ hK
    cases constant <;> simp

theorem common_complete_trace (F : RationalMobius) (xs : List Bool) (K : ℕ) (constant : Bool)
    (hK : K ≤ F.integerOperandConstant^2) (pos : Port → ℤ) :
    ∃ t ≤ budget (PaddedWord.commonConstant F) K xs,
      Trace (PaddedWord.commonConstant F) K constant t
        (cfg (.seed (.pad false (.init (.erase 0)))) (ArithmeticSeed.initial xs) pos)
        (cfg (.multiply .done) (final (PaddedWord.commonConstant F) K xs constant) pos) ∧
      Counter.value (output (PaddedWord.commonConstant F) K xs constant) =
        K*(if constant then 1 else Counter.value xs) ∧
      (output (PaddedWord.commonConstant F) K xs constant).length =
        2*xs.length+PaddedWord.commonConstant F := by
  have hm : 0 < 2*xs.length+PaddedWord.commonConstant F := by
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t, ht, htr⟩ := complete_trace (PaddedWord.commonConstant F) K constant xs hm pos
  exact ⟨t, ht, htr, common_output_exact F xs K constant hK, output_length _ _ _ _ hm⟩

inductive Coefficient | a | b | c | d | loNum | loDen | hiNum | hiDen
  deriving DecidableEq

def coefficient (F : RationalMobius) : Coefficient → ℤ
  | .a => F.integralA | .b => F.integralB | .c => F.integralC | .d => F.integralD
  | .loNum => F.lo.num | .loDen => F.lo.den | .hiNum => F.hi.num | .hiDen => F.hi.den

theorem coefficient_bound (F : RationalMobius) (entry : Coefficient) :
    (coefficient F entry).natAbs ≤ F.integerOperandConstant^2 := by
  have hm : F.integerMagnitude ≤ F.integerOperandConstant :=
    Nat.le_mul_of_pos_right _ F.arithmeticConstant_pos
  have hc := F.arithmeticConstant_le_integerOperandConstant
  have hlo := rationalHeight_le.mp F.coefficient_heights.2.2.2.2.1
  have hhi := rationalHeight_le.mp F.coefficient_heights.2.2.2.2.2
  have he : F.integerOperandConstant ≤ F.integerOperandConstant^2 := by
    nlinarith [F.integerOperandConstant_pos]
  dsimp [RationalMobius.integerMagnitude] at hm
  cases entry <;> simp only [coefficient, Int.natAbs_natCast] <;> omega

/-- All four integral map coefficients and both endpoint numerators and
denominators satisfy the fit condition; no extra magnitude premise is needed. -/
theorem coefficient_trace (F : RationalMobius) (entry : Coefficient) (xs : List Bool)
    (constant : Bool) (pos : Port → ℤ) :
    let K := (coefficient F entry).natAbs
    ∃ t ≤ budget (PaddedWord.commonConstant F) K xs,
      Trace (PaddedWord.commonConstant F) K constant t
        (cfg (.seed (.pad false (.init (.erase 0)))) (ArithmeticSeed.initial xs) pos)
        (cfg (.multiply .done) (final (PaddedWord.commonConstant F) K xs constant) pos) ∧
      Counter.value (output (PaddedWord.commonConstant F) K xs constant) =
        K*(if constant then 1 else Counter.value xs) ∧
      (output (PaddedWord.commonConstant F) K xs constant).length =
        2*xs.length+PaddedWord.commonConstant F :=
  common_complete_trace F xs _ constant (coefficient_bound F entry) pos

theorem budget_expansion (C K : ℕ) (xs : List Bool) :
    budget C K xs = (17+18*K)*C+83+52*K+(46+36*K)*xs.length := by
  unfold budget ArithmeticSeed.budget FixedMultiple.budget
  ring

theorem total_budget (F : RationalMobius) (K n : ℕ) (xs : List Bool) (hn : 1 ≤ n)
    (hl : xs.length ≤ (n+1).size) :
    n*(n*budget (PaddedWord.commonConstant F) K xs) ≤
      ((34+36*K)*(F.integerOperandConstant^2).size+578+464*K)*Transpose.inputLength n := by
  have h := dense_scan_budget ((17+18*K)*PaddedWord.commonConstant F+83+52*K) (46+36*K) n hn
  calc
    _ ≤ n*(n*(((17+18*K)*PaddedWord.commonConstant F+83+52*K)+(46+36*K)*(n+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      rw [budget_expansion]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.SeedMultiple
