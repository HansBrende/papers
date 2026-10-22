import TransposeFollowup.SeedMultipleMeaning
import TransposeFollowup.NativeErase

/-! An endpoint is stored as positive/negative numerator components and a
positive denominator. Inputs are the dimension, row index and paid seed
resources. All endpoint coefficients, products and output tapes start blank. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

inductive Port | dimension | index | unit | zero | fuel | scratch | grid
  | work (i : Fin 4) | out (i : Fin 3)
  deriving DecidableEq, Fintype

@[ext] structure Bank where
  dimension : Tape Bool
  index : Tape Bool
  unit : Tape Bool
  zero : Tape Bool
  fuel : Tape Bool
  scratch : Tape Bool
  grid : Tape Bool
  work : Fin 4 → Tape Bool
  out : Fin 3 → Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .dimension => s.dimension | .index => s.index | .unit => s.unit
  | .zero => s.zero | .fuel => s.fuel | .scratch => s.scratch | .grid => s.grid
  | .work i => s.work i | .out i => s.out i

def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank :=
  match p with
  | .dimension => {s with dimension := w} | .index => {s with index := w}
  | .unit => {s with unit := w} | .zero => {s with zero := w}
  | .fuel => {s with fuel := w} | .scratch => {s with scratch := w}
  | .grid => {s with grid := w} | .work i => {s with work := Function.update s.work i w}
  | .out i => {s with out := Function.update s.out i w}

def initial (n i : List Bool) : Bank where
  dimension := Counter.marked n
  index := Counter.marked i
  unit := Counter.marked (ArithmeticSeed.one n.length)
  zero := Counter.marked (ArithmeticSeed.zeros n.length)
  fuel := Counter.marked [true]
  scratch := BinaryCarry.preparedOutput
  grid := ⟨[], []⟩
  work := fun _ => ⟨[], []⟩
  out := fun _ => ⟨[], []⟩

def gridWord (upper : Bool) (n i : List Bool) : List Bool :=
  if upper then RepeatedAdd.addWord i (ArithmeticSeed.one n.length) else i

theorem gridWord_length (upper : Bool) (n i : List Bool) (hm : 0 < n.length)
    (hi : i.length = n.length) : (gridWord upper n i).length = n.length := by
  cases upper <;> simp only [gridWord, Bool.false_eq_true, ite_false, ite_true]
  · exact hi
  · exact (RepeatedAdd.addWord_length _ _ (hi.trans (ArithmeticSeed.one_length _ hm).symm)).trans
      (ArithmeticSeed.one_length _ hm)

def multiplier (A B : ℕ) (j : Fin 4) : ℕ := if j = 0 ∨ j = 2 then A else B
def factorPort (j : Fin 4) : Port := if j = 2 then .dimension else if j = 3 then .grid else .unit
def factorWord (upper : Bool) (n i : List Bool) (j : Fin 4) : List Bool :=
  if j = 2 then n else if j = 3 then gridWord upper n i else ArithmeticSeed.one n.length

theorem factorWord_length (upper : Bool) (n i : List Bool) (j : Fin 4)
    (hm : 0 < n.length) (hi : i.length = n.length) :
    (factorWord upper n i j).length = n.length := by
  fin_cases j <;> simp [factorWord, gridWord_length upper n i hm hi, ArithmeticSeed.one_length _ hm]

def workWord (A B : ℕ) (upper : Bool) (n i : List Bool) (j : Fin 4) : List Bool :=
  RepeatedAdd.repeatWord (factorWord upper n i j) (multiplier A B j) (ArithmeticSeed.zeros n.length)

theorem workWord_length (A B : ℕ) (upper : Bool) (n i : List Bool) (j : Fin 4)
    (hm : 0 < n.length) (hi : i.length = n.length) :
    (workWord A B upper n i j).length = n.length := by
  have h := factorWord_length upper n i j hm hi
  exact (RepeatedAdd.repeatWord_length _ _ _ (by simp [ArithmeticSeed.zeros, h])).trans h

def chooseGrid (upper negative : Bool) (r : BinaryCompare.Result) : Bool :=
  if negative then !upper else if upper then decide (r ≠ .less) else decide (r ≠ .greater)

def selection (A B : ℕ) (upper negative : Bool) (n i : List Bool) : Bool :=
  chooseGrid upper negative (BinaryCompare.numeric .equal
    (BinaryCompare.value (workWord A B upper n i 2)) (BinaryCompare.value (workWord A B upper n i 3)))

def outputPort (negative grid : Bool) (j : Fin 3) : Port :=
  if j = 2 then (if grid then .dimension else .work 1)
  else if j = 0 then (if grid then .grid else if negative then .zero else .work 0)
  else if grid then .zero else if negative then .work 0 else .zero

def computed (A B : ℕ) (upper : Bool) (n i : List Bool) : Bank :=
  {initial n i with grid := Counter.marked (gridWord upper n i),
                    work := fun j => Counter.marked (workWord A B upper n i j)}

def final (A B : ℕ) (upper negative : Bool) (n i : List Bool) : Bank :=
  let s := computed A B upper n i
  {s with out := fun j => s.tapes (outputPort negative (selection A B upper negative n i) j)}

end TransposeFollowup.EndpointClip


/-! Static finite control for grid copying/increment, four zero buffers,
four fixed multiples, one comparison and three conditional output copies. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
set_option autoImplicit false

def pairBinding (a b : Port) (hab : a ≠ b) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![a,b], by intro j k h; fin_cases j <;> fin_cases k <;> simp_all⟩
  decode := fun p => if p = a then some 0 else if p = b then some 1 else none
  decode_spec := by
    intro p j
    change (if p = a then some 0 else if p = b then some 1 else none) = some j ↔ ![a,b] j = p
    fin_cases j <;> by_cases ha : p = a <;> by_cases hb : p = b <;> simp_all [eq_comm]

def gridBinding := pairBinding .index .grid (by decide)
def zeroBinding (j : Fin 4) := pairBinding .zero (.work j) (by simp)
def compareBinding := pairBinding (.work 2) (.work 3) (by decide)
def outputBinding (negative grid : Bool) (j : Fin 3) :=
  pairBinding (outputPort negative grid j) (.out j) (by
    cases negative <;> cases grid <;> fin_cases j <;> decide)

def addPort : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .grid | .factor => .unit | .scratch => .scratch | .zero => .zero
def addBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort, by decide +kernel⟩
  decode := fun p => match p with
    | .fuel => some .fuel | .grid => some .acc | .unit => some .factor
    | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec := by intro p t; cases p <;> cases t <;> simp [addPort]

def multiplyPort (j : Fin 4) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .work j | .factor => factorPort j
  | .scratch => .scratch | .zero => .zero
def multiplyBinding (j : Fin 4) : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨multiplyPort j, by fin_cases j <;> decide +kernel⟩
  decode := fun p => if p = .fuel then some .fuel else if p = .work j then some .acc else
    if p = factorPort j then some .factor else if p = .scratch then some .scratch else
    if p = .zero then some .zero else none
  decode_spec := by
    intro p t
    fin_cases j <;> cases p <;> cases t <;> simp [multiplyPort, factorPort, eq_comm]

inductive Label (A B : ℕ)
  | grid (pc : NativeMappedCopy.Label)
  | advance (pc : RepeatedAdd.Label)
  | init (j : Fin 4) (pc : NativeMappedCopy.Label)
  | multiply (j : Fin 4) (pc : FixedMultiple.Label (multiplier A B j))
  | compare (pc : BinaryCompare.Label)
  | copy (grid : Bool) (j : Fin 3) (pc : NativeMappedCopy.Label)
  | done (grid : Bool)
  deriving DecidableEq, Fintype

def afterInit (A B : ℕ) (j : Fin 4) : Label A B :=
  if h : j.val < 3 then .init ⟨j.val+1, by omega⟩ (.init (.erase 0))
  else .multiply 0 (FixedMultiple.start (multiplier A B 0))
def afterMultiply (A B : ℕ) (j : Fin 4) : Label A B :=
  if h : j.val < 3 then .multiply ⟨j.val+1, by omega⟩ (FixedMultiple.start _)
  else .compare (.scan .equal)
def afterCopy (A B : ℕ) (grid : Bool) (j : Fin 3) : Label A B :=
  if h : j.val < 2 then .copy grid ⟨j.val+1, by omega⟩ (.init (.erase 0)) else .done grid

def program (A B : ℕ) (upper negative : Bool) : Microcode.Program Port (Label A B)
  | .grid (.seal .done) => .jump (if upper then .advance (.counter 0) else .init 0 (.init (.erase 0)))
  | .grid pc => gridBinding.instruction Label.grid (NativeMappedCopy.program id pc)
  | .advance (.counter pc) => if pc = 12 then .jump (.init 0 (.init (.erase 0)))
      else addBinding.instruction Label.advance (RepeatedAdd.program (.counter pc))
  | .advance pc => addBinding.instruction Label.advance (RepeatedAdd.program pc)
  | .init j (.seal .done) => .jump (afterInit A B j)
  | .init j pc => (zeroBinding j).instruction (Label.init j) (NativeMappedCopy.program id pc)
  | .multiply j .done => .jump (afterMultiply A B j)
  | .multiply j pc => (multiplyBinding j).instruction (Label.multiply j) (FixedMultiple.program _ pc)
  | .compare (.done r) => .jump (.copy (chooseGrid upper negative r) 0 (.init (.erase 0)))
  | .compare pc => compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .copy grid j (.seal .done) => .jump (afterCopy A B grid j)
  | .copy grid j pc => (outputBinding negative grid j).instruction
      (Label.copy grid j) (NativeMappedCopy.program id pc)
  | .done _ => .halt

theorem grid_code (A B : ℕ) (upper negative : Bool) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc ≠ .halt) (_ : NativeMappedCopy.program id pc ≠ .reject) :
    program A B upper negative (.grid pc) = MicrocodeEmbedding.instruction gridBinding.ports
      Label.grid (NativeMappedCopy.program id pc) := by
  have hp : pc ≠ .seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem advance_code (A B : ℕ) (upper negative : Bool) (pc : RepeatedAdd.Label)
    (hh : RepeatedAdd.program pc ≠ .halt) (_ : RepeatedAdd.program pc ≠ .reject) :
    program A B upper negative (.advance pc) = MicrocodeEmbedding.instruction addBinding.ports
      Label.advance (RepeatedAdd.program pc) := by
  have hp : pc ≠ .counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem init_code (A B : ℕ) (upper negative : Bool) (j : Fin 4) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc ≠ .halt) (_ : NativeMappedCopy.program id pc ≠ .reject) :
    program A B upper negative (.init j pc) = MicrocodeEmbedding.instruction (zeroBinding j).ports
      (Label.init j) (NativeMappedCopy.program id pc) := by
  have hp : pc ≠ .seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem multiply_code (A B : ℕ) (upper negative : Bool) (j : Fin 4)
    (pc : FixedMultiple.Label (multiplier A B j))
    (hh : FixedMultiple.program _ pc ≠ .halt) (_ : FixedMultiple.program _ pc ≠ .reject) :
    program A B upper negative (.multiply j pc) = MicrocodeEmbedding.instruction (multiplyBinding j).ports
      (Label.multiply j) (FixedMultiple.program _ pc) := by
  have hp : pc ≠ .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem compare_code (A B : ℕ) (upper negative : Bool) (pc : BinaryCompare.Label)
    (hh : BinaryCompare.program pc ≠ .halt) (_ : BinaryCompare.program pc ≠ .reject) :
    program A B upper negative (.compare pc) = MicrocodeEmbedding.instruction compareBinding.ports
      Label.compare (BinaryCompare.program pc) := by
  cases pc <;> simp_all [program, BinaryCompare.program, FinitePortBinding.instruction_eq]

theorem copy_code (A B : ℕ) (upper negative grid : Bool) (j : Fin 3) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc ≠ .halt) (_ : NativeMappedCopy.program id pc ≠ .reject) :
    program A B upper negative (.copy grid j pc) = MicrocodeEmbedding.instruction
      (outputBinding negative grid j).ports (Label.copy grid j) (NativeMappedCopy.program id pc) := by
  have hp : pc ≠ .seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

def cfg {A B : ℕ} (pc : Label A B) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label A B) :=
  ⟨⟨pc, fun p => (s.tapes p).denote⟩, pos⟩
def zipperCfg {A B : ℕ} (pc : Label A B) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label A B) :=
  ⟨⟨pc, s.tapes⟩, pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s.tapes p).denote, pos⟩

noncomputable def nativeEncoding (A B : ℕ) :=
  NativeMicrocode.initialEncoding (T := Port) (Label.grid (A := A) (B := B) (.init (.erase 0)))
noncomputable def nativeMachine (A B : ℕ) (upper negative : Bool) :=
  NativeMicrocode.machine (nativeEncoding A B) (program A B upper negative)

end TransposeFollowup.EndpointClip


/-! Both coefficients are fixed machine parameters. The state count is
independent of the dimension, row index and word width. -/

namespace TransposeFollowup.EndpointClip

set_option autoImplicit false

def labelEquiv (A B : ℕ) : Label A B ≃
    NativeMappedCopy.Label ⊕ RepeatedAdd.Label ⊕ (Fin 4 × NativeMappedCopy.Label) ⊕
    (Σ j : Fin 4, FixedMultiple.Label (multiplier A B j)) ⊕ BinaryCompare.Label ⊕
    (Bool × Fin 3 × NativeMappedCopy.Label) ⊕ Bool where
  toFun
    | .grid pc => .inl pc
    | .advance pc => .inr (.inl pc)
    | .init j pc => .inr (.inr (.inl (j,pc)))
    | .multiply j pc => .inr (.inr (.inr (.inl ⟨j,pc⟩)))
    | .compare pc => .inr (.inr (.inr (.inr (.inl pc))))
    | .copy grid j pc => .inr (.inr (.inr (.inr (.inr (.inl (grid,j,pc))))))
    | .done grid => .inr (.inr (.inr (.inr (.inr (.inr grid)))))
  invFun
    | .inl pc => .grid pc
    | .inr (.inl pc) => .advance pc
    | .inr (.inr (.inl (j,pc))) => .init j pc
    | .inr (.inr (.inr (.inl ⟨j,pc⟩))) => .multiply j pc
    | .inr (.inr (.inr (.inr (.inl pc)))) => .compare pc
    | .inr (.inr (.inr (.inr (.inr (.inl (grid,j,pc)))))) => .copy grid j pc
    | .inr (.inr (.inr (.inr (.inr (.inr grid))))) => .done grid
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | pc | ⟨j,pc⟩ | ⟨j,pc⟩ | pc | ⟨grid,j,pc⟩ | grid) <;> rfl

theorem label_card (A B : ℕ) : Fintype.card (Label A B) = 198*(A+B)+793 := by
  have h := Fintype.card_congr (labelEquiv A B)
  have hc : Fintype.card NativeMappedCopy.Label = 24 := by decide +kernel
  have ha : Fintype.card RepeatedAdd.Label = 99 := by decide +kernel
  have hp : Fintype.card BinaryCompare.Label = 28 := by decide +kernel
  have hm : (∑ j : Fin 4, (99*(multiplier A B j+1)+1)) = 198*(A+B)+400 := by
    norm_num [Fin.sum_univ_succ, multiplier]
    omega
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_bool, hc, ha, hp, FixedMultiple.label_card] at h
  rw [hm] at h
  exact h.trans (by ring)

theorem fixed_resources (A B : ℕ) (upper negative : Bool) :
    (nativeMachine A B upper negative).k = 14 ∧ (nativeMachine A B upper negative).g+1 = 5 ∧
    (nativeMachine A B upper negative).q+1 = 198*(A+B)+793 ∧
    (nativeEncoding A B).label (.grid (.init (.erase 0))) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 14
    decide +kernel
  · change Fintype.card (Label A B)-1+1 = 198*(A+B)+793
    rw [label_card]
    omega

end TransposeFollowup.EndpointClip


/-! Framed native calls for the clipping controller. Preconditions on seed
resources are explicit; coefficient/product/output buffers are paid by copying. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

@[simp] theorem Bank.set_tapes (s : Bank) (p q : Port) (w : Tape Bool) :
    (s.set p w).tapes q = Function.update s.tapes p w q := by
  cases p <;> cases q <;> simp [Bank.set, Bank.tapes, Function.update]

@[simp] theorem Bank.set_self (s : Bank) (p : Port) : s.set p (s.tapes p) = s := by
  cases p <;> simp [Bank.set, Bank.tapes]

theorem embed_copy (A B : ℕ) (p q : Port) (hpq : p ≠ q)
    (labels : NativeMappedCopy.Label → Label A B) (pc : NativeMappedCopy.Label)
    (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (pairBinding p q hpq).ports labels
      (NativeMappedCopy.cfg pc a b (fun t => pos ((pairBinding p q hpq).ports t))) (frame s pos) =
      cfg (labels pc) ((s.set p a).set q b) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← (pairBinding p q hpq).values_eq_extend]
  congr 2 <;> funext t
  all_goals
    by_cases ht : t = p
    · subst t
      simp [pairBinding, FinitePortBinding.values, NativeMappedCopy.bank, Function.update, hpq] <;> rfl
    · by_cases hq : t = q
      · subst t
        simp [pairBinding, FinitePortBinding.values, NativeMappedCopy.bank, Function.update, Ne.symm hpq] <;> rfl
      · simp [pairBinding, FinitePortBinding.values, Function.update, ht, hq]

theorem embed_advance (A B : ℕ) (pc : RepeatedAdd.Label) (b : RepeatedAdd.Bank)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports (Label.advance (A := A) (B := B))
      (RepeatedAdd.cfg pc b (fun t => pos (addBinding.ports t))) (frame s pos) =
      cfg (.advance pc) {s with fuel := b.fuel, grid := b.acc, unit := b.factor, scratch := b.scratch, zero := b.zero} pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_multiply (A B : ℕ) (j : Fin 4) (pc : FixedMultiple.Label (multiplier A B j))
    (b : RepeatedAdd.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (multiplyBinding j).ports (Label.multiply j)
      (FixedMultiple.cfg pc b (fun t => pos ((multiplyBinding j).ports t))) (frame s pos) =
      cfg (.multiply j pc)
        (({s with fuel := b.fuel, scratch := b.scratch, zero := b.zero, work := Function.update s.work j b.acc}).set (factorPort j) b.factor) pos := by
  unfold MicrocodeEmbedding.embed FixedMultiple.cfg cfg frame
  simp only [← (multiplyBinding j).values_eq_extend]
  fin_cases j <;> congr 2 <;> funext p <;> cases p <;> try rfl
  all_goals rename_i k; fin_cases k <;> rfl

theorem embed_compare (A B : ℕ) (pc : BinaryCompare.Label) (a b : Tape Bool)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports (Label.compare (A := A) (B := B))
      (BinaryCompare.cfg pc a b (fun t => pos (compareBinding.ports t))).denote (frame s pos) =
      cfg (.compare pc) ((s.set (.work 2) a).set (.work 3) b) pos := by
  unfold MicrocodeEmbedding.embed BinaryCompare.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← compareBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try rfl
  all_goals rename_i k; fin_cases k <;> rfl

abbrev Trace (A B : ℕ) (upper negative : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program A B upper negative))
    (NativeMicrocode.Active (program A B upper negative))

theorem jump_trace (A B : ℕ) (upper negative : Bool) (pc next : Label A B)
    (s : Bank) (pos : Port → ℤ) (h : program A B upper negative pc = .jump next) :
    Trace A B upper negative 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem mapped_call (A B : ℕ) (upper negative : Bool) (p q : Port) (hpq : p ≠ q)
    (labels : NativeMappedCopy.Label → Label A B)
    (hc : ∀ pc, NativeMappedCopy.program id pc ≠ .halt → NativeMappedCopy.program id pc ≠ .reject →
      program A B upper negative (labels pc) = MicrocodeEmbedding.instruction (pairBinding p q hpq).ports
        labels (NativeMappedCopy.program id pc))
    (xs : List Bool) (s : Bank) (hs : s.tapes p = Counter.marked xs)
    (hq : s.tapes q = ⟨[], []⟩) (pos : Port → ℤ) :
    ∃ t ≤ 6*xs.length+14,
      Trace A B upper negative t (cfg (labels (.init (.erase 0))) s pos)
        (cfg (labels (.seal .done)) (s.set q (Counter.marked xs)) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeMappedCopy.copy_trace id xs (fun t => pos ((pairBinding p q hpq).ports t))
  have he := MicrocodeEmbedding.trace_embed (pairBinding p q hpq).ports labels
    (NativeMappedCopy.program id) (program A B upper negative) (frame s pos) hc htr
  exact ⟨t, ht, by simpa only [embed_copy, List.map_id, ← hs, Bank.set_self, ← hq] using he⟩

theorem advance_call (A B : ℕ) (upper negative : Bool) (a u : List Bool)
    (h : a.length = u.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 18*u.length+51,
      Trace A B upper negative t
        (cfg (.advance (.counter 0)) {s with fuel := Counter.marked [true], grid := Counter.marked a, unit := Counter.marked u, scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate u.length false)} pos)
        (cfg (.advance (.counter 12)) {s with fuel := Counter.marked [true], grid := Counter.marked (RepeatedAdd.addWord a u), unit := Counter.marked u, scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate u.length false)} pos) := by
  obtain ⟨t, ht, htr⟩ := RepeatedAdd.single_add_trace a u h (fun t => pos (addBinding.ports t))
  have he := MicrocodeEmbedding.trace_embed addBinding.ports (Label.advance (A := A) (B := B))
    RepeatedAdd.program (program A B upper negative) (frame s pos) (advance_code A B upper negative) htr
  exact ⟨t, ht, by simpa only [embed_advance, RepeatedAdd.ready, Counter.marked,
    BinaryCarry.marked, BinaryCompare.marked] using he⟩

theorem multiply_call (A B : ℕ) (upper negative : Bool) (j : Fin 4) (a x : List Bool)
    (h : a.length = x.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ FixedMultiple.budget (multiplier A B j) x.length,
      Trace A B upper negative t
        (cfg (.multiply j (FixedMultiple.start _))
          (({s with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate x.length false), work := Function.update s.work j (Counter.marked a)}).set (factorPort j) (Counter.marked x)) pos)
        (cfg (.multiply j .done)
          (({s with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate x.length false), work := Function.update s.work j (Counter.marked (RepeatedAdd.repeatWord x (multiplier A B j) a))}).set
            (factorPort j) (Counter.marked x)) pos) := by
  obtain ⟨t, ht, htr⟩ := FixedMultiple.multiple_trace (multiplier A B j) a x h
    (fun t => pos ((multiplyBinding j).ports t))
  have he := MicrocodeEmbedding.trace_embed (multiplyBinding j).ports (Label.multiply j)
    (FixedMultiple.program _) (program A B upper negative) (frame s pos) (multiply_code A B upper negative j) htr
  exact ⟨t, ht, by simpa only [embed_multiply, RepeatedAdd.ready, Counter.marked,
    BinaryCarry.marked, BinaryCompare.marked] using he⟩

theorem compare_call (A B : ℕ) (upper negative : Bool) (a b : List Bool)
    (h : a.length = b.length) (s : Bank) (ha : s.tapes (.work 2) = Counter.marked a)
    (hb : s.tapes (.work 3) = Counter.marked b) (pos : Port → ℤ) :
    ∃ t ≤ 5*a.length+6,
      Trace A B upper negative t (cfg (.compare (.scan .equal)) s pos)
        (cfg (.compare (.done (BinaryCompare.numeric .equal (BinaryCompare.value a) (BinaryCompare.value b)))) s pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCompare.comparison_trace a b h (fun t => pos (compareBinding.ports t))
  have he := MicrocodeEmbedding.trace_embed compareBinding.ports (Label.compare (A := A) (B := B))
    BinaryCompare.program (program A B upper negative) (frame s pos) (compare_code A B upper negative) htr
  have hmarked (w : List Bool) : BinaryCompare.marked w = Counter.marked w := rfl
  exact ⟨t, ht, by simpa only [embed_compare, hmarked, ← ha, Bank.set_self, ← hb] using he⟩

end TransposeFollowup.EndpointClip


/-! The successive concrete banks contain only input words, paid zero
copies, and outputs of the actual arithmetic calls. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def base (upper : Bool) (n i : List Bool) : Bank :=
  {initial n i with grid := Counter.marked (gridWord upper n i)}
def zeroed (upper : Bool) (n i : List Bool) (k : ℕ) : Bank :=
  {base upper n i with work := fun j => if j.val < k then Counter.marked (ArithmeticSeed.zeros n.length) else ⟨[], []⟩}
def multiplied (A B : ℕ) (upper : Bool) (n i : List Bool) (k : ℕ) : Bank :=
  {base upper n i with work := fun j => if j.val < k then Counter.marked (workWord A B upper n i j) else Counter.marked (ArithmeticSeed.zeros n.length)}

theorem zeroed_zero (upper : Bool) (n i : List Bool) : zeroed upper n i 0 = base upper n i := by
  simp [zeroed, base, initial]

theorem zeroed_step (upper : Bool) (n i : List Bool) (j : Fin 4) :
    (zeroed upper n i j.val).set (.work j) (Counter.marked (ArithmeticSeed.zeros n.length)) =
      zeroed upper n i (j.val+1) := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases j <;> fin_cases k <;> rfl

theorem zeroed_four (A B : ℕ) (upper : Bool) (n i : List Bool) :
    zeroed upper n i 4 = multiplied A B upper n i 0 := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases k <;> rfl

theorem multiplied_four (A B : ℕ) (upper : Bool) (n i : List Bool) :
    multiplied A B upper n i 4 = computed A B upper n i := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases k <;> rfl

theorem grid_trace (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ 24*n.length+67,
      Trace A B upper negative t (cfg (.grid (.init (.erase 0))) (initial n i) pos)
        (cfg (.init 0 (.init (.erase 0))) (base upper n i) pos) := by
  obtain ⟨a, ha, hc⟩ := mapped_call A B upper negative .index .grid (by decide) Label.grid
    (grid_code A B upper negative) i (initial n i) rfl rfl pos
  cases upper with
  | false =>
    have hj := jump_trace A B false negative (.grid (.seal .done)) (.init 0 (.init (.erase 0)))
      ((initial n i).set .grid (Counter.marked i)) pos rfl
    exact ⟨a+1, by omega, trace_trans hc hj⟩
  | true =>
    let s := (initial n i).set .grid (Counter.marked i)
    have j1 := jump_trace A B true negative (.grid (.seal .done)) (.advance (.counter 0)) s pos rfl
    have hu := ArithmeticSeed.one_length n.length hm
    obtain ⟨b, hb, had⟩ := advance_call A B true negative i (ArithmeticSeed.one n.length)
      (hi.trans hu.symm) s pos
    rw [hu] at hb had
    have ht : Trace A B true negative b (cfg (.advance (.counter 0)) s pos)
        (cfg (.advance (.counter 12)) (base true n i) pos) := by
      simpa [s, Bank.set, initial, base, gridWord, ArithmeticSeed.zeros] using had
    have j2 := jump_trace A B true negative (.advance (.counter 12)) (.init 0 (.init (.erase 0)))
      (base true n i) pos rfl
    exact ⟨a+(1+(b+1)), by omega, trace_trans hc (trace_trans j1 (trace_trans ht j2))⟩

theorem init_stage (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (j : Fin 4) (pos : Port → ℤ) :
    ∃ t ≤ 6*n.length+15,
      Trace A B upper negative t
        (cfg (.init j (.init (.erase 0))) (zeroed upper n i j.val) pos)
        (cfg (afterInit A B j) (zeroed upper n i (j.val+1)) pos) := by
  obtain ⟨a, ha, hc⟩ := mapped_call A B upper negative .zero (.work j) (by simp) (Label.init j)
    (init_code A B upper negative j) (ArithmeticSeed.zeros n.length) (zeroed upper n i j.val)
    rfl (by simp [zeroed, Bank.tapes]) pos
  rw [zeroed_step] at hc
  have hj := jump_trace A B upper negative (.init j (.seal .done)) (afterInit A B j)
    (zeroed upper n i (j.val+1)) pos rfl
  exact ⟨a+1, by simpa [ArithmeticSeed.zeros] using Nat.add_le_add_right ha 1, trace_trans hc hj⟩

theorem init_all (A B : ℕ) (upper negative : Bool) (n i : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 24*n.length+60,
      Trace A B upper negative t (cfg (.init 0 (.init (.erase 0))) (base upper n i) pos)
        (cfg (.multiply 0 (FixedMultiple.start _)) (multiplied A B upper n i 0) pos) := by
  obtain ⟨a, ha, h0⟩ := init_stage A B upper negative n i 0 pos
  obtain ⟨b, hb, h1⟩ := init_stage A B upper negative n i 1 pos
  obtain ⟨c, hc, h2⟩ := init_stage A B upper negative n i 2 pos
  obtain ⟨d, hd, h3⟩ := init_stage A B upper negative n i 3 pos
  have h := trace_trans h0 (trace_trans h1 (trace_trans h2 h3))
  refine ⟨a+(b+(c+d)), by omega, ?_⟩
  simpa [afterInit, zeroed_zero, zeroed_four A B upper n i] using h

theorem multiply_stage (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (j : Fin 4) (pos : Port → ℤ) :
    ∃ t ≤ FixedMultiple.budget (multiplier A B j) n.length+1,
      Trace A B upper negative t
        (cfg (.multiply j (FixedMultiple.start _)) (multiplied A B upper n i j.val) pos)
        (cfg (afterMultiply A B j) (multiplied A B upper n i (j.val+1)) pos) := by
  have hl := factorWord_length upper n i j hm hi
  obtain ⟨a, ha, hc⟩ := multiply_call A B upper negative j (ArithmeticSeed.zeros n.length)
    (factorWord upper n i j) (by simp [ArithmeticSeed.zeros, hl])
    (multiplied A B upper n i j.val) pos
  rw [hl] at ha hc
  have hstart :
      (({multiplied A B upper n i j.val with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate n.length false), work := Function.update (multiplied A B upper n i j.val).work j (Counter.marked (ArithmeticSeed.zeros n.length))}).set
        (factorPort j) (Counter.marked (factorWord upper n i j))) = multiplied A B upper n i j.val := by
    fin_cases j <;> apply Bank.ext <;> try rfl
    all_goals funext k; fin_cases k <;> rfl
  have hend :
      (({multiplied A B upper n i j.val with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate n.length false), work := Function.update (multiplied A B upper n i j.val).work j (Counter.marked (workWord A B upper n i j))}).set
        (factorPort j) (Counter.marked (factorWord upper n i j))) = multiplied A B upper n i (j.val+1) := by
    fin_cases j <;> apply Bank.ext <;> try rfl
    all_goals funext k; fin_cases k <;> rfl
  change Trace A B upper negative a (cfg _ _ pos) (cfg _ _ pos) at hc
  rw [hstart, show RepeatedAdd.repeatWord (factorWord upper n i j) (multiplier A B j)
    (ArithmeticSeed.zeros n.length) = workWord A B upper n i j by rfl, hend] at hc
  have hj := jump_trace A B upper negative (.multiply j .done) (afterMultiply A B j)
    (multiplied A B upper n i (j.val+1)) pos rfl
  exact ⟨a+1, Nat.add_le_add_right ha 1, trace_trans hc hj⟩

theorem multiply_all (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ 2*(A+B)*(18*n.length+52)+8,
      Trace A B upper negative t
        (cfg (.multiply 0 (FixedMultiple.start _)) (multiplied A B upper n i 0) pos)
        (cfg (.compare (.scan .equal)) (computed A B upper n i) pos) := by
  obtain ⟨a, ha, h0⟩ := multiply_stage A B upper negative n i hm hi 0 pos
  obtain ⟨b, hb, h1⟩ := multiply_stage A B upper negative n i hm hi 1 pos
  obtain ⟨c, hc, h2⟩ := multiply_stage A B upper negative n i hm hi 2 pos
  obtain ⟨d, hd, h3⟩ := multiply_stage A B upper negative n i hm hi 3 pos
  have h := trace_trans h0 (trace_trans h1 (trace_trans h2 h3))
  refine ⟨a+(b+(c+d)), ?_, ?_⟩
  · simp only [multiplier, FixedMultiple.budget] at ha hb hc hd
    norm_num at ha hb hc hd
    nlinarith
  · simpa [afterMultiply, multiplied_four] using h

end TransposeFollowup.EndpointClip


/-! The complete clipping controller pays for the comparison result's
branch and all three output copies, including signs and denominator. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def outputWord (A B : ℕ) (upper negative grid : Bool) (n i : List Bool) (j : Fin 3) : List Bool :=
  if j = 2 then (if grid then n else workWord A B upper n i 1)
  else if j = 0 then (if grid then gridWord upper n i else if negative then ArithmeticSeed.zeros n.length else workWord A B upper n i 0)
  else if grid then ArithmeticSeed.zeros n.length else if negative then workWord A B upper n i 0 else ArithmeticSeed.zeros n.length

def outputStage (A B : ℕ) (upper negative grid : Bool) (n i : List Bool) (k : ℕ) : Bank :=
  {computed A B upper n i with out := fun j => if j.val < k then Counter.marked (outputWord A B upper negative grid n i j) else ⟨[], []⟩}

theorem output_source (A B : ℕ) (upper negative grid : Bool) (n i : List Bool) (k : ℕ) (j : Fin 3) :
    (outputStage A B upper negative grid n i k).tapes (outputPort negative grid j) =
      Counter.marked (outputWord A B upper negative grid n i j) := by
  cases negative <;> cases grid <;> fin_cases j <;> rfl

theorem computed_source (A B : ℕ) (upper negative grid : Bool) (n i : List Bool) (j : Fin 3) :
    (computed A B upper n i).tapes (outputPort negative grid j) =
      Counter.marked (outputWord A B upper negative grid n i j) := by
  cases negative <;> cases grid <;> fin_cases j <;> rfl

theorem final_out (A B : ℕ) (upper negative : Bool) (n i : List Bool) (j : Fin 3) :
    (final A B upper negative n i).out j =
      Counter.marked (outputWord A B upper negative (selection A B upper negative n i) n i j) :=
  computed_source A B upper negative (selection A B upper negative n i) n i j

theorem outputWord_length (A B : ℕ) (upper negative grid : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (j : Fin 3) :
    (outputWord A B upper negative grid n i j).length = n.length := by
  have hw (k : Fin 4) := workWord_length A B upper n i k hm hi
  have hg := gridWord_length upper n i hm hi
  cases negative <;> cases grid <;> fin_cases j <;> simp [outputWord, hw, hg, ArithmeticSeed.zeros]

theorem outputStage_zero (A B : ℕ) (upper negative grid : Bool) (n i : List Bool) :
    outputStage A B upper negative grid n i 0 = computed A B upper n i := by
  simp [outputStage, computed, initial]

theorem outputStage_step (A B : ℕ) (upper negative grid : Bool) (n i : List Bool) (j : Fin 3) :
    (outputStage A B upper negative grid n i j.val).set (.out j)
      (Counter.marked (outputWord A B upper negative grid n i j)) =
      outputStage A B upper negative grid n i (j.val+1) := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases j <;> fin_cases k <;> rfl

theorem outputStage_final (A B : ℕ) (upper negative : Bool) (n i : List Bool) :
    outputStage A B upper negative (selection A B upper negative n i) n i 3 =
      final A B upper negative n i := by
  apply Bank.ext <;> try rfl
  funext j
  simp only [outputStage, final, show j.val < 3 from j.isLt, ite_true, computed_source]

theorem comparison_stage (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ 5*n.length+7,
      Trace A B upper negative t (cfg (.compare (.scan .equal)) (computed A B upper n i) pos)
        (cfg (.copy (selection A B upper negative n i) 0 (.init (.erase 0)))
          (outputStage A B upper negative (selection A B upper negative n i) n i 0) pos) := by
  have h2 := workWord_length A B upper n i 2 hm hi
  have h3 := workWord_length A B upper n i 3 hm hi
  obtain ⟨t, ht, htr⟩ := compare_call A B upper negative
    (workWord A B upper n i 2) (workWord A B upper n i 3) (h2.trans h3.symm)
    (computed A B upper n i) rfl rfl pos
  have hj := jump_trace A B upper negative (.compare (.done (BinaryCompare.numeric .equal
      (BinaryCompare.value (workWord A B upper n i 2)) (BinaryCompare.value (workWord A B upper n i 3)))))
    (.copy (selection A B upper negative n i) 0 (.init (.erase 0))) (computed A B upper n i) pos rfl
  refine ⟨t+1, by rw [h2] at ht; omega, ?_⟩
  simpa only [outputStage_zero] using trace_trans htr hj

theorem output_stage (A B : ℕ) (upper negative grid : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (j : Fin 3) (pos : Port → ℤ) :
    ∃ t ≤ 6*n.length+15,
      Trace A B upper negative t
        (cfg (.copy grid j (.init (.erase 0))) (outputStage A B upper negative grid n i j.val) pos)
        (cfg (afterCopy A B grid j) (outputStage A B upper negative grid n i (j.val+1)) pos) := by
  obtain ⟨t, ht, htr⟩ := mapped_call A B upper negative (outputPort negative grid j) (.out j)
    (by cases negative <;> cases grid <;> fin_cases j <;> decide) (Label.copy grid j)
    (copy_code A B upper negative grid j) (outputWord A B upper negative grid n i j)
    (outputStage A B upper negative grid n i j.val) (output_source _ _ _ _ _ _ _ _ _)
    (by simp [outputStage, Bank.tapes]) pos
  rw [outputStage_step] at htr
  have hj := jump_trace A B upper negative (.copy grid j (.seal .done)) (afterCopy A B grid j)
    (outputStage A B upper negative grid n i (j.val+1)) pos rfl
  exact ⟨t+1, by rw [outputWord_length _ _ _ _ _ _ _ hm hi] at ht; omega, trace_trans htr hj⟩

theorem output_all (A B : ℕ) (upper negative grid : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ 18*n.length+45,
      Trace A B upper negative t
        (cfg (.copy grid 0 (.init (.erase 0))) (outputStage A B upper negative grid n i 0) pos)
        (cfg (.done grid) (outputStage A B upper negative grid n i 3) pos) := by
  obtain ⟨a, ha, h0⟩ := output_stage A B upper negative grid n i hm hi 0 pos
  obtain ⟨b, hb, h1⟩ := output_stage A B upper negative grid n i hm hi 1 pos
  obtain ⟨c, hc, h2⟩ := output_stage A B upper negative grid n i hm hi 2 pos
  exact ⟨a+(b+c), by omega, trace_trans h0 (trace_trans h1 h2)⟩

def budget (A B m : ℕ) : ℕ := 71*m+187+2*(A+B)*(18*m+52)

theorem clip_trace (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ budget A B n.length,
      Trace A B upper negative t (cfg (.grid (.init (.erase 0))) (initial n i) pos)
        (cfg (.done (selection A B upper negative n i)) (final A B upper negative n i) pos) := by
  obtain ⟨a, ha, hg⟩ := grid_trace A B upper negative n i hm hi pos
  obtain ⟨b, hb, hz⟩ := init_all A B upper negative n i pos
  obtain ⟨c, hc, hmul⟩ := multiply_all A B upper negative n i hm hi pos
  obtain ⟨d, hd, hcmp⟩ := comparison_stage A B upper negative n i hm hi pos
  obtain ⟨e, he, hout⟩ := output_all A B upper negative (selection A B upper negative n i)
    n i hm hi pos
  have h := trace_trans hg (trace_trans hz (trace_trans hmul (trace_trans hcmp hout)))
  exact ⟨a+(b+(c+(d+e))), by dsimp [budget]; omega, by simpa only [outputStage_final] using h⟩

theorem native_clip (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget A B n.length,
      Transpose.stepN (nativeMachine A B upper negative) input t
        ((cfg (.grid (.init (.erase 0))) (initial n i) pos).denote
          (nativeEncoding A B) (program A B upper negative) inputPos outRev) =
        some ((cfg (.done (selection A B upper negative n i)) (final A B upper negative n i) pos).denote
          (nativeEncoding A B) (program A B upper negative) inputPos outRev) ∧
      Transpose.step (nativeMachine A B upper negative) input
        ((cfg (.done (selection A B upper negative n i)) (final A B upper negative n i) pos).denote
          (nativeEncoding A B) (program A B upper negative) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := clip_trace A B upper negative n i hm hi pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding A B) (program A B upper negative)
    input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding A B) (program A B upper negative)
    input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (A B : ℕ) (upper negative : Bool)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label A B → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program A B upper negative pc ≠ .halt → program A B upper negative pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program A B upper negative pc))
    (n i : List Bool) (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget A B n.length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (.grid (.init (.erase 0))) (initial n i) pos) frame).denote
          encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (selection A B upper negative n i)) (final A B upper negative n i) pos) frame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := clip_trace A B upper negative n i hm hi pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program A B upper negative) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.EndpointClip


/-! Exact integer clipping semantics. All products use the real binary
calls; their fit bounds will be supplied by the common-width construction. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
set_option autoImplicit false

def gridIndex (upper : Bool) (i : ℕ) : ℕ := if upper then i+1 else i

theorem gridWord_value (upper : Bool) (n i : List Bool) (hm : 0 < n.length)
    (hi : i.length = n.length) (hin : Counter.value i < Counter.value n) :
    Counter.value (gridWord upper n i) = gridIndex upper (Counter.value i) := by
  have hn : Counter.value n < 2^n.length := by
    rw [NativeCounter.word_value]
    exact BinaryCarry.value_lt n
  cases upper with
  | false => rfl
  | true =>
    have hu := ArithmeticSeed.one_length n.length hm
    change Counter.value (RepeatedAdd.addWord i (ArithmeticSeed.one n.length)) = Counter.value i+1
    rw [NativeCounter.word_value, RepeatedAdd.addWord_value _ _ (hi.trans hu.symm)]
    rw [← NativeCounter.word_value, ← NativeCounter.word_value,
      ArithmeticSeed.one_value, hu, Nat.mod_eq_of_lt (by omega)]

def expectedWork (A B N I : ℕ) (upper : Bool) : Fin 4 → ℕ :=
  ![A, B, A*N, B*gridIndex upper I]

theorem work_values_mod (A B : ℕ) (upper : Bool) (n i : List Bool) (j : Fin 4)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n) :
    Counter.value (workWord A B upper n i j) =
      expectedWork A B (Counter.value n) (Counter.value i) upper j % 2^n.length := by
  have hl := factorWord_length upper n i j hm hi
  have h := RepeatedAdd.repeatWord_value (factorWord upper n i j) (multiplier A B j)
    (ArithmeticSeed.zeros n.length) (by simp [ArithmeticSeed.zeros, hl])
  rw [← NativeCounter.word_value, ← NativeCounter.word_value, ← NativeCounter.word_value] at h
  simp only [ArithmeticSeed.zeros, PaddedWord.value_zeroes, Nat.zero_add, hl] at h
  change Counter.value (workWord A B upper n i j) = _ at h
  fin_cases j <;> simpa [factorWord, multiplier, expectedWork, ArithmeticSeed.one_value,
    gridWord_value upper n i hm hi hin] using h

theorem work_values_exact (A B : ℕ) (upper : Bool) (n i : List Bool) (j : Fin 4)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n)
    (hA : A*Counter.value n < 2^n.length) (hB : B*Counter.value n < 2^n.length) :
    Counter.value (workWord A B upper n i j) = expectedWork A B (Counter.value n) (Counter.value i) upper j := by
  rw [work_values_mod A B upper n i j hm hi hin]
  apply Nat.mod_eq_of_lt
  have hg : gridIndex upper (Counter.value i) ≤ Counter.value n := by
    cases upper <;> simp only [gridIndex, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hgrid := Nat.mul_le_mul_left B hg
  fin_cases j <;> simp [expectedWork] <;> nlinarith

theorem choose_numeric (upper : Bool) (a b : ℕ) :
    chooseGrid upper false (BinaryCompare.numeric .equal a b) =
      decide (if upper then b ≤ a else a ≤ b) := by
  cases upper <;> unfold chooseGrid BinaryCompare.numeric <;> split_ifs <;> simp_all
  all_goals omega

theorem choose_integer (upper : Bool) (z : ℤ) (B N J : ℕ) (hN : 0 < N) :
    chooseGrid upper (decide (z < 0)) (BinaryCompare.numeric .equal (z.natAbs*N) (B*J)) =
      decide (if upper then (J : ℤ)*B ≤ z*N else z*N ≤ (J : ℤ)*B) := by
  by_cases hz : z < 0
  · have hn : (0 : ℤ) < N := by exact_mod_cast hN
    have hneg : z*(N : ℤ) < 0 := mul_neg_of_neg_of_pos hz hn
    have hpos : (0 : ℤ) ≤ (J : ℤ)*B := by positivity
    cases upper <;> simp [chooseGrid, hz] <;> omega
  · have hz0 : 0 ≤ z := by omega
    have habs : (z.natAbs : ℤ) = z := by simp [abs_of_nonneg hz0]
    simp only [hz, decide_false, choose_numeric]
    apply decide_eq_decide.mpr
    cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals rw [← habs]
    all_goals norm_cast
    all_goals simp [Nat.mul_comm]

theorem selection_integer (z : ℤ) (B : ℕ) (upper : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n)
    (hA : z.natAbs*Counter.value n < 2^n.length) (hB : B*Counter.value n < 2^n.length) :
    selection z.natAbs B upper (decide (z < 0)) n i =
      decide (if upper then (gridIndex upper (Counter.value i) : ℤ)*B ≤ z*Counter.value n
        else z*Counter.value n ≤ (gridIndex upper (Counter.value i) : ℤ)*B) := by
  unfold selection
  rw [← NativeCounter.word_value, ← NativeCounter.word_value,
    work_values_exact _ _ _ _ _ _ hm hi hin hA hB, work_values_exact _ _ _ _ _ _ hm hi hin hA hB]
  exact choose_integer upper z B _ _ (by omega)

theorem output_values (z : ℤ) (B : ℕ) (upper grid : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n)
    (hA : z.natAbs*Counter.value n < 2^n.length) (hB : B*Counter.value n < 2^n.length) :
    (Counter.value (outputWord z.natAbs B upper (decide (z < 0)) grid n i 0),
      Counter.value (outputWord z.natAbs B upper (decide (z < 0)) grid n i 1),
      Counter.value (outputWord z.natAbs B upper (decide (z < 0)) grid n i 2)) =
      if grid then (gridIndex upper (Counter.value i), 0, Counter.value n)
      else (z.toNat, (-z).toNat, B) := by
  have h0 := work_values_exact z.natAbs B upper n i 0 hm hi hin hA hB
  have h1 := work_values_exact z.natAbs B upper n i 1 hm hi hin hA hB
  have hg := gridWord_value upper n i hm hi hin
  change Counter.value (workWord z.natAbs B upper n i 0) = z.natAbs at h0
  change Counter.value (workWord z.natAbs B upper n i 1) = B at h1
  cases grid <;> cases z <;> simp_all [outputWord, ArithmeticSeed.zeros, PaddedWord.value_zeroes]
  split_ifs <;> simp_all [PaddedWord.value_zeroes]
  omega

def clippedPair (upper : Bool) (z : ℤ) (B N I : ℕ) : ℤ × ℤ :=
  let J := gridIndex upper I
  if (if upper then (J : ℤ)*B ≤ z*N else z*N ≤ (J : ℤ)*B) then (J,N) else (z,B)

theorem clipped_output (z : ℤ) (B : ℕ) (upper : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n)
    (hA : z.natAbs*Counter.value n < 2^n.length) (hB : B*Counter.value n < 2^n.length) :
    let g := selection z.natAbs B upper (decide (z < 0)) n i
    let p := clippedPair upper z B (Counter.value n) (Counter.value i)
    (Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n i 0),
      Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n i 1),
      Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n i 2)) =
        (p.1.toNat, (-p.1).toNat, p.2.toNat) := by
  dsimp only
  rw [output_values z B upper _ n i hm hi hin hA hB, selection_integer z B upper n i hm hi hin hA hB]
  unfold clippedPair
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals split_ifs with h <;> simp_all

end TransposeFollowup.EndpointClip


/-! Specialization to the original leftPair/rightPair definitions. Fits
are derived from the map and common width, including the upper increment. -/

namespace TransposeFollowup.EndpointClip

open FixedTapeCompiler
set_option autoImplicit false

def endpoint (F : RationalMobius) (upper : Bool) : ℚ := if upper then F.hi else F.lo

theorem endpoint_bounds (F : RationalMobius) (upper : Bool) :
    (endpoint F upper).num.natAbs ≤ F.integerOperandConstant^2 ∧
      (endpoint F upper).den ≤ F.integerOperandConstant^2 := by
  cases upper
  · exact ⟨by simpa [endpoint, SeedMultiple.coefficient] using SeedMultiple.coefficient_bound F .loNum,
      by simpa [endpoint, SeedMultiple.coefficient] using SeedMultiple.coefficient_bound F .loDen⟩
  · exact ⟨by simpa [endpoint, SeedMultiple.coefficient] using SeedMultiple.coefficient_bound F .hiNum,
      by simpa [endpoint, SeedMultiple.coefficient] using SeedMultiple.coefficient_bound F .hiDen⟩

theorem endpoint_fits (F : RationalMobius) (upper : Bool) (xs : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    (endpoint F upper).num.natAbs*Counter.value n < 2^n.length ∧
      (endpoint F upper).den*Counter.value n < 2^n.length := by
  dsimp only
  rw [PaddedWord.word_length, PaddedWord.identity_value]
  exact ⟨SeedMultiple.common_small_multiple_fits F xs _ _ (endpoint_bounds F upper).1 (by omega),
    SeedMultiple.common_small_multiple_fits F xs _ _ (endpoint_bounds F upper).2 (by omega)⟩

theorem clippedPair_spec (F : RationalMobius) {N : ℕ} (i : Fin N) (upper : Bool) :
    clippedPair upper (endpoint F upper).num (endpoint F upper).den N i.val =
      if upper then F.rightPair i else F.leftPair i := by
  cases upper <;> simp [clippedPair, endpoint, gridIndex, RationalMobius.leftPair,
    RationalMobius.rightPair, Nat.cast_add, Nat.cast_one]

theorem rational_output (F : RationalMobius) (upper : Bool) (xs : List Bool)
    (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length = (PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw = i.val) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    let z := (endpoint F upper).num
    let B := (endpoint F upper).den
    let g := selection z.natAbs B upper (decide (z < 0)) n iw
    let p := if upper then F.rightPair i else F.leftPair i
    (Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n iw 0),
      Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n iw 1),
      Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n iw 2)) =
        (p.1.toNat, (-p.1).toNat, p.2.toNat) := by
  have hm : 0 < (PaddedWord.word (PaddedWord.commonConstant F) id xs).length := by
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  have hin : Counter.value iw < Counter.value (PaddedWord.word (PaddedWord.commonConstant F) id xs) := by
    rw [hv, PaddedWord.common_value]
    exact i.isLt
  have h := clipped_output (endpoint F upper).num (endpoint F upper).den upper
    (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw hm hl hin
    (endpoint_fits F upper xs).1 (endpoint_fits F upper xs).2
  simpa only [PaddedWord.common_value, hv, clippedPair_spec] using h

theorem rational_clip_trace (F : RationalMobius) (upper : Bool) (xs : List Bool)
    (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length = (PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw = i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    let z := (endpoint F upper).num
    let B := (endpoint F upper).den
    let g := selection z.natAbs B upper (decide (z < 0)) n iw
    let p := if upper then F.rightPair i else F.leftPair i
    ∃ t ≤ budget z.natAbs B n.length,
      Trace z.natAbs B upper (decide (z < 0)) t
        (cfg (.grid (.init (.erase 0))) (initial n iw) pos)
        (cfg (.done g) (final z.natAbs B upper (decide (z < 0)) n iw) pos) ∧
      (Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n iw 0),
        Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n iw 1),
        Counter.value (outputWord z.natAbs B upper (decide (z < 0)) g n iw 2)) =
          (p.1.toNat, (-p.1).toNat, p.2.toNat) ∧
      ∀ j, (outputWord z.natAbs B upper (decide (z < 0)) g n iw j).length = n.length := by
  have hm : 0 < (PaddedWord.word (PaddedWord.commonConstant F) id xs).length := by
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t, ht, htr⟩ := clip_trace (endpoint F upper).num.natAbs (endpoint F upper).den upper
    (decide ((endpoint F upper).num < 0)) (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw hm hl pos
  exact ⟨t, ht, htr, rational_output F upper xs i iw hl hv,
    fun j => outputWord_length _ _ _ _ _ _ _ hm hl j⟩

theorem total_budget (F : RationalMobius) (upper : Bool) (N : ℕ) (xs : List Bool)
    (hN : 1 ≤ N) (hl : xs.length ≤ (N+1).size) :
    let S := (endpoint F upper).num.natAbs+(endpoint F upper).den
    N*(N*budget (endpoint F upper).num.natAbs (endpoint F upper).den
      (PaddedWord.word (PaddedWord.commonConstant F) id xs).length) ≤
      ((142+72*S)*(F.integerOperandConstant^2).size+1794+928*S)*Transpose.inputLength N := by
  let S := (endpoint F upper).num.natAbs+(endpoint F upper).den
  have he : budget (endpoint F upper).num.natAbs (endpoint F upper).den
      (PaddedWord.word (PaddedWord.commonConstant F) id xs).length =
      ((71+36*S)*PaddedWord.commonConstant F+187+104*S)+(142+72*S)*xs.length := by
    rw [PaddedWord.word_length]
    unfold budget S
    ring
  have h := dense_scan_budget ((71+36*S)*PaddedWord.commonConstant F+187+104*S) (142+72*S) N hN
  rw [he]
  calc
    _ ≤ N*(N*(((71+36*S)*PaddedWord.commonConstant F+187+104*S)+(142+72*S)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.EndpointClip


/-! Strict source-boundary tests reuse the clipping products. Only one
addition and one comparison are needed. Negative endpoints use a fixed
branch. The clipped output words are framed and remain untouched. -/

namespace TransposeFollowup.EndpointGuard

open FixedTapeCompiler
open EndpointClip (Port Bank)
set_option autoImplicit false

def target (upper : Bool) : Fin 4 := if upper then 2 else 3

def addPort (upper : Bool) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .work (target upper) | .factor => .work 1
  | .scratch => .scratch | .zero => .zero

def addBinding (upper : Bool) : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort upper, by cases upper <;> decide +kernel⟩
  decode := fun p => if p = .fuel then some .fuel else if p = .work (target upper) then some .acc
    else if p = .work 1 then some .factor else if p = .scratch then some .scratch
    else if p = .zero then some .zero else none
  decode_spec := by
    intro p t
    cases upper <;> cases p <;> cases t <;> simp [addPort, target, eq_comm]
    all_goals rename_i j; fin_cases j <;> decide

def choose (upper : Bool) (r : BinaryCompare.Result) : Bool :=
  if upper then decide (r = .greater) else decide (r = .less)

inductive Label | start | add (pc : RepeatedAdd.Label) | compare (pc : BinaryCompare.Label)
  | done (answer : Bool)
  deriving DecidableEq, Fintype

def program (upper negative : Bool) : Microcode.Program Port Label
  | .start => .jump (if negative then .done (!upper) else .add (.counter 0))
  | .add (.counter pc) => if pc = 12 then .jump (.compare (.scan .equal))
      else (addBinding upper).instruction Label.add (RepeatedAdd.program (.counter pc))
  | .add pc => (addBinding upper).instruction Label.add (RepeatedAdd.program pc)
  | .compare (.done r) => .jump (.done (choose upper r))
  | .compare pc => EndpointClip.compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .done _ => .halt

theorem add_code (upper negative : Bool) (pc : RepeatedAdd.Label)
    (hh : RepeatedAdd.program pc ≠ .halt) (_ : RepeatedAdd.program pc ≠ .reject) :
    program upper negative (.add pc) = MicrocodeEmbedding.instruction (addBinding upper).ports
      Label.add (RepeatedAdd.program pc) := by
  have hp : pc ≠ .counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program, FinitePortBinding.instruction_eq]

theorem compare_code (upper negative : Bool) (pc : BinaryCompare.Label)
    (hh : BinaryCompare.program pc ≠ .halt) (_ : BinaryCompare.program pc ≠ .reject) :
    program upper negative (.compare pc) = MicrocodeEmbedding.instruction EndpointClip.compareBinding.ports
      Label.compare (BinaryCompare.program pc) := by
  cases pc <;> simp_all [program, BinaryCompare.program, FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc, fun p => (s.tapes p).denote⟩, pos⟩
def zipperCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc, s.tapes⟩, pos⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) Label.start
noncomputable def nativeMachine (upper negative : Bool) :=
  NativeMicrocode.machine nativeEncoding (program upper negative)

theorem fixed_resources (upper negative : Bool) :
    (nativeMachine upper negative).k = 14 ∧ (nativeMachine upper negative).g+1 = 5 ∧
    (nativeMachine upper negative).q+1 = 130 ∧ nativeEncoding.label .start = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 14
    decide +kernel
  · change Fintype.card Label-1+1 = 130
    decide +kernel

def adjustedWord (A B : ℕ) (upper : Bool) (n i : List Bool) (j : Fin 4) : List Bool :=
  if j = target upper then
    RepeatedAdd.addWord (EndpointClip.workWord A B upper n i j) (EndpointClip.workWord A B upper n i 1)
  else EndpointClip.workWord A B upper n i j

def updated (A B : ℕ) (upper negative : Bool) (n i : List Bool) : Bank :=
  {EndpointClip.final A B upper negative n i with work := fun j => Counter.marked (adjustedWord A B upper n i j)}

def final (A B : ℕ) (upper negative : Bool) (n i : List Bool) : Bank :=
  if negative then EndpointClip.final A B upper negative n i else updated A B upper negative n i

def answer (A B : ℕ) (upper negative : Bool) (n i : List Bool) : Bool :=
  if negative then !upper else choose upper (BinaryCompare.numeric .equal
    (BinaryCompare.value (adjustedWord A B upper n i 2)) (BinaryCompare.value (adjustedWord A B upper n i 3)))

theorem adjustedWord_length (A B : ℕ) (upper : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (j : Fin 4) :
    (adjustedWord A B upper n i j).length = n.length := by
  have hj := EndpointClip.workWord_length A B upper n i j hm hi
  have h1 := EndpointClip.workWord_length A B upper n i 1 hm hi
  unfold adjustedWord
  split_ifs
  · exact (RepeatedAdd.addWord_length _ _ (hj.trans h1.symm)).trans h1
  · exact hj

theorem final_out (A B : ℕ) (upper negative : Bool) (n i : List Bool) :
    (final A B upper negative n i).out = (EndpointClip.final A B upper negative n i).out := by
  cases negative <;> rfl

end TransposeFollowup.EndpointGuard


/-! Native traces include all three transfer steps. The negative case
executes one transfer and preserves the entire clipping bank. -/

namespace TransposeFollowup.EndpointGuard

open FixedTapeCompiler
open CopyMachine (Tape)
open EndpointClip (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def addedBank (upper : Bool) (b : RepeatedAdd.Bank) (s : Bank) : Bank :=
  {s with fuel := b.fuel, scratch := b.scratch, zero := b.zero, work := Function.update (Function.update s.work (target upper) b.acc) 1 b.factor}

theorem embed_add (upper : Bool) (pc : RepeatedAdd.Label) (b : RepeatedAdd.Bank)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (addBinding upper).ports Label.add
      (RepeatedAdd.cfg pc b (fun t => pos ((addBinding upper).ports t))) (EndpointClip.frame s pos) =
      cfg (.add pc) (addedBank upper b s) pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg EndpointClip.frame
  simp only [← (addBinding upper).values_eq_extend]
  cases upper <;> congr 2 <;> funext p <;> cases p <;> try rfl
  all_goals rename_i j; fin_cases j <;> rfl

theorem embed_compare (pc : BinaryCompare.Label) (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed EndpointClip.compareBinding.ports Label.compare
      (BinaryCompare.cfg pc a b (fun t => pos (EndpointClip.compareBinding.ports t))).denote
        (EndpointClip.frame s pos) =
      cfg (.compare pc) ((s.set (.work 2) a).set (.work 3) b) pos := by
  unfold MicrocodeEmbedding.embed BinaryCompare.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg EndpointClip.frame
  simp only [← EndpointClip.compareBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try rfl
  all_goals rename_i j; fin_cases j <;> rfl

abbrev Trace (upper negative : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program upper negative))
    (NativeMicrocode.Active (program upper negative))

theorem jump_trace (upper negative : Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program upper negative pc = .jump next) :
    Trace upper negative 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem add_call (upper negative : Bool) (a b : List Bool) (h : a.length = b.length)
    (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ 18*b.length+51,
      Trace upper negative t (cfg (.add (.counter 0)) (addedBank upper (RepeatedAdd.ready [true] a b) s) pos)
        (cfg (.add (.counter 12)) (addedBank upper (RepeatedAdd.ready [true] (RepeatedAdd.addWord a b) b) s) pos) := by
  obtain ⟨t, ht, htr⟩ := RepeatedAdd.single_add_trace a b h (fun t => pos ((addBinding upper).ports t))
  have he := MicrocodeEmbedding.trace_embed (addBinding upper).ports Label.add RepeatedAdd.program
    (program upper negative) (EndpointClip.frame s pos) (add_code upper negative) htr
  exact ⟨t, ht, by simpa only [embed_add] using he⟩

theorem add_stage (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ 18*n.length+51,
      Trace upper negative t (cfg (.add (.counter 0)) (EndpointClip.final A B upper negative n i) pos)
        (cfg (.add (.counter 12)) (updated A B upper negative n i) pos) := by
  have hj := EndpointClip.workWord_length A B upper n i (target upper) hm hi
  have h1 := EndpointClip.workWord_length A B upper n i 1 hm hi
  obtain ⟨t, ht, htr⟩ := add_call upper negative (EndpointClip.workWord A B upper n i (target upper))
    (EndpointClip.workWord A B upper n i 1) (hj.trans h1.symm) (EndpointClip.final A B upper negative n i) pos
  have hs : addedBank upper (RepeatedAdd.ready [true] (EndpointClip.workWord A B upper n i (target upper))
      (EndpointClip.workWord A B upper n i 1)) (EndpointClip.final A B upper negative n i) =
      EndpointClip.final A B upper negative n i := by
    apply Bank.ext <;> try rfl
    · simp [addedBank, RepeatedAdd.ready, h1, EndpointClip.final, EndpointClip.computed, EndpointClip.initial,
        ArithmeticSeed.zeros, Counter.marked, BinaryCompare.marked, BinaryCarry.marked]
    · funext j
      cases upper <;> fin_cases j <;> rfl
  have he : addedBank upper (RepeatedAdd.ready [true]
      (RepeatedAdd.addWord (EndpointClip.workWord A B upper n i (target upper)) (EndpointClip.workWord A B upper n i 1))
      (EndpointClip.workWord A B upper n i 1)) (EndpointClip.final A B upper negative n i) =
      updated A B upper negative n i := by
    apply Bank.ext <;> try rfl
    · simp [addedBank, RepeatedAdd.ready, h1, updated, EndpointClip.final, EndpointClip.computed, EndpointClip.initial,
        ArithmeticSeed.zeros, Counter.marked, BinaryCompare.marked, BinaryCarry.marked]
    · funext j
      cases upper <;> fin_cases j <;> rfl
  exact ⟨t, by rwa [h1] at ht, by simpa only [hs, he] using htr⟩

theorem compare_call (upper negative : Bool) (a b : List Bool) (h : a.length = b.length)
    (s : Bank) (ha : s.tapes (.work 2) = Counter.marked a) (hb : s.tapes (.work 3) = Counter.marked b)
    (pos : Port → ℤ) :
    ∃ t ≤ 5*a.length+6, Trace upper negative t (cfg (.compare (.scan .equal)) s pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (BinaryCompare.value a) (BinaryCompare.value b)))) s pos) := by
  obtain ⟨t, ht, htr⟩ := BinaryCompare.comparison_trace a b h (fun t => pos (EndpointClip.compareBinding.ports t))
  have he := MicrocodeEmbedding.trace_embed EndpointClip.compareBinding.ports Label.compare BinaryCompare.program
    (program upper negative) (EndpointClip.frame s pos) (compare_code upper negative) htr
  have hmarked (w : List Bool) : BinaryCompare.marked w = Counter.marked w := rfl
  exact ⟨t, ht, by simpa only [embed_compare, hmarked, ← ha, Bank.set_self, ← hb] using he⟩

def budget (m : ℕ) := 23*m+60

theorem guard_trace (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ) :
    ∃ t ≤ budget n.length,
      Trace upper negative t (cfg .start (EndpointClip.final A B upper negative n i) pos)
        (cfg (.done (answer A B upper negative n i)) (final A B upper negative n i) pos) := by
  cases negative with
  | true =>
    exact ⟨1, by unfold budget; omega, jump_trace upper true .start (.done (!upper)) _ pos rfl⟩
  | false =>
    have hstart := jump_trace upper false .start (.add (.counter 0)) (EndpointClip.final A B upper false n i) pos rfl
    obtain ⟨a, ha, hadd⟩ := add_stage A B upper false n i hm hi pos
    have hjump := jump_trace upper false (.add (.counter 12)) (.compare (.scan .equal)) (updated A B upper false n i) pos rfl
    have h2 := adjustedWord_length A B upper n i hm hi 2
    have h3 := adjustedWord_length A B upper n i hm hi 3
    obtain ⟨b, hb, hcmp⟩ := compare_call upper false (adjustedWord A B upper n i 2) (adjustedWord A B upper n i 3)
      (h2.trans h3.symm) (updated A B upper false n i) rfl rfl pos
    have hfinish := jump_trace upper false
      (.compare (.done (BinaryCompare.numeric .equal (BinaryCompare.value (adjustedWord A B upper n i 2))
        (BinaryCompare.value (adjustedWord A B upper n i 3)))))
      (.done (answer A B upper false n i)) (updated A B upper false n i) pos rfl
    exact ⟨1+(a+(1+(b+1))), by rw [h2] at hb; unfold budget; omega,
      trace_trans hstart (trace_trans hadd (trace_trans hjump (trace_trans hcmp hfinish)))⟩

theorem native_guard (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget n.length,
      Transpose.stepN (nativeMachine upper negative) input t
        ((cfg .start (EndpointClip.final A B upper negative n i) pos).denote
          nativeEncoding (program upper negative) inputPos outRev) =
        some ((cfg (.done (answer A B upper negative n i)) (final A B upper negative n i) pos).denote
          nativeEncoding (program upper negative) inputPos outRev) ∧
      Transpose.step (nativeMachine upper negative) input
        ((cfg (.done (answer A B upper negative n i)) (final A B upper negative n i) pos).denote
          nativeEncoding (program upper negative) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := guard_trace A B upper negative n i hm hi pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN nativeEncoding (program upper negative) input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding (program upper negative) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (A B : ℕ) (upper negative : Bool)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (targetProgram : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program upper negative pc ≠ .halt → program upper negative pc ≠ .reject →
      targetProgram (labels pc) = MicrocodeEmbedding.instruction ports labels (program upper negative pc))
    (n i : List Bool) (hm : 0 < n.length) (hi : i.length = n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget n.length,
      Transpose.stepN (NativeMicrocode.machine encoding targetProgram) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .start (EndpointClip.final A B upper negative n i) pos) frame).denote
          encoding targetProgram inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (answer A B upper negative n i)) (final A B upper negative n i) pos) frame).denote
            encoding targetProgram inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := guard_trace A B upper negative n i hm hi pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program upper negative)
    targetProgram frame input inputPos outRev hc htr⟩

end TransposeFollowup.EndpointGuard


/-! Arithmetic meaning of the actual guard. Fit is required for the single
new sum, in addition to the clipping products. No subtraction is used. -/

namespace TransposeFollowup.EndpointGuard

open FixedTapeCompiler
set_option autoImplicit false

def sumValue (A B N I : ℕ) (upper : Bool) : ℕ :=
  EndpointClip.expectedWork A B N I upper (target upper)+B

theorem adjustedWord_value (A B : ℕ) (upper : Bool) (n i : List Bool) (j : Fin 4)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n)
    (hA : A*Counter.value n < 2^n.length) (hB : B*Counter.value n < 2^n.length)
    (hs : sumValue A B (Counter.value n) (Counter.value i) upper < 2^n.length) :
    Counter.value (adjustedWord A B upper n i j) =
      EndpointClip.expectedWork A B (Counter.value n) (Counter.value i) upper j+
        (if j = target upper then B else 0) := by
  have hj := EndpointClip.workWord_length A B upper n i j hm hi
  have h1 := EndpointClip.workWord_length A B upper n i 1 hm hi
  have hv1 := EndpointClip.work_values_exact A B upper n i 1 hm hi hin hA hB
  change Counter.value (EndpointClip.workWord A B upper n i 1) = B at hv1
  unfold adjustedWord
  split_ifs with h
  · rw [NativeCounter.word_value, RepeatedAdd.addWord_value _ _ (hj.trans h1.symm),
      ← NativeCounter.word_value, ← NativeCounter.word_value,
      EndpointClip.work_values_exact A B upper n i j hm hi hin hA hB, hv1, h1]
    apply Nat.mod_eq_of_lt
    simpa only [h, sumValue] using hs
  · simpa using EndpointClip.work_values_exact A B upper n i j hm hi hin hA hB

theorem choose_numeric (upper : Bool) (a b : ℕ) :
    choose upper (BinaryCompare.numeric .equal a b) = decide (if upper then b<a else a<b) := by
  cases upper <;> unfold choose BinaryCompare.numeric <;> split_ifs <;> simp_all
  all_goals omega

def integerCondition (upper : Bool) (z : ℤ) (B N I : ℕ) : Prop :=
  if upper then (I : ℤ)*B<z*N else z*N<((I : ℤ)+1)*B
instance (upper : Bool) (z : ℤ) (B N I : ℕ) : Decidable (integerCondition upper z B N I) :=
  inferInstanceAs (Decidable (if upper then (I : ℤ)*B<z*N else z*N<((I : ℤ)+1)*B))

theorem answer_integer (z : ℤ) (B : ℕ) (upper : Bool) (n i : List Bool)
    (hm : 0 < n.length) (hi : i.length = n.length) (hin : Counter.value i < Counter.value n)
    (hA : z.natAbs*Counter.value n < 2^n.length) (hB : B*Counter.value n < 2^n.length)
    (hs : sumValue z.natAbs B (Counter.value n) (Counter.value i) upper < 2^n.length) :
    answer z.natAbs B upper (decide (z<0)) n i =
      decide (integerCondition upper z B (Counter.value n) (Counter.value i)) := by
  by_cases hz : z<0
  · have hn : (0 : ℤ)<Counter.value n := by exact_mod_cast (show 0<Counter.value n by omega)
    have hneg := mul_neg_of_neg_of_pos hz hn
    have h0 : (0 : ℤ)≤(Counter.value i : ℤ)*B := by positivity
    have h1 : (0 : ℤ)≤((Counter.value i : ℤ)+1)*B := by positivity
    cases upper <;> simp [answer, integerCondition, hz] <;> omega
  · have hz0 : 0≤z := by omega
    have habs : (z.natAbs : ℤ)=z := by simp [abs_of_nonneg hz0]
    simp only [answer, hz, decide_false, Bool.false_eq_true, ite_false, choose_numeric]
    rw [← NativeCounter.word_value, ← NativeCounter.word_value,
      adjustedWord_value _ _ _ _ _ _ hm hi hin hA hB hs,
      adjustedWord_value _ _ _ _ _ _ hm hi hin hA hB hs]
    apply decide_eq_decide.mpr
    unfold integerCondition
    cases upper <;> simp [EndpointClip.expectedWork, target, EndpointClip.gridIndex]
    all_goals
      conv_rhs => rw [← habs]
      norm_cast
      constructor <;> intro h <;> nlinarith

end TransposeFollowup.EndpointGuard


/-! Derive the new sum's fit from the map, identify the exact rational
boundary test, and combine both tests into the row's source-open flag. -/

namespace TransposeFollowup.EndpointGuard

open FixedTapeCompiler
open EndpointClip (Port)
set_option autoImplicit false

theorem sumValue_bound (A B E N I : ℕ) (upper : Bool) (hA : A≤E) (hB : B≤E) (hi : I≤N) :
    sumValue A B N I upper ≤ E*(N+1) := by
  have ha := Nat.mul_le_mul_right N hA
  have hb := Nat.mul_le_mul_right I hB
  have hni := Nat.mul_le_mul_left E hi
  cases upper <;> simp [sumValue, EndpointClip.expectedWork, target, EndpointClip.gridIndex] <;> nlinarith

theorem common_sum_fits (F : RationalMobius) (upper : Bool) (xs iw : List Bool)
    (hi : Counter.value iw < Counter.value xs) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    sumValue (EndpointClip.endpoint F upper).num.natAbs (EndpointClip.endpoint F upper).den
      (Counter.value n) (Counter.value iw) upper < 2^n.length := by
  dsimp only
  rw [PaddedWord.common_value, PaddedWord.word_length]
  have h := EndpointClip.endpoint_bounds F upper
  exact (sumValue_bound _ _ _ _ _ upper h.1 h.2 (by omega)).trans_lt
    (SeedMultiple.common_small_multiple_fits F xs _ (Counter.value xs+1) (by rfl) (by rfl))

def boundary (F : RationalMobius) {N : ℕ} (i : Fin N) (upper : Bool) : Prop :=
  if upper then (i.val : ℚ)/N < F.hi else F.lo < ((i.val : ℚ)+1)/N
instance (F : RationalMobius) {N : ℕ} (i : Fin N) (upper : Bool) : Decidable (boundary F i upper) :=
  inferInstanceAs (Decidable (if upper then (i.val : ℚ)/N < F.hi else F.lo < ((i.val : ℚ)+1)/N))

theorem boundary_integer (F : RationalMobius) {N : ℕ} (i : Fin N) (upper : Bool) :
    boundary F i upper ↔ integerCondition upper (EndpointClip.endpoint F upper).num
      (EndpointClip.endpoint F upper).den N i.val := by
  have hn : (0 : ℚ)<N := by exact_mod_cast (show 0<N by have := i.isLt; omega)
  cases upper with
  | false =>
    change F.lo < ((i.val : ℚ)+1)/N ↔ F.lo.num*(N : ℤ)<((i.val : ℤ)+1)*F.lo.den
    conv_lhs => lhs; rw [← F.lo.num_div_den]
    rw [div_lt_div_iff₀ (by exact_mod_cast F.lo.den_pos) hn]
    norm_cast
  | true =>
    change (i.val : ℚ)/N < F.hi ↔ (i.val : ℤ)*F.hi.den<F.hi.num*(N : ℤ)
    conv_lhs => rhs; rw [← F.hi.num_div_den]
    rw [div_lt_div_iff₀ hn (by exact_mod_cast F.hi.den_pos)]
    norm_cast

theorem source_open_iff (F : RationalMobius) {N : ℕ} (i : Fin N) :
    F.sourceLeft i < F.sourceRight i ↔ boundary F i false ∧ boundary F i true := by
  have hn : (0 : ℚ)<N := by exact_mod_cast (show 0<N by have := i.isLt; omega)
  have hcell : (i.val : ℚ)/N < ((i.val : ℚ)+1)/N := (div_lt_div_iff_of_pos_right hn).mpr (by linarith)
  have hf := F.interval_nonempty
  simp only [RationalMobius.sourceLeft, RationalMobius.sourceRight, max_lt_iff, lt_min_iff,
    boundary, Bool.false_eq_true, ite_false, ite_true]
  tauto

theorem answer_rational (F : RationalMobius) (upper : Bool) (xs : List Bool)
    (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length = (PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw = i.val) :
    answer (EndpointClip.endpoint F upper).num.natAbs (EndpointClip.endpoint F upper).den upper
      (decide ((EndpointClip.endpoint F upper).num<0)) (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw =
      decide (boundary F i upper) := by
  have hm : 0 < (PaddedWord.word (PaddedWord.commonConstant F) id xs).length := by
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  have hin : Counter.value iw < Counter.value xs := by rw [hv]; exact i.isLt
  rw [answer_integer _ _ _ _ _ hm hl (by simpa only [PaddedWord.common_value] using hin)
    (EndpointClip.endpoint_fits F upper xs).1 (EndpointClip.endpoint_fits F upper xs).2
    (common_sum_fits F upper xs iw hin), PaddedWord.common_value, hv]
  exact decide_eq_decide.mpr (boundary_integer F i upper).symm

theorem both_answers (F : RationalMobius) (xs : List Bool) (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length = (PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw = i.val) :
    (answer F.lo.num.natAbs F.lo.den false (decide (F.lo.num<0))
      (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw &&
     answer F.hi.num.natAbs F.hi.den true (decide (F.hi.num<0))
      (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw) =
      (F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight := by
  have h0 := answer_rational F false xs i iw hl hv
  have h1 := answer_rational F true xs i iw hl hv
  simp only [EndpointClip.endpoint, Bool.false_eq_true, ite_false, ite_true] at h0 h1
  rw [h0, h1]
  have hs := congrArg RowCrossingTest.sourceOpen (F.componentRow_integerTest i)
  change (F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight =
    decide ((F.leftPair i).1*(F.rightPair i).2 < (F.rightPair i).1*(F.leftPair i).2) at hs
  rw [hs]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact (source_open_iff F i).symm.trans (F.sourcePair_lt_iff i).symm

theorem rational_guard_trace (F : RationalMobius) (upper : Bool) (xs : List Bool)
    (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length = (PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw = i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    let z := (EndpointClip.endpoint F upper).num
    let B := (EndpointClip.endpoint F upper).den
    ∃ t ≤ budget n.length,
      Trace upper (decide (z<0)) t (cfg .start (EndpointClip.final z.natAbs B upper (decide (z<0)) n iw) pos)
        (cfg (.done (decide (boundary F i upper))) (final z.natAbs B upper (decide (z<0)) n iw) pos) := by
  have hm : 0 < (PaddedWord.word (PaddedWord.commonConstant F) id xs).length := by
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t, ht, htr⟩ := guard_trace (EndpointClip.endpoint F upper).num.natAbs (EndpointClip.endpoint F upper).den
    upper (decide ((EndpointClip.endpoint F upper).num<0))
    (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw hm hl pos
  exact ⟨t, ht, by simpa only [answer_rational F upper xs i iw hl hv] using htr⟩

theorem total_budget (F : RationalMobius) (N : ℕ) (xs : List Bool)
    (hN : 1≤N) (hl : xs.length≤(N+1).size) :
    N*(N*budget (PaddedWord.word (PaddedWord.commonConstant F) id xs).length) ≤
      (46*(F.integerOperandConstant^2).size+580)*Transpose.inputLength N := by
  have he : budget (PaddedWord.word (PaddedWord.commonConstant F) id xs).length =
      (23*PaddedWord.commonConstant F+60)+46*xs.length := by
    rw [PaddedWord.word_length]
    unfold budget
    ring
  have h := dense_scan_budget (23*PaddedWord.commonConstant F+60) 46 N hN
  rw [he]
  calc
    _ ≤ N*(N*((23*PaddedWord.commonConstant F+60)+46*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.EndpointGuard


/-! One actual caller combines paid clipping with the strict guard. The
transfer is charged; outputs, products and absolute heads have one final
bank, so the guard is not supplied as a precomputed input. -/

namespace TransposeFollowup.GuardedEndpoint

open FixedTapeCompiler
open EndpointClip (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

abbrev Label (A B : ℕ) := EndpointClip.Label A B ⊕ EndpointGuard.Label

def binding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

def program (A B : ℕ) (upper negative : Bool) : Microcode.Program Port (Label A B)
  | .inl (.done _) => .jump (.inr .start)
  | .inl pc => binding.instruction Sum.inl (EndpointClip.program A B upper negative pc)
  | .inr pc => binding.instruction Sum.inr (EndpointGuard.program upper negative pc)

theorem clip_code (A B : ℕ) (upper negative : Bool) (pc : EndpointClip.Label A B)
    (hh : EndpointClip.program A B upper negative pc ≠ .halt)
    (_ : EndpointClip.program A B upper negative pc ≠ .reject) :
    program A B upper negative (.inl pc) = MicrocodeEmbedding.instruction binding.ports
      Sum.inl (EndpointClip.program A B upper negative pc) := by
  cases pc <;> simp_all [program, EndpointClip.program, FinitePortBinding.instruction_eq]

theorem guard_code (A B : ℕ) (upper negative : Bool) (pc : EndpointGuard.Label) :
    program A B upper negative (.inr pc) = MicrocodeEmbedding.instruction binding.ports
      Sum.inr (EndpointGuard.program upper negative pc) := binding.instruction_eq _ _

def cfg {A B : ℕ} (pc : Label A B) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label A B) :=
  ⟨⟨pc, fun p => (s.tapes p).denote⟩, pos⟩
def zipperCfg {A B : ℕ} (pc : Label A B) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label A B) :=
  ⟨⟨pc, s.tapes⟩, pos⟩

noncomputable def nativeEncoding (A B : ℕ) :=
  NativeMicrocode.initialEncoding (T := Port) (Sum.inl (β := EndpointGuard.Label)
    (EndpointClip.Label.grid (A := A) (B := B) (.init (.erase 0))))
noncomputable def nativeMachine (A B : ℕ) (upper negative : Bool) :=
  NativeMicrocode.machine (nativeEncoding A B) (program A B upper negative)

theorem fixed_resources (A B : ℕ) (upper negative : Bool) :
    (nativeMachine A B upper negative).k = 14 ∧ (nativeMachine A B upper negative).g+1 = 5 ∧
    (nativeMachine A B upper negative).q+1 = 198*(A+B)+923 ∧
    (nativeEncoding A B).label (.inl (.grid (.init (.erase 0)))) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 14
    decide +kernel
  · have hg : Fintype.card EndpointGuard.Label = 130 := by decide +kernel
    change Fintype.card (EndpointClip.Label A B ⊕ EndpointGuard.Label)-1+1 = _
    rw [Fintype.card_sum, EndpointClip.label_card, hg]
    omega

theorem embed_clip (A B : ℕ) (pc : EndpointClip.Label A B) (s : Bank) (pos : Port → ℤ) (frame : MicrocodeEmbedding.Frame Port) :
    MicrocodeEmbedding.embed binding.ports Sum.inl (EndpointClip.cfg pc s pos) frame =
      cfg (.inl pc) s pos := by
  unfold MicrocodeEmbedding.embed EndpointClip.cfg cfg
  simp only [← binding.values_eq_extend]
  rfl

theorem embed_guard (A B : ℕ) (pc : EndpointGuard.Label) (s : Bank) (pos : Port → ℤ) (frame : MicrocodeEmbedding.Frame Port) :
    MicrocodeEmbedding.embed binding.ports (Sum.inr (α := EndpointClip.Label A B))
      (EndpointGuard.cfg pc s pos) frame = cfg (.inr pc) s pos := by
  unfold MicrocodeEmbedding.embed EndpointGuard.cfg cfg
  simp only [← binding.values_eq_extend]
  rfl

abbrev Trace (A B : ℕ) (upper negative : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program A B upper negative))
    (NativeMicrocode.Active (program A B upper negative))

def budget (A B m : ℕ) := EndpointClip.budget A B m+1+EndpointGuard.budget m

theorem complete_trace (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ) :
    ∃ t ≤ budget A B n.length,
      Trace A B upper negative t (cfg (.inl (.grid (.init (.erase 0)))) (EndpointClip.initial n i) pos)
        (cfg (.inr (.done (EndpointGuard.answer A B upper negative n i)))
          (EndpointGuard.final A B upper negative n i) pos) := by
  obtain ⟨a, ha, hclip⟩ := EndpointClip.clip_trace A B upper negative n i hm hi pos
  have hc := MicrocodeEmbedding.trace_embed binding.ports Sum.inl (EndpointClip.program A B upper negative)
    (program A B upper negative) (EndpointClip.frame (EndpointClip.initial n i) pos)
    (clip_code A B upper negative) hclip
  simp only [embed_clip] at hc
  have hj : Trace A B upper negative 1
      (cfg (.inl (.done (EndpointClip.selection A B upper negative n i))) (EndpointClip.final A B upper negative n i) pos)
      (cfg (.inr .start) (EndpointClip.final A B upper negative n i) pos) := by
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active, cfg, program]
    · change Trace A B upper negative 0
        (NativeMicrocode.step (program A B upper negative)
          (cfg (.inl (.done (EndpointClip.selection A B upper negative n i))) (EndpointClip.final A B upper negative n i) pos)) _
      have he : NativeMicrocode.step (program A B upper negative)
          (cfg (.inl (.done (EndpointClip.selection A B upper negative n i))) (EndpointClip.final A B upper negative n i) pos) =
          cfg (.inr .start) (EndpointClip.final A B upper negative n i) pos := by
        simp [NativeMicrocode.step, Microcode.actualStep, cfg, program]
      rw [he]
      exact .refl _
  obtain ⟨b, hb, hguard⟩ := EndpointGuard.guard_trace A B upper negative n i hm hi pos
  have hg := MicrocodeEmbedding.trace_embed binding.ports Sum.inr (EndpointGuard.program upper negative)
    (program A B upper negative) (EndpointClip.frame (EndpointClip.initial n i) pos)
    (fun pc _ _ => guard_code A B upper negative pc) hguard
  simp only [embed_guard] at hg
  exact ⟨a+(1+b), by unfold budget; omega, trace_trans hc (trace_trans hj hg)⟩

theorem native_complete (A B : ℕ) (upper negative : Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget A B n.length,
      Transpose.stepN (nativeMachine A B upper negative) input t
        ((cfg (.inl (.grid (.init (.erase 0)))) (EndpointClip.initial n i) pos).denote
          (nativeEncoding A B) (program A B upper negative) inputPos outRev) =
        some ((cfg (.inr (.done (EndpointGuard.answer A B upper negative n i)))
          (EndpointGuard.final A B upper negative n i) pos).denote
            (nativeEncoding A B) (program A B upper negative) inputPos outRev) ∧
      Transpose.step (nativeMachine A B upper negative) input
        ((cfg (.inr (.done (EndpointGuard.answer A B upper negative n i)))
          (EndpointGuard.final A B upper negative n i) pos).denote
            (nativeEncoding A B) (program A B upper negative) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := complete_trace A B upper negative n i hm hi pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding A B) (program A B upper negative)
    input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding A B) (program A B upper negative) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (A B : ℕ) (upper negative : Bool)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label A B → J)
    (targetProgram : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program A B upper negative pc ≠ .halt → program A B upper negative pc ≠ .reject →
      targetProgram (labels pc) = MicrocodeEmbedding.instruction ports labels (program A B upper negative pc))
    (n i : List Bool) (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget A B n.length,
      Transpose.stepN (NativeMicrocode.machine encoding targetProgram) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (.inl (.grid (.init (.erase 0)))) (EndpointClip.initial n i) pos) frame).denote
          encoding targetProgram inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.inr (.done (EndpointGuard.answer A B upper negative n i)))
            (EndpointGuard.final A B upper negative n i) pos) frame).denote encoding targetProgram inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := complete_trace A B upper negative n i hm hi pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program A B upper negative)
    targetProgram frame input inputPos outRev hc htr⟩

theorem total_budget (F : RationalMobius) (upper : Bool) (N : ℕ) (xs : List Bool)
    (hN : 1≤N) (hl : xs.length≤(N+1).size) :
    let S := (EndpointClip.endpoint F upper).num.natAbs+(EndpointClip.endpoint F upper).den
    N*(N*budget (EndpointClip.endpoint F upper).num.natAbs (EndpointClip.endpoint F upper).den
      (PaddedWord.word (PaddedWord.commonConstant F) id xs).length) ≤
      ((188+72*S)*(F.integerOperandConstant^2).size+2376+928*S)*Transpose.inputLength N := by
  let S := (EndpointClip.endpoint F upper).num.natAbs+(EndpointClip.endpoint F upper).den
  have he : budget (EndpointClip.endpoint F upper).num.natAbs (EndpointClip.endpoint F upper).den
      (PaddedWord.word (PaddedWord.commonConstant F) id xs).length =
      ((94+36*S)*PaddedWord.commonConstant F+248+104*S)+(188+72*S)*xs.length := by
    rw [PaddedWord.word_length]
    unfold budget EndpointClip.budget EndpointGuard.budget S
    ring
  have h := dense_scan_budget ((94+36*S)*PaddedWord.commonConstant F+248+104*S) (188+72*S) N hN
  rw [he]
  calc
    _ ≤ N*(N*(((94+36*S)*PaddedWord.commonConstant F+248+104*S)+(188+72*S)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.GuardedEndpoint


/-! The combined native execution computes both the original clipped
fraction and its strict source-boundary flag. All output words have the
common proved width. The remaining product workspace is explicit. -/

namespace TransposeFollowup.GuardedEndpoint

open FixedTapeCompiler
open EndpointClip (Port)
set_option autoImplicit false

theorem rational_complete_trace (F : RationalMobius) (upper : Bool) (xs : List Bool)
    (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length = (PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw = i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    let z := (EndpointClip.endpoint F upper).num
    let B := (EndpointClip.endpoint F upper).den
    let p := if upper then F.rightPair i else F.leftPair i
    ∃ t ≤ budget z.natAbs B n.length, ∃ w : Fin 3 → List Bool,
      Trace z.natAbs B upper (decide (z<0)) t
        (cfg (.inl (.grid (.init (.erase 0)))) (EndpointClip.initial n iw) pos)
        (cfg (.inr (.done (decide (EndpointGuard.boundary F i upper))))
          (EndpointGuard.final z.natAbs B upper (decide (z<0)) n iw) pos) ∧
      (∀ j, (EndpointGuard.final z.natAbs B upper (decide (z<0)) n iw).out j = Counter.marked (w j)) ∧
      (Counter.value (w 0), Counter.value (w 1), Counter.value (w 2)) =
        (p.1.toNat, (-p.1).toNat, p.2.toNat) ∧ ∀ j, (w j).length=n.length := by
  have hm : 0 < (PaddedWord.word (PaddedWord.commonConstant F) id xs).length := by
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t, ht, htr⟩ := complete_trace (EndpointClip.endpoint F upper).num.natAbs
    (EndpointClip.endpoint F upper).den upper (decide ((EndpointClip.endpoint F upper).num<0))
    (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw hm hl pos
  refine ⟨t, ht, fun j => EndpointClip.outputWord (EndpointClip.endpoint F upper).num.natAbs
    (EndpointClip.endpoint F upper).den upper (decide ((EndpointClip.endpoint F upper).num<0))
    (EndpointClip.selection (EndpointClip.endpoint F upper).num.natAbs (EndpointClip.endpoint F upper).den
      upper (decide ((EndpointClip.endpoint F upper).num<0))
      (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw)
    (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw j, ?_, ?_, ?_, ?_⟩
  · simpa only [EndpointGuard.answer_rational F upper xs i iw hl hv] using htr
  · intro j
    rw [EndpointGuard.final_out]
    exact EndpointClip.final_out _ _ _ _ _ _ j
  · exact EndpointClip.rational_output F upper xs i iw hl hv
  · intro j
    exact EndpointClip.outputWord_length _ _ _ _ _ _ _ hm hl j

end TransposeFollowup.GuardedEndpoint


/-! A shared fourteen-tape bank plus three separate upper-endpoint outputs.
Only the grid and four work products are erased between the two calls. -/

namespace TransposeFollowup.SourceEndpoints

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

inductive Port | shared (p : EndpointClip.Port) | other (j : Fin 3)
  deriving DecidableEq, Fintype

@[ext] structure Bank where
  base : EndpointClip.Bank
  other : Fin 3 → Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .shared p => s.base.tapes p | .other j => s.other j

def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank :=
  match p with
  | .shared q => {s with base := s.base.set q w}
  | .other j => {s with other := Function.update s.other j w}

@[simp] theorem Bank.set_tapes (s : Bank) (p q : Port) (w : Tape Bool) :
    (s.set p w).tapes q = Function.update s.tapes p w q := by
  cases p <;> cases q <;> simp [Bank.set, Bank.tapes, Function.update]

@[simp] theorem Bank.set_self (s : Bank) (p : Port) : s.set p (s.tapes p) = s := by
  cases p <;> simp [Bank.set, Bank.tapes]

def initial (n i : List Bool) : Bank := ⟨EndpointClip.initial n i, fun _ => ⟨[], []⟩⟩

def place (upper : Bool) (b : EndpointClip.Bank) (s : Bank) : Bank :=
  if upper then ⟨{b with out := s.base.out}, b.out⟩ else ⟨b, s.other⟩

def afterLower (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) : Bank :=
  place false (EndpointGuard.final (A false) (B false) false (negative false) n i) (initial n i)

def erasePort (j : Fin 5) : Port :=
  ![.shared .grid, .shared (.work 0), .shared (.work 1), .shared (.work 2), .shared (.work 3)] j

def lowerWork (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) (j : Fin 4) : List Bool :=
  if negative false then EndpointClip.workWord (A false) (B false) false n i j
  else EndpointGuard.adjustedWord (A false) (B false) false n i j

def eraseWord (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) (j : Fin 5) : List Bool :=
  ![i, lowerWork A B negative n i 0, lowerWork A B negative n i 1,
    lowerWork A B negative n i 2, lowerWork A B negative n i 3] j

def eraseStage (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) (k : ℕ) : Bank :=
  let s := afterLower A B negative n i
  ⟨{s.base with grid := if 0<k then ⟨[], []⟩ else s.base.grid, work := fun j => if j.val+1<k then ⟨[], []⟩ else s.base.work j}, s.other⟩

def final (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) : Bank :=
  place true (EndpointGuard.final (A true) (B true) true (negative true) n i)
    (eraseStage A B negative n i 5)

def answer (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) : Bool :=
  EndpointGuard.answer (A false) (B false) false (negative false) n i &&
    EndpointGuard.answer (A true) (B true) true (negative true) n i

theorem eraseWord_length (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (j : Fin 5) :
    (eraseWord A B negative n i j).length=n.length := by
  have hw (k : Fin 4) := EndpointClip.workWord_length (A false) (B false) false n i k hm hi
  have hg (k : Fin 4) := EndpointGuard.adjustedWord_length (A false) (B false) false n i hm hi k
  cases h : negative false <;> fin_cases j <;> simp [eraseWord, lowerWork, h, hw, hg, hi]

theorem eraseStage_zero (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) :
    eraseStage A B negative n i 0 = afterLower A B negative n i := by
  simp [eraseStage]

theorem eraseStage_source (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) (j : Fin 5) :
    (eraseStage A B negative n i j.val).tapes (erasePort j) = Counter.marked (eraseWord A B negative n i j) := by
  fin_cases j <;> cases h : negative false <;>
    simp [eraseStage, erasePort, eraseWord, lowerWork, afterLower, place, Bank.tapes,
      EndpointGuard.final, EndpointGuard.updated, EndpointClip.final, EndpointClip.computed,
      EndpointClip.initial, EndpointClip.Bank.tapes, EndpointClip.gridWord, h]

theorem eraseStage_step (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) (j : Fin 5) :
    (eraseStage A B negative n i j.val).set (erasePort j) ⟨[], []⟩ =
      eraseStage A B negative n i (j.val+1) := by
  fin_cases j
  all_goals
    apply Bank.ext
    · apply EndpointClip.Bank.ext <;> try rfl
      all_goals funext k; fin_cases k <;> rfl
    · rfl

theorem upper_initial (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) :
    place true (EndpointClip.initial n i) (eraseStage A B negative n i 5) =
      eraseStage A B negative n i 5 := by
  cases h : negative false
  all_goals
    apply Bank.ext
    · apply EndpointClip.Bank.ext
      all_goals simp [place, eraseStage, afterLower, EndpointGuard.final, h, EndpointGuard.updated,
        EndpointClip.final, EndpointClip.computed, EndpointClip.initial]
      funext j
      have hj : j.val+1<5 := by omega
      simp [hj]
    · rfl

theorem final_lower (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) :
    (final A B negative n i).base.out =
      (EndpointClip.final (A false) (B false) false (negative false) n i).out := by
  change (EndpointGuard.final (A false) (B false) false (negative false) n i).out = _
  exact EndpointGuard.final_out _ _ _ _ _ _

theorem final_upper (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool) :
    (final A B negative n i).other =
      (EndpointClip.final (A true) (B true) true (negative true) n i).out := by
  change (EndpointGuard.final (A true) (B true) true (negative true) n i).out = _
  exact EndpointGuard.final_out _ _ _ _ _ _

end TransposeFollowup.SourceEndpoints


/-! The lower Boolean is retained in finitely many labels throughout paid
cleanup and the upper call. Neither endpoint output is used as workspace. -/

namespace TransposeFollowup.SourceEndpoints

open FixedTapeCompiler
set_option autoImplicit false

def endpointPort (upper : Bool) : EndpointClip.Port → Port
  | .out j => if upper then .other j else .shared (.out j)
  | p => .shared p

def endpointBinding (upper : Bool) : FinitePortBinding EndpointClip.Port Port where
  ports := ⟨endpointPort upper, by
    intro p q h
    cases upper <;> cases p <;> cases q <;> simp_all [endpointPort]⟩
  decode := fun p => match p with
    | .shared (.out j) => if upper then none else some (.out j)
    | .shared q => some q
    | .other j => if upper then some (.out j) else none
  decode_spec := by
    intro p q
    change (match p with
      | .shared (.out j) => if upper then none else some (.out j)
      | .shared r => some r
      | .other j => if upper then some (.out j) else none) = some q ↔ endpointPort upper q = p
    cases upper <;> cases p with
    | shared p => cases p <;> cases q <;> simp [endpointPort, eq_comm]
    | other j => cases q <;> simp [endpointPort, eq_comm]

def eraseBinding (j : Fin 5) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => erasePort j, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=erasePort j then some 0 else none
  decode_spec := by
    intro p t
    change (if p=erasePort j then some (0 : Fin 1) else none)=some t ↔ erasePort j=p
    fin_cases t
    simp [eq_comm]

inductive Label (A B : Bool → ℕ)
  | lower (pc : GuardedEndpoint.Label (A false) (B false))
  | erase (saved : Bool) (j : Fin 5) (pc : NativeErase.Label)
  | upper (saved : Bool) (pc : GuardedEndpoint.Label (A true) (B true))
  | done (answer : Bool)
  deriving DecidableEq, Fintype

def afterErase (A B : Bool → ℕ) (saved : Bool) (j : Fin 5) : Label A B :=
  if h : j.val<4 then .erase saved ⟨j.val+1, by omega⟩ 2
  else .upper saved (.inl (.grid (.init (.erase 0))))

def program (A B : Bool → ℕ) (negative : Bool → Bool) : Microcode.Program Port (Label A B)
  | .lower (.inr (.done a)) => .jump (.erase a 0 2)
  | .lower pc => (endpointBinding false).instruction Label.lower
      (GuardedEndpoint.program (A false) (B false) false (negative false) pc)
  | .erase saved j pc => if pc=0 then .jump (afterErase A B saved j)
      else (eraseBinding j).instruction (Label.erase saved j) (NativeErase.program pc)
  | .upper saved (.inr (.done b)) => .jump (.done (saved && b))
  | .upper saved pc => (endpointBinding true).instruction (Label.upper saved)
      (GuardedEndpoint.program (A true) (B true) true (negative true) pc)
  | .done _ => .halt

theorem lower_code (A B : Bool → ℕ) (negative : Bool → Bool) (pc : GuardedEndpoint.Label (A false) (B false))
    (hh : GuardedEndpoint.program (A false) (B false) false (negative false) pc ≠ .halt)
    (_ : GuardedEndpoint.program (A false) (B false) false (negative false) pc ≠ .reject) :
    program A B negative (.lower pc) = MicrocodeEmbedding.instruction (endpointBinding false).ports
      Label.lower (GuardedEndpoint.program (A false) (B false) false (negative false) pc) := by
  rcases pc with pc | pc
  · exact (endpointBinding false).instruction_eq _ _
  · cases pc <;> simp_all [program, GuardedEndpoint.program, EndpointGuard.program, FinitePortBinding.instruction_eq]
    exact False.elim (hh rfl)

theorem upper_code (A B : Bool → ℕ) (negative : Bool → Bool) (saved : Bool)
    (pc : GuardedEndpoint.Label (A true) (B true))
    (hh : GuardedEndpoint.program (A true) (B true) true (negative true) pc ≠ .halt)
    (_ : GuardedEndpoint.program (A true) (B true) true (negative true) pc ≠ .reject) :
    program A B negative (.upper saved pc) = MicrocodeEmbedding.instruction (endpointBinding true).ports
      (Label.upper saved) (GuardedEndpoint.program (A true) (B true) true (negative true) pc) := by
  rcases pc with pc | pc
  · exact (endpointBinding true).instruction_eq _ _
  · cases pc <;> simp_all [program, GuardedEndpoint.program, EndpointGuard.program, FinitePortBinding.instruction_eq]
    exact False.elim (hh rfl)

theorem erase_code (A B : Bool → ℕ) (negative : Bool → Bool) (saved : Bool) (j : Fin 5) (pc : NativeErase.Label)
    (hh : NativeErase.program pc ≠ .halt) (_ : NativeErase.program pc ≠ .reject) :
    program A B negative (.erase saved j pc) = MicrocodeEmbedding.instruction (eraseBinding j).ports
      (Label.erase saved j) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program, hp, FinitePortBinding.instruction_eq]

def cfg {A B : Bool → ℕ} (pc : Label A B) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label A B) :=
  ⟨⟨pc, fun p => (s.tapes p).denote⟩, pos⟩
def zipperCfg {A B : Bool → ℕ} (pc : Label A B) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label A B) :=
  ⟨⟨pc, s.tapes⟩, pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s.tapes p).denote, pos⟩

noncomputable def nativeEncoding (A B : Bool → ℕ) :=
  NativeMicrocode.initialEncoding (T := Port) (Label.lower (A := A) (B := B) (.inl (.grid (.init (.erase 0)))))
noncomputable def nativeMachine (A B : Bool → ℕ) (negative : Bool → Bool) :=
  NativeMicrocode.machine (nativeEncoding A B) (program A B negative)

def labelEquiv (A B : Bool → ℕ) : Label A B ≃
    GuardedEndpoint.Label (A false) (B false) ⊕ (Bool × Fin 5 × NativeErase.Label) ⊕
      (Bool × GuardedEndpoint.Label (A true) (B true)) ⊕ Bool where
  toFun
    | .lower pc => .inl pc
    | .erase saved j pc => .inr (.inl (saved,j,pc))
    | .upper saved pc => .inr (.inr (.inl (saved,pc)))
    | .done a => .inr (.inr (.inr a))
  invFun
    | .inl pc => .lower pc
    | .inr (.inl (saved,j,pc)) => .erase saved j pc
    | .inr (.inr (.inl (saved,pc))) => .upper saved pc
    | .inr (.inr (.inr a)) => .done a
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨saved,j,pc⟩ | ⟨saved,pc⟩ | a) <;> rfl

theorem label_card (A B : Bool → ℕ) :
    Fintype.card (Label A B) = 198*(A false+B false)+396*(A true+B true)+2851 := by
  have hg : Fintype.card EndpointGuard.Label=130 := by decide +kernel
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  have h := Fintype.card_congr (labelEquiv A B)
  simp only [GuardedEndpoint.Label, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, EndpointClip.label_card, hg, he] at h
  exact h.trans (by ring)

theorem fixed_resources (A B : Bool → ℕ) (negative : Bool → Bool) :
    (nativeMachine A B negative).k=17 ∧ (nativeMachine A B negative).g+1=5 ∧
    (nativeMachine A B negative).q+1=198*(A false+B false)+396*(A true+B true)+2851 ∧
    (nativeEncoding A B).label (.lower (.inl (.grid (.init (.erase 0)))))=0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=17
    decide +kernel
  · change Fintype.card (Label A B)-1+1=_
    rw [label_card]
    omega

end TransposeFollowup.SourceEndpoints


/-! Framed endpoint and erasure calls preserve both unused output banks
and every absolute head. Cleanup removes all five shared marked words. -/

namespace TransposeFollowup.SourceEndpoints

open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_endpoint (A B : Bool → ℕ) (upper : Bool)
    (labels : GuardedEndpoint.Label (A upper) (B upper) → Label A B)
    (pc : GuardedEndpoint.Label (A upper) (B upper)) (b : EndpointClip.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (endpointBinding upper).ports labels
      (GuardedEndpoint.cfg pc b (fun t => pos ((endpointBinding upper).ports t))) (frame s pos) =
      cfg (labels pc) (place upper b s) pos := by
  unfold MicrocodeEmbedding.embed GuardedEndpoint.cfg cfg frame
  simp only [← (endpointBinding upper).values_eq_extend]
  cases upper <;> congr 2 <;> funext p
  all_goals cases p with
  | shared p => cases p <;> rfl
  | other j => rfl

theorem embed_erase (A B : Bool → ℕ) (saved : Bool) (j : Fin 5) (pc : NativeErase.Label)
    (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding j).ports (Label.erase (A := A) (B := B) saved j)
      (NativeErase.cfg pc w (fun t => pos ((eraseBinding j).ports t))).denote (frame s pos) =
      cfg (.erase saved j pc) (s.set (erasePort j) w) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (eraseBinding j).values_eq_extend]
  congr 2 <;> funext p
  all_goals
    by_cases hp : p=erasePort j
    · subst p
      simp [eraseBinding, FinitePortBinding.values, Microcode.focus, Function.update] <;> rfl
    · simp [eraseBinding, FinitePortBinding.values, Function.update, hp]

abbrev Trace (A B : Bool → ℕ) (negative : Bool → Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program A B negative)) (NativeMicrocode.Active (program A B negative))

theorem jump_trace (A B : Bool → ℕ) (negative : Bool → Bool) (pc next : Label A B)
    (s : Bank) (pos : Port → ℤ) (h : program A B negative pc=.jump next) :
    Trace A B negative 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem endpoint_call (A B : Bool → ℕ) (negative : Bool → Bool) (upper : Bool)
    (labels : GuardedEndpoint.Label (A upper) (B upper) → Label A B)
    (hc : ∀ pc, GuardedEndpoint.program (A upper) (B upper) upper (negative upper) pc≠.halt →
      GuardedEndpoint.program (A upper) (B upper) upper (negative upper) pc≠.reject →
      program A B negative (labels pc)=MicrocodeEmbedding.instruction (endpointBinding upper).ports
        labels (GuardedEndpoint.program (A upper) (B upper) upper (negative upper) pc))
    (n i : List Bool) (hm : 0<n.length) (hi : i.length=n.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t ≤ GuardedEndpoint.budget (A upper) (B upper) n.length,
      Trace A B negative t (cfg (labels (.inl (.grid (.init (.erase 0))))) (place upper (EndpointClip.initial n i) s) pos)
        (cfg (labels (.inr (.done (EndpointGuard.answer (A upper) (B upper) upper (negative upper) n i))))
          (place upper (EndpointGuard.final (A upper) (B upper) upper (negative upper) n i) s) pos) := by
  obtain ⟨t, ht, htr⟩ := GuardedEndpoint.complete_trace (A upper) (B upper) upper (negative upper) n i hm hi
    (fun t => pos ((endpointBinding upper).ports t))
  have he := MicrocodeEmbedding.trace_embed (endpointBinding upper).ports labels
    (GuardedEndpoint.program (A upper) (B upper) upper (negative upper))
    (program A B negative) (frame s pos) hc htr
  exact ⟨t, ht, by simpa only [embed_endpoint] using he⟩

theorem erase_call (A B : Bool → ℕ) (negative : Bool → Bool) (saved : Bool) (j : Fin 5)
    (xs : List Bool) (s : Bank) (hs : s.tapes (erasePort j)=Counter.marked xs) (pos : Port → ℤ) :
    ∃ t ≤ 4*xs.length+4,
      Trace A B negative t (cfg (.erase saved j 2) s pos)
        (cfg (.erase saved j 0) (s.set (erasePort j) ⟨[], []⟩) pos) := by
  obtain ⟨t, ht, htr⟩ := NativeErase.erase_trace xs (fun t => pos ((eraseBinding j).ports t))
  have he := MicrocodeEmbedding.trace_embed (eraseBinding j).ports (Label.erase saved j) NativeErase.program
    (program A B negative) (frame s pos) (erase_code A B negative saved j) htr
  exact ⟨t, ht, by simpa only [embed_erase, ← hs, Bank.set_self] using he⟩

end TransposeFollowup.SourceEndpoints


/-! Both endpoint calls and all five erasures are actual subroutine traces.
The lower flag is carried unchanged across each erase and the upper call. -/

namespace TransposeFollowup.SourceEndpoints

open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem lower_call (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ) :
    ∃ t ≤ GuardedEndpoint.budget (A false) (B false) n.length,
      Trace A B negative t (cfg (.lower (.inl (.grid (.init (.erase 0))))) (initial n i) pos)
        (cfg (.lower (.inr (.done (EndpointGuard.answer (A false) (B false) false (negative false) n i))))
          (afterLower A B negative n i) pos) :=
  endpoint_call A B negative false Label.lower (lower_code A B negative) n i hm hi (initial n i) pos

theorem erase_stage (A B : Bool → ℕ) (negative : Bool → Bool) (saved : Bool)
    (n i : List Bool) (hm : 0<n.length) (hi : i.length=n.length) (j : Fin 5) (pos : Port → ℤ) :
    ∃ t ≤ 4*n.length+5,
      Trace A B negative t (cfg (.erase saved j 2) (eraseStage A B negative n i j.val) pos)
        (cfg (afterErase A B saved j) (eraseStage A B negative n i (j.val+1)) pos) := by
  obtain ⟨t, ht, htr⟩ := erase_call A B negative saved j (eraseWord A B negative n i j)
    (eraseStage A B negative n i j.val) (eraseStage_source A B negative n i j) pos
  rw [eraseStage_step] at htr
  have hj := jump_trace A B negative (.erase saved j 0) (afterErase A B saved j)
    (eraseStage A B negative n i (j.val+1)) pos rfl
  exact ⟨t+1, by rw [eraseWord_length A B negative n i hm hi j] at ht; omega, trace_trans htr hj⟩

theorem erase_all (A B : Bool → ℕ) (negative : Bool → Bool) (saved : Bool)
    (n i : List Bool) (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ) :
    ∃ t ≤ 20*n.length+25,
      Trace A B negative t (cfg (.erase saved 0 2) (afterLower A B negative n i) pos)
        (cfg (.upper saved (.inl (.grid (.init (.erase 0))))) (eraseStage A B negative n i 5) pos) := by
  obtain ⟨a, ha, h0⟩ := erase_stage A B negative saved n i hm hi 0 pos
  obtain ⟨b, hb, h1⟩ := erase_stage A B negative saved n i hm hi 1 pos
  obtain ⟨c, hc, h2⟩ := erase_stage A B negative saved n i hm hi 2 pos
  obtain ⟨d, hd, h3⟩ := erase_stage A B negative saved n i hm hi 3 pos
  obtain ⟨e, he, h4⟩ := erase_stage A B negative saved n i hm hi 4 pos
  have h := trace_trans h0 (trace_trans h1 (trace_trans h2 (trace_trans h3 h4)))
  exact ⟨a+(b+(c+(d+e))), by omega, by simpa [afterErase, eraseStage_zero] using h⟩

theorem upper_call (A B : Bool → ℕ) (negative : Bool → Bool) (saved : Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ) :
    ∃ t ≤ GuardedEndpoint.budget (A true) (B true) n.length,
      Trace A B negative t (cfg (.upper saved (.inl (.grid (.init (.erase 0))))) (eraseStage A B negative n i 5) pos)
        (cfg (.upper saved (.inr (.done (EndpointGuard.answer (A true) (B true) true (negative true) n i))))
          (final A B negative n i) pos) := by
  obtain ⟨t, ht, htr⟩ := endpoint_call A B negative true (Label.upper saved) (upper_code A B negative saved)
    n i hm hi (eraseStage A B negative n i 5) pos
  exact ⟨t, ht, by simpa only [upper_initial, final] using htr⟩

end TransposeFollowup.SourceEndpoints


/-! One complete native execution retains the lower endpoint, pays for
shared-work blanking, runs the upper endpoint, and conjoins the flags. -/

namespace TransposeFollowup.SourceEndpoints

open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def budget (A B : Bool → ℕ) (m : ℕ) :=
  GuardedEndpoint.budget (A false) (B false) m+20*m+27+GuardedEndpoint.budget (A true) (B true) m

theorem complete_trace (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ) :
    ∃ t ≤ budget A B n.length,
      Trace A B negative t (cfg (.lower (.inl (.grid (.init (.erase 0))))) (initial n i) pos)
        (cfg (.done (answer A B negative n i)) (final A B negative n i) pos) := by
  obtain ⟨a, ha, hleft⟩ := lower_call A B negative n i hm hi pos
  have hlink := jump_trace A B negative
    (.lower (.inr (.done (EndpointGuard.answer (A false) (B false) false (negative false) n i))))
    (.erase (EndpointGuard.answer (A false) (B false) false (negative false) n i) 0 2)
    (afterLower A B negative n i) pos rfl
  obtain ⟨b, hb, herase⟩ := erase_all A B negative
    (EndpointGuard.answer (A false) (B false) false (negative false) n i) n i hm hi pos
  obtain ⟨c, hc, hright⟩ := upper_call A B negative
    (EndpointGuard.answer (A false) (B false) false (negative false) n i) n i hm hi pos
  have hfinish := jump_trace A B negative
    (.upper (EndpointGuard.answer (A false) (B false) false (negative false) n i)
      (.inr (.done (EndpointGuard.answer (A true) (B true) true (negative true) n i))))
    (.done (answer A B negative n i)) (final A B negative n i) pos rfl
  exact ⟨a+(1+(b+(c+1))), by unfold budget; omega,
    trace_trans hleft (trace_trans hlink (trace_trans herase (trace_trans hright hfinish)))⟩

theorem native_complete (A B : Bool → ℕ) (negative : Bool → Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget A B n.length,
      Transpose.stepN (nativeMachine A B negative) input t
        ((cfg (.lower (.inl (.grid (.init (.erase 0))))) (initial n i) pos).denote
          (nativeEncoding A B) (program A B negative) inputPos outRev) =
        some ((cfg (.done (answer A B negative n i)) (final A B negative n i) pos).denote
          (nativeEncoding A B) (program A B negative) inputPos outRev) ∧
      Transpose.step (nativeMachine A B negative) input
        ((cfg (.done (answer A B negative n i)) (final A B negative n i) pos).denote
          (nativeEncoding A B) (program A B negative) inputPos outRev) = none := by
  obtain ⟨t, ht, htr⟩ := complete_trace A B negative n i hm hi pos
  refine ⟨t, ht, NativeMicrocode.trace_stepN (nativeEncoding A B) (program A B negative)
    input inputPos outRev htr, ?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding A B) (program A B negative) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (A B : Bool → ℕ) (negative : Bool → Bool)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label A B → J)
    (targetProgram : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program A B negative pc≠.halt → program A B negative pc≠.reject →
      targetProgram (labels pc)=MicrocodeEmbedding.instruction ports labels (program A B negative pc))
    (n i : List Bool) (hm : 0<n.length) (hi : i.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget A B n.length,
      Transpose.stepN (NativeMicrocode.machine encoding targetProgram) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.lower (.inl (.grid (.init (.erase 0))))) (initial n i) pos) frame).denote
            encoding targetProgram inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (answer A B negative n i)) (final A B negative n i) pos) frame).denote
            encoding targetProgram inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := complete_trace A B negative n i hm hi pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels (program A B negative)
    targetProgram frame input inputPos outRev hc htr⟩

end TransposeFollowup.SourceEndpoints


/-! Exact original endpoint fractions and the row's source-open flag,
produced together by the paid seventeen-tape caller. -/

namespace TransposeFollowup.SourceEndpoints

open FixedTapeCompiler
set_option autoImplicit false

def magnitude (F : RationalMobius) (upper : Bool) : ℕ := (EndpointClip.endpoint F upper).num.natAbs
def denominator (F : RationalMobius) (upper : Bool) : ℕ := (EndpointClip.endpoint F upper).den
def negative (F : RationalMobius) (upper : Bool) : Bool := decide ((EndpointClip.endpoint F upper).num<0)

def outputBank (s : Bank) (upper : Bool) : Fin 3 → CopyMachine.Tape Bool :=
  if upper then s.other else s.base.out

def outputWords (A B : Bool → ℕ) (neg : Bool → Bool) (n i : List Bool) (upper : Bool) (j : Fin 3) : List Bool :=
  EndpointClip.outputWord (A upper) (B upper) upper (neg upper)
    (EndpointClip.selection (A upper) (B upper) upper (neg upper) n i) n i j

theorem final_words (A B : Bool → ℕ) (neg : Bool → Bool) (n i : List Bool) (upper : Bool) (j : Fin 3) :
    outputBank (final A B neg n i) upper j=Counter.marked (outputWords A B neg n i upper j) := by
  cases upper <;> simp only [outputBank, Bool.false_eq_true, ite_false, ite_true, final_lower, final_upper]
  all_goals exact EndpointClip.final_out _ _ _ _ _ _ j

theorem outputWords_length (A B : Bool → ℕ) (neg : Bool → Bool) (n i : List Bool)
    (hm : 0<n.length) (hi : i.length=n.length) (upper : Bool) (j : Fin 3) :
    (outputWords A B neg n i upper j).length=n.length :=
  EndpointClip.outputWord_length _ _ _ _ _ _ _ hm hi j

theorem answer_rational (F : RationalMobius) (xs : List Bool) (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw=i.val) :
    answer (magnitude F) (denominator F) (negative F)
      (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw =
      (F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight :=
  EndpointGuard.both_answers F xs i iw hl hv

theorem rational_words (F : RationalMobius) (xs : List Bool) (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw=i.val) (upper : Bool) :
    let w := outputWords (magnitude F) (denominator F) (negative F)
      (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw upper
    let p := if upper then F.rightPair i else F.leftPair i
    (Counter.value (w 0), Counter.value (w 1), Counter.value (w 2))=
      (p.1.toNat, (-p.1).toNat, p.2.toNat) :=
  EndpointClip.rational_output F upper xs i iw hl hv

theorem rational_complete_trace (F : RationalMobius) (xs : List Bool)
    (i : Fin (Counter.value xs)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id xs).length)
    (hv : Counter.value iw=i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id xs
    ∃ t ≤ budget (magnitude F) (denominator F) n.length, ∃ w : Bool → Fin 3 → List Bool,
      Trace (magnitude F) (denominator F) (negative F) t
        (cfg (.lower (.inl (.grid (.init (.erase 0))))) (initial n iw) pos)
        (cfg (.done ((F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight))
          (final (magnitude F) (denominator F) (negative F) n iw) pos) ∧
      (∀ upper j, outputBank (final (magnitude F) (denominator F) (negative F) n iw) upper j=
        Counter.marked (w upper j)) ∧
      (∀ upper, let p := if upper then F.rightPair i else F.leftPair i
        (Counter.value (w upper 0), Counter.value (w upper 1), Counter.value (w upper 2))=
          (p.1.toNat, (-p.1).toNat, p.2.toNat)) ∧ ∀ upper j, (w upper j).length=n.length := by
  have hm : 0<(PaddedWord.word (PaddedWord.commonConstant F) id xs).length := by
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t, ht, htr⟩ := complete_trace (magnitude F) (denominator F) (negative F)
    (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw hm hl pos
  refine ⟨t, ht, outputWords (magnitude F) (denominator F) (negative F)
    (PaddedWord.word (PaddedWord.commonConstant F) id xs) iw, ?_, ?_, ?_, ?_⟩
  · simpa only [answer_rational F xs i iw hl hv] using htr
  · intro upper j
    exact final_words _ _ _ _ _ upper j
  · intro upper
    exact rational_words F xs i iw hl hv upper
  · intro upper j
    exact outputWords_length _ _ _ _ _ hm hl upper j

theorem total_budget (F : RationalMobius) (N : ℕ) (xs : List Bool)
    (hN : 1≤N) (hl : xs.length≤(N+1).size) :
    let S := magnitude F false+denominator F false+magnitude F true+denominator F true
    N*(N*budget (magnitude F) (denominator F) (PaddedWord.word (PaddedWord.commonConstant F) id xs).length) ≤
      ((416+72*S)*(F.integerOperandConstant^2).size+5206+928*S)*Transpose.inputLength N := by
  let S := magnitude F false+denominator F false+magnitude F true+denominator F true
  have he : budget (magnitude F) (denominator F) (PaddedWord.word (PaddedWord.commonConstant F) id xs).length =
      ((208+36*S)*PaddedWord.commonConstant F+523+104*S)+(416+72*S)*xs.length := by
    rw [PaddedWord.word_length]
    unfold budget GuardedEndpoint.budget EndpointClip.budget EndpointGuard.budget S
    ring
  have h := dense_scan_budget ((208+36*S)*PaddedWord.commonConstant F+523+104*S) (416+72*S) N hN
  rw [he]
  calc
    _ ≤ N*(N*(((208+36*S)*PaddedWord.commonConstant F+523+104*S)+(416+72*S)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.SourceEndpoints
