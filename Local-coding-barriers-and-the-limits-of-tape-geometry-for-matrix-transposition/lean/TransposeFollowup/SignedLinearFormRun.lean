import TransposeFollowup.SignedComponents
import TransposeFollowup.SeedMultipleMeaning

/-! Component algebra for the next native image routine. Three fixed
products, sign-directed placement and one addition suffice. This file
proves the reference components and full mass, not a native execution. -/

namespace TransposeFollowup.SignedLinearForm
open SignedComponents
set_option autoImplicit false

def components (u v : ℤ) (p n d : ℕ) : Pair :=
  ⟨u.natAbs*(if u<0 then n else p)+(if v<0 then 0 else v.natAbs*d),
    u.natAbs*(if u<0 then p else n)+(if v<0 then v.natAbs*d else 0)⟩

theorem coefficient_pair (u : ℤ) :
    Pair.ofInt u = if u<0 then ⟨0,u.natAbs⟩ else ⟨u.natAbs,0⟩ := by
  have hm : u.toNat+(-u).toNat=u.natAbs := ofInt_mass u
  by_cases h : u<0
  · have hp : u.toNat=0 := by omega
    have hn : (-u).toNat=u.natAbs := by omega
    simp [Pair.ofInt,h,hp,hn]
  · have hn : (-u).toNat=0 := by omega
    have hp : u.toNat=u.natAbs := by omega
    simp [Pair.ofInt,h,hp,hn]

theorem components_spec (u v : ℤ) (p n d : ℕ) :
    components u v p n d=((Pair.ofInt u).mul ⟨p,n⟩).add ((Pair.ofInt v).mul ⟨d,0⟩) := by
  rw [coefficient_pair,coefficient_pair]
  by_cases hu : u<0 <;> by_cases hv : v<0 <;>
    simp [components,hu,hv,Pair.mul,Pair.add]

theorem components_mass (u v : ℤ) (p n d : ℕ) :
    (components u v p n d).mass=u.natAbs*(p+n)+v.natAbs*d := by
  rw [components_spec,add_mass,mul_mass,mul_mass,ofInt_mass,ofInt_mass]
  simp [Pair.mass]

theorem terms_le_mass (u v : ℤ) (p n d : ℕ) :
    u.natAbs*p≤(components u v p n d).mass ∧
    u.natAbs*n≤(components u v p n d).mass ∧
    v.natAbs*d≤(components u v p n d).mass := by
  rw [components_mass]
  have hp := Nat.mul_le_mul_left u.natAbs (show p≤p+n by omega)
  have hn := Nat.mul_le_mul_left u.natAbs (show n≤p+n by omega)
  omega

end TransposeFollowup.SignedLinearForm


/-! Reference words for the next paid signed linear-form controller.
The full component mass bounds all products and the selected addition.
These are word semantics, not a native execution or initialization theorem. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler SignedComponents
set_option autoImplicit false

def multiplier (u v : ℤ) (j : Fin 3) : ℕ := if j=2 then v.natAbs else u.natAbs

def workWord (u v : ℤ) (xs : Fin 3 → List Bool) (j : Fin 3) : List Bool :=
  RepeatedAdd.repeatWord (xs j) (multiplier u v j) (ArithmeticSeed.zeros (xs 0).length)

def outputIndex (u : ℤ) (negative : Bool) : Fin 3 :=
  if negative=decide (u<0) then 0 else 1

def outputWord (u v : ℤ) (xs : Fin 3 → List Bool) (negative : Bool) : List Bool :=
  if negative=decide (v<0) then RepeatedAdd.addWord (workWord u v xs (outputIndex u negative)) (workWord u v xs 2)
  else workWord u v xs (outputIndex u negative)

theorem workWord_length (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j, (xs j).length=(xs 0).length) (j : Fin 3) :
    (workWord u v xs j).length=(xs 0).length := by
  exact (RepeatedAdd.repeatWord_length _ _ _ (by simp [ArithmeticSeed.zeros,h])).trans (h j)

theorem workWord_value_mod (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j, (xs j).length=(xs 0).length) (j : Fin 3) :
    Counter.value (workWord u v xs j)=multiplier u v j * Counter.value (xs j)%2^(xs 0).length := by
  have hv := RepeatedAdd.repeatWord_value (xs j) (multiplier u v j)
    (ArithmeticSeed.zeros (xs 0).length) (by simp [ArithmeticSeed.zeros,h])
  simpa [← NativeCounter.word_value, ArithmeticSeed.zeros,PaddedWord.value_zeroes,h,workWord] using hv

theorem workWord_value_exact (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j, (xs j).length=(xs 0).length)
    (hf : (components u v (Counter.value (xs 0)) (Counter.value (xs 1)) (Counter.value (xs 2))).mass<2^(xs 0).length)
    (j : Fin 3) : Counter.value (workWord u v xs j)=multiplier u v j*Counter.value (xs j) := by
  rw [workWord_value_mod u v xs h j]
  apply Nat.mod_eq_of_lt
  have ht := terms_le_mass u v (Counter.value (xs 0)) (Counter.value (xs 1)) (Counter.value (xs 2))
  fin_cases j <;> simp only [multiplier] <;> norm_num <;> omega

theorem outputWord_length (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j, (xs j).length=(xs 0).length) (negative : Bool) :
    (outputWord u v xs negative).length=(xs 0).length := by
  have hw := workWord_length u v xs h
  unfold outputWord
  split_ifs
  · exact (RepeatedAdd.addWord_length _ _ ((hw _).trans (hw _).symm)).trans (hw _)
  · exact hw _

theorem outputWord_value (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j, (xs j).length=(xs 0).length)
    (hf : (components u v (Counter.value (xs 0)) (Counter.value (xs 1)) (Counter.value (xs 2))).mass<2^(xs 0).length)
    (negative : Bool) : Counter.value (outputWord u v xs negative)=
      if negative then (components u v (Counter.value (xs 0)) (Counter.value (xs 1)) (Counter.value (xs 2))).negative
      else (components u v (Counter.value (xs 0)) (Counter.value (xs 1)) (Counter.value (xs 2))).positive := by
  have hw := workWord_value_exact u v xs h hf
  have hl := workWord_length u v xs h
  have ha : Counter.value (RepeatedAdd.addWord (workWord u v xs (outputIndex u negative)) (workWord u v xs 2))=
      (multiplier u v (outputIndex u negative)*Counter.value (xs (outputIndex u negative))+
        multiplier u v 2*Counter.value (xs 2))%2^(xs 0).length := by
    rw [NativeCounter.word_value,RepeatedAdd.addWord_value _ _ ((hl _).trans (hl _).symm),
      ← NativeCounter.word_value,← NativeCounter.word_value,hw,hw,hl]
  by_cases hu : u<0 <;> by_cases hv : v<0 <;> cases negative <;>
    simp [outputWord,outputIndex,hu,hv,hw,multiplier,components] at *
  all_goals rw [ha,Nat.mod_eq_of_lt (by dsimp [Pair.mass] at hf; omega)]

end TransposeFollowup.SignedLinearForm


/-! Concrete banks for three paid fixed products, two output copies and
one addition. Five work/output tapes start blank; input words and the
zero, fuel and scratch resources are explicit preconditions. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

inductive Port | arg (j : Fin 3) | zero | fuel | scratch | work (j : Fin 3) | out (negative : Bool)
  deriving DecidableEq, Fintype

@[ext] structure Bank where
  arg : Fin 3 → Tape Bool
  zero : Tape Bool
  fuel : Tape Bool
  scratch : Tape Bool
  work : Fin 3 → Tape Bool
  out : Bool → Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .arg j => s.arg j | .zero => s.zero | .fuel => s.fuel | .scratch => s.scratch
  | .work j => s.work j | .out b => s.out b

def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank :=
  match p with
  | .arg j => {s with arg := Function.update s.arg j w}
  | .zero => {s with zero := w} | .fuel => {s with fuel := w} | .scratch => {s with scratch := w}
  | .work j => {s with work := Function.update s.work j w}
  | .out b => {s with out := Function.update s.out b w}

@[simp] theorem Bank.set_tapes (s : Bank) (p q : Port) (w : Tape Bool) :
    (s.set p w).tapes q = Function.update s.tapes p w q := by
  cases p <;> cases q <;> simp [Bank.set, Bank.tapes, Function.update]

@[simp] theorem Bank.set_self (s : Bank) (p : Port) : s.set p (s.tapes p) = s := by
  cases p <;> simp [Bank.set, Bank.tapes]

def initial (xs : Fin 3 → List Bool) : Bank where
  arg := fun j => Counter.marked (xs j)
  zero := Counter.marked (ArithmeticSeed.zeros (xs 0).length)
  fuel := Counter.marked [true]
  scratch := BinaryCarry.preparedOutput
  work := fun _ => ⟨[], []⟩
  out := fun _ => ⟨[], []⟩

def zeroed (xs : Fin 3 → List Bool) (k : ℕ) : Bank :=
  {initial xs with work := fun j => if j.val<k then Counter.marked (ArithmeticSeed.zeros (xs 0).length) else ⟨[], []⟩}

def multiplied (u v : ℤ) (xs : Fin 3 → List Bool) (k : ℕ) : Bank :=
  {initial xs with work := fun j => if j.val<k then Counter.marked (workWord u v xs j) else Counter.marked (ArithmeticSeed.zeros (xs 0).length)}

def copied (u v : ℤ) (xs : Fin 3 → List Bool) (k : ℕ) : Bank :=
  {multiplied u v xs 3 with out := fun b => if (if b then 1 else 0)<k then Counter.marked (workWord u v xs (outputIndex u b)) else ⟨[], []⟩}

def final (u v : ℤ) (xs : Fin 3 → List Bool) : Bank :=
  {multiplied u v xs 3 with out := fun b => Counter.marked (outputWord u v xs b)}

theorem zeroed_zero (xs : Fin 3 → List Bool) : zeroed xs 0=initial xs := by
  simp [zeroed,initial]

theorem zeroed_step (xs : Fin 3 → List Bool) (j : Fin 3) :
    (zeroed xs j.val).set (.work j) (Counter.marked (ArithmeticSeed.zeros (xs 0).length))=
      zeroed xs (j.val+1) := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases j <;> fin_cases k <;> rfl

theorem zeroed_three (u v : ℤ) (xs : Fin 3 → List Bool) : zeroed xs 3=multiplied u v xs 0 := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases k <;> rfl

theorem copied_zero (u v : ℤ) (xs : Fin 3 → List Bool) : copied u v xs 0=multiplied u v xs 3 := by
  simp [copied,multiplied,initial]

theorem copied_step (u v : ℤ) (xs : Fin 3 → List Bool) (b : Bool) :
    (copied u v xs (if b then 1 else 0)).set (.out b)
      (Counter.marked (workWord u v xs (outputIndex u b)))=
      copied u v xs (if b then 2 else 1) := by
  apply Bank.ext <;> try rfl
  funext c
  cases b <;> cases c <;> rfl

theorem copied_source (u v : ℤ) (xs : Fin 3 → List Bool) (k : ℕ) (j : Fin 3) :
    (copied u v xs k).tapes (.work j)=Counter.marked (workWord u v xs j) := by
  simp [copied,multiplied,Bank.tapes]

end TransposeFollowup.SignedLinearForm


/-! Coefficients and signs are fixed machine parameters. No growing
integer is stored in control. Every primitive return pays a transfer. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler
set_option autoImplicit false

def pairBinding (a b : Port) (hab : a≠b) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![a,b], by intro j k h; fin_cases j <;> fin_cases k <;> simp_all⟩
  decode := fun p => if p=a then some 0 else if p=b then some 1 else none
  decode_spec := by
    intro p j
    change (if p=a then some 0 else if p=b then some 1 else none)=some j ↔ ![a,b] j=p
    fin_cases j <;> by_cases ha : p=a <;> by_cases hb : p=b <;> simp_all [eq_comm]

def zeroBinding (j : Fin 3) := pairBinding .zero (.work j) (by simp)
def outputBinding (u : ℤ) (b : Bool) := pairBinding (.work (outputIndex u b)) (.out b) (by simp)

def multiplyPort (j : Fin 3) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .work j | .factor => .arg j | .scratch => .scratch | .zero => .zero
def multiplyBinding (j : Fin 3) : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨multiplyPort j, by intro p q h; cases p <;> cases q <;> simp_all [multiplyPort]⟩
  decode := fun p => match p with
    | .fuel => some .fuel | .work k => if k=j then some .acc else none
    | .arg k => if k=j then some .factor else none
    | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec := by
    intro p t
    change (match p with
      | .fuel => some RepeatedAdd.Port.fuel | .work k => if k=j then some .acc else none
      | .arg k => if k=j then some .factor else none
      | .scratch => some .scratch | .zero => some .zero | _ => none)=some t ↔ multiplyPort j t=p
    cases p <;> cases t <;> simp [multiplyPort,eq_comm]

def addPort (v : ℤ) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .out (decide (v<0)) | .factor => .work 2
  | .scratch => .scratch | .zero => .zero
def addBinding (v : ℤ) : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort v, by intro p q h; cases p <;> cases q <;> simp_all [addPort]⟩
  decode := fun p => match p with
    | .fuel => some .fuel | .out b => if b=decide (v<0) then some .acc else none
    | .work j => if j=2 then some .factor else none
    | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec := by
    intro p t
    change (match p with
      | .fuel => some RepeatedAdd.Port.fuel | .out b => if b=decide (v<0) then some .acc else none
      | .work j => if j=2 then some .factor else none
      | .scratch => some .scratch | .zero => some .zero | _ => none)=some t ↔ addPort v t=p
    cases p <;> cases t <;> simp [addPort,eq_comm]

inductive Label (u v : ℤ)
  | init (j : Fin 3) (pc : NativeMappedCopy.Label)
  | multiply (j : Fin 3) (pc : FixedMultiple.Label (multiplier u v j))
  | copy (negative : Bool) (pc : NativeMappedCopy.Label)
  | add (pc : RepeatedAdd.Label)
  | done
  deriving DecidableEq, Fintype

def afterInit (u v : ℤ) (j : Fin 3) : Label u v :=
  if h : j.val<2 then .init ⟨j.val+1,by omega⟩ (.init (.erase 0))
  else .multiply 0 (FixedMultiple.start _)
def afterMultiply (u v : ℤ) (j : Fin 3) : Label u v :=
  if h : j.val<2 then .multiply ⟨j.val+1,by omega⟩ (FixedMultiple.start _)
  else .copy false (.init (.erase 0))
def afterCopy (u v : ℤ) (negative : Bool) : Label u v :=
  if negative then .add (.counter 0) else .copy true (.init (.erase 0))

def program (u v : ℤ) : Microcode.Program Port (Label u v)
  | .init j (.seal .done) => .jump (afterInit u v j)
  | .init j pc => (zeroBinding j).instruction (Label.init j) (NativeMappedCopy.program id pc)
  | .multiply j .done => .jump (afterMultiply u v j)
  | .multiply j pc => (multiplyBinding j).instruction (Label.multiply j) (FixedMultiple.program _ pc)
  | .copy b (.seal .done) => .jump (afterCopy u v b)
  | .copy b pc => (outputBinding u b).instruction (Label.copy b) (NativeMappedCopy.program id pc)
  | .add (.counter pc) => if pc=12 then .jump .done
      else (addBinding v).instruction Label.add (RepeatedAdd.program (.counter pc))
  | .add pc => (addBinding v).instruction Label.add (RepeatedAdd.program pc)
  | .done => .halt

theorem init_code (u v : ℤ) (j : Fin 3) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    program u v (.init j pc)=MicrocodeEmbedding.instruction (zeroBinding j).ports
      (Label.init j) (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem multiply_code (u v : ℤ) (j : Fin 3) (pc : FixedMultiple.Label (multiplier u v j))
    (hh : FixedMultiple.program _ pc≠.halt) (_ : FixedMultiple.program _ pc≠.reject) :
    program u v (.multiply j pc)=MicrocodeEmbedding.instruction (multiplyBinding j).ports
      (Label.multiply j) (FixedMultiple.program _ pc) := by
  have hp : pc≠.done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem copy_code (u v : ℤ) (b : Bool) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    program u v (.copy b pc)=MicrocodeEmbedding.instruction (outputBinding u b).ports
      (Label.copy b) (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem add_code (u v : ℤ) (pc : RepeatedAdd.Label)
    (hh : RepeatedAdd.program pc≠.halt) (_ : RepeatedAdd.program pc≠.reject) :
    program u v (.add pc)=MicrocodeEmbedding.instruction (addBinding v).ports
      Label.add (RepeatedAdd.program pc) := by
  have hp : pc≠.counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

def cfg {u v : ℤ} (pc : Label u v) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label u v) :=
  ⟨⟨pc,fun p => (s.tapes p).denote⟩,pos⟩
def zipperCfg {u v : ℤ} (pc : Label u v) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label u v) :=
  ⟨⟨pc,s.tapes⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s.tapes p).denote,pos⟩

noncomputable def nativeEncoding (u v : ℤ) :=
  NativeMicrocode.initialEncoding (T := Port) (Label.init (u := u) (v := v) 0 (.init (.erase 0)))
noncomputable def nativeMachine (u v : ℤ) := NativeMicrocode.machine (nativeEncoding u v) (program u v)

def labelEquiv (u v : ℤ) : Label u v ≃ (Fin 3 × NativeMappedCopy.Label) ⊕
    (Σ j : Fin 3, FixedMultiple.Label (multiplier u v j)) ⊕
    (Bool × NativeMappedCopy.Label) ⊕ RepeatedAdd.Label ⊕ Unit where
  toFun
    | .init j pc => .inl (j,pc)
    | .multiply j pc => .inr (.inl ⟨j,pc⟩)
    | .copy b pc => .inr (.inr (.inl (b,pc)))
    | .add pc => .inr (.inr (.inr (.inl pc)))
    | .done => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl (j,pc) => .init j pc
    | .inr (.inl ⟨j,pc⟩) => .multiply j pc
    | .inr (.inr (.inl (b,pc))) => .copy b pc
    | .inr (.inr (.inr (.inl pc))) => .add pc
    | .inr (.inr (.inr (.inr ()))) => .done
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (⟨j,pc⟩ | ⟨j,pc⟩ | ⟨b,pc⟩ | pc | ⟨⟩) <;> rfl

theorem label_card (u v : ℤ) : Fintype.card (Label u v)=99*(2*u.natAbs+v.natAbs)+520 := by
  have h := Fintype.card_congr (labelEquiv u v)
  have hc : Fintype.card NativeMappedCopy.Label=24 := by decide +kernel
  have ha : Fintype.card RepeatedAdd.Label=99 := by decide +kernel
  have hm : (∑ j : Fin 3, (99*(multiplier u v j+1)+1))=99*(2*u.natAbs+v.natAbs)+300 := by
    norm_num [Fin.sum_univ_succ,multiplier]
    omega
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_sigma,Fintype.card_fin,
    Fintype.card_bool,Fintype.card_unit,hc,ha,FixedMultiple.label_card] at h
  rw [hm] at h
  exact h.trans (by ring)

theorem fixed_resources (u v : ℤ) : (nativeMachine u v).k=11 ∧
    (nativeMachine u v).g+1=5 ∧ (nativeMachine u v).q+1=99*(2*u.natAbs+v.natAbs)+520 ∧
    (nativeEncoding u v).label (.init 0 (.init (.erase 0)))=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=11
    decide +kernel
  · change Fintype.card (Label u v)-1+1=_
    rw [label_card]
    omega

end TransposeFollowup.SignedLinearForm


/-! Framed calls to the existing copy, fixed-multiple and addition
programs. All input words, template resources and head positions are explicit. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_copy (u v : ℤ) (p q : Port) (hpq : p≠q)
    (labels : NativeMappedCopy.Label → Label u v) (pc : NativeMappedCopy.Label)
    (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (pairBinding p q hpq).ports labels
      (NativeMappedCopy.cfg pc a b (fun t => pos ((pairBinding p q hpq).ports t))) (frame s pos)=
      cfg (labels pc) ((s.set p a).set q b) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← (pairBinding p q hpq).values_eq_extend]
  congr 2 <;> funext t
  all_goals
    by_cases ht : t=p
    · subst t
      simp [pairBinding,FinitePortBinding.values,NativeMappedCopy.bank,Function.update,hpq] <;> rfl
    · by_cases hq : t=q
      · subst t
        simp [pairBinding,FinitePortBinding.values,NativeMappedCopy.bank,Function.update,Ne.symm hpq] <;> rfl
      · simp [pairBinding,FinitePortBinding.values,Function.update,ht,hq]

theorem embed_multiply (u v : ℤ) (j : Fin 3) (pc : FixedMultiple.Label (multiplier u v j))
    (b : RepeatedAdd.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (multiplyBinding j).ports (Label.multiply j)
      (FixedMultiple.cfg pc b (fun t => pos ((multiplyBinding j).ports t))) (frame s pos)=
      cfg (.multiply j pc)
        {s with fuel := b.fuel, scratch := b.scratch, zero := b.zero, work := Function.update s.work j b.acc, arg := Function.update s.arg j b.factor} pos := by
  unfold MicrocodeEmbedding.embed FixedMultiple.cfg cfg frame
  simp only [← (multiplyBinding j).values_eq_extend]
  fin_cases j <;> congr 2 <;> funext p <;> cases p <;> try rfl
  all_goals rename_i k; fin_cases k <;> rfl

theorem embed_add (u v : ℤ) (pc : RepeatedAdd.Label) (b : RepeatedAdd.Bank)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (addBinding v).ports (Label.add (u := u) (v := v))
      (RepeatedAdd.cfg pc b (fun t => pos ((addBinding v).ports t))) (frame s pos)=
      cfg (.add pc)
        {s with fuel := b.fuel, scratch := b.scratch, zero := b.zero, out := Function.update s.out (decide (v<0)) b.acc, work := Function.update s.work 2 b.factor} pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← (addBinding v).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try rfl
  all_goals
    rename_i j
    fin_cases j <;> by_cases hv : v<0 <;>
      simp [addBinding,FinitePortBinding.values,hv] <;>
        first | rfl | (change pos (.out (decide (v<0))) = _; simp [hv])

abbrev Trace (u v : ℤ) :=
  OperationalTrace.Trace (NativeMicrocode.step (program u v)) (NativeMicrocode.Active (program u v))

theorem jump_trace (u v : ℤ) (pc next : Label u v) (s : Bank) (pos : Port → ℤ)
    (h : program u v pc=.jump next) : Trace u v 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem mapped_call (u v : ℤ) (p q : Port) (hpq : p≠q)
    (labels : NativeMappedCopy.Label → Label u v)
    (hc : ∀ pc, NativeMappedCopy.program id pc≠.halt → NativeMappedCopy.program id pc≠.reject →
      program u v (labels pc)=MicrocodeEmbedding.instruction (pairBinding p q hpq).ports
        labels (NativeMappedCopy.program id pc))
    (xs : List Bool) (s : Bank) (hs : s.tapes p=Counter.marked xs)
    (hq : s.tapes q=⟨[], []⟩) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+14, Trace u v t (cfg (labels (.init (.erase 0))) s pos)
      (cfg (labels (.seal .done)) (s.set q (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun t => pos ((pairBinding p q hpq).ports t))
  have he := MicrocodeEmbedding.trace_embed (pairBinding p q hpq).ports labels
    (NativeMappedCopy.program id) (program u v) (frame s pos) hc htr
  exact ⟨t,ht,by simpa only [embed_copy,List.map_id,← hs,Bank.set_self,← hq] using he⟩

theorem multiply_call (u v : ℤ) (j : Fin 3) (a x : List Bool)
    (h : a.length=x.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t≤FixedMultiple.budget (multiplier u v j) x.length,
      Trace u v t
        (cfg (.multiply j (FixedMultiple.start _))
          {s with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate x.length false), work := Function.update s.work j (Counter.marked a), arg := Function.update s.arg j (Counter.marked x)} pos)
        (cfg (.multiply j .done)
          {s with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate x.length false), work := Function.update s.work j (Counter.marked (RepeatedAdd.repeatWord x (multiplier u v j) a)), arg := Function.update s.arg j (Counter.marked x)} pos) := by
  obtain ⟨t,ht,htr⟩ := FixedMultiple.multiple_trace (multiplier u v j) a x h
    (fun t => pos ((multiplyBinding j).ports t))
  have he := MicrocodeEmbedding.trace_embed (multiplyBinding j).ports (Label.multiply j)
    (FixedMultiple.program _) (program u v) (frame s pos) (multiply_code u v j) htr
  exact ⟨t,ht,by simpa only [embed_multiply,RepeatedAdd.ready,Counter.marked,
    BinaryCarry.marked,BinaryCompare.marked] using he⟩

theorem add_call (u v : ℤ) (a x : List Bool) (h : a.length=x.length)
    (s : Bank) (pos : Port → ℤ) :
    ∃ t≤18*x.length+51, Trace u v t
      (cfg (.add (.counter 0))
        {s with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate x.length false), out := Function.update s.out (decide (v<0)) (Counter.marked a), work := Function.update s.work 2 (Counter.marked x)} pos)
      (cfg (.add (.counter 12))
        {s with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate x.length false), out := Function.update s.out (decide (v<0)) (Counter.marked (RepeatedAdd.addWord a x)), work := Function.update s.work 2 (Counter.marked x)} pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.single_add_trace a x h (fun t => pos ((addBinding v).ports t))
  have he := MicrocodeEmbedding.trace_embed (addBinding v).ports (Label.add (u := u) (v := v))
    RepeatedAdd.program (program u v) (frame s pos) (add_code u v) htr
  exact ⟨t,ht,by simpa only [embed_add,RepeatedAdd.ready,Counter.marked,
    BinaryCarry.marked,BinaryCompare.marked] using he⟩

end TransposeFollowup.SignedLinearForm


/-! Each stage connects its actual output bank to the next call. Zero
words and output copies are charged; scratch reuse is provided by the adder. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem init_stage (u v : ℤ) (xs : Fin 3 → List Bool) (j : Fin 3) (pos : Port → ℤ) :
    ∃ t≤6*(xs 0).length+15, Trace u v t
      (cfg (.init j (.init (.erase 0))) (zeroed xs j.val) pos)
      (cfg (afterInit u v j) (zeroed xs (j.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := mapped_call u v .zero (.work j) (by simp) (Label.init j)
    (init_code u v j) (ArithmeticSeed.zeros (xs 0).length) (zeroed xs j.val)
    rfl (by simp [zeroed,Bank.tapes]) pos
  rw [zeroed_step] at htr
  have hj := jump_trace u v (.init j (.seal .done)) (afterInit u v j)
    (zeroed xs (j.val+1)) pos rfl
  exact ⟨t+1,by simpa [ArithmeticSeed.zeros] using Nat.add_le_add_right ht 1,trace_trans htr hj⟩

theorem init_all (u v : ℤ) (xs : Fin 3 → List Bool) (pos : Port → ℤ) :
    ∃ t≤18*(xs 0).length+45, Trace u v t
      (cfg (.init 0 (.init (.erase 0))) (initial xs) pos)
      (cfg (.multiply 0 (FixedMultiple.start _)) (multiplied u v xs 0) pos) := by
  obtain ⟨a,ha,h0⟩ := init_stage u v xs 0 pos
  obtain ⟨b,hb,h1⟩ := init_stage u v xs 1 pos
  obtain ⟨c,hc,h2⟩ := init_stage u v xs 2 pos
  have h := trace_trans h0 (trace_trans h1 h2)
  exact ⟨a+(b+c),by omega,by simpa [afterInit,zeroed_zero,zeroed_three u v xs] using h⟩

theorem multiply_stage (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (j : Fin 3) (pos : Port → ℤ) :
    ∃ t≤FixedMultiple.budget (multiplier u v j) (xs 0).length+1, Trace u v t
      (cfg (.multiply j (FixedMultiple.start _)) (multiplied u v xs j.val) pos)
      (cfg (afterMultiply u v j) (multiplied u v xs (j.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := multiply_call u v j (ArithmeticSeed.zeros (xs 0).length) (xs j)
    (by simp [ArithmeticSeed.zeros,h]) (multiplied u v xs j.val) pos
  rw [h j] at ht htr
  have hstart :
      {multiplied u v xs j.val with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate (xs 0).length false), work := Function.update (multiplied u v xs j.val).work j (Counter.marked (ArithmeticSeed.zeros (xs 0).length)), arg := Function.update (multiplied u v xs j.val).arg j (Counter.marked (xs j))}=multiplied u v xs j.val := by
    fin_cases j <;> apply Bank.ext <;> try rfl
    all_goals funext k; fin_cases k <;> rfl
  have hend :
      {multiplied u v xs j.val with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate (xs 0).length false), work := Function.update (multiplied u v xs j.val).work j (Counter.marked (workWord u v xs j)), arg := Function.update (multiplied u v xs j.val).arg j (Counter.marked (xs j))}=multiplied u v xs (j.val+1) := by
    fin_cases j <;> apply Bank.ext <;> try rfl
    all_goals funext k; fin_cases k <;> rfl
  change Trace u v t (cfg _ _ pos) (cfg _ _ pos) at htr
  rw [hstart,show RepeatedAdd.repeatWord (xs j) (multiplier u v j) (ArithmeticSeed.zeros (xs 0).length)=workWord u v xs j by rfl,hend] at htr
  have hj := jump_trace u v (.multiply j .done) (afterMultiply u v j)
    (multiplied u v xs (j.val+1)) pos rfl
  exact ⟨t+1,Nat.add_le_add_right ht 1,trace_trans htr hj⟩

theorem multiply_all (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (pos : Port → ℤ) :
    ∃ t≤(2*u.natAbs+v.natAbs)*(18*(xs 0).length+52)+6, Trace u v t
      (cfg (.multiply 0 (FixedMultiple.start _)) (multiplied u v xs 0) pos)
      (cfg (.copy false (.init (.erase 0))) (copied u v xs 0) pos) := by
  obtain ⟨a,ha,h0⟩ := multiply_stage u v xs h 0 pos
  obtain ⟨b,hb,h1⟩ := multiply_stage u v xs h 1 pos
  obtain ⟨c,hc,h2⟩ := multiply_stage u v xs h 2 pos
  have ht := trace_trans h0 (trace_trans h1 h2)
  refine ⟨a+(b+c),?_,?_⟩
  · simp [FixedMultiple.budget,multiplier] at ha hb hc
    nlinarith
  · simpa [afterMultiply,copied_zero] using ht

theorem copy_stage (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (b : Bool) (pos : Port → ℤ) :
    ∃ t≤6*(xs 0).length+15, Trace u v t
      (cfg (.copy b (.init (.erase 0))) (copied u v xs (if b then 1 else 0)) pos)
      (cfg (afterCopy u v b) (copied u v xs (if b then 2 else 1)) pos) := by
  obtain ⟨t,ht,htr⟩ := mapped_call u v (.work (outputIndex u b)) (.out b) (by simp)
    (Label.copy b) (copy_code u v b) (workWord u v xs (outputIndex u b))
    (copied u v xs (if b then 1 else 0)) (copied_source _ _ _ _ _)
    (by cases b <;> rfl) pos
  rw [copied_step] at htr
  have hj := jump_trace u v (.copy b (.seal .done)) (afterCopy u v b)
    (copied u v xs (if b then 2 else 1)) pos rfl
  exact ⟨t+1,by rw [workWord_length u v xs h] at ht; omega,trace_trans htr hj⟩

theorem copy_all (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (pos : Port → ℤ) :
    ∃ t≤12*(xs 0).length+30, Trace u v t
      (cfg (.copy false (.init (.erase 0))) (copied u v xs 0) pos)
      (cfg (.add (.counter 0)) (copied u v xs 2) pos) := by
  obtain ⟨a,ha,h0⟩ := copy_stage u v xs h false pos
  obtain ⟨b,hb,h1⟩ := copy_stage u v xs h true pos
  exact ⟨a+b,by omega,trace_trans h0 h1⟩

theorem add_stage (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (pos : Port → ℤ) :
    ∃ t≤18*(xs 0).length+52, Trace u v t
      (cfg (.add (.counter 0)) (copied u v xs 2) pos)
      (cfg .done (final u v xs) pos) := by
  have hl := workWord_length u v xs h
  obtain ⟨t,ht,htr⟩ := add_call u v (workWord u v xs (outputIndex u (decide (v<0))))
    (workWord u v xs 2) ((hl _).trans (hl _).symm) (copied u v xs 2) pos
  rw [hl] at ht htr
  have hstart :
      {copied u v xs 2 with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate (xs 0).length false), out := Function.update (copied u v xs 2).out (decide (v<0)) (Counter.marked (workWord u v xs (outputIndex u (decide (v<0))))), work := Function.update (copied u v xs 2).work 2 (Counter.marked (workWord u v xs 2))}=copied u v xs 2 := by
    apply Bank.ext <;> try rfl
    · funext j; fin_cases j <;> rfl
    · funext b; cases b <;> by_cases hv : v<0 <;> simp [copied,Function.update,hv]
  have hend :
      {copied u v xs 2 with fuel := Counter.marked [true], scratch := BinaryCarry.preparedOutput, zero := Counter.marked (List.replicate (xs 0).length false), out := Function.update (copied u v xs 2).out (decide (v<0)) (Counter.marked (RepeatedAdd.addWord (workWord u v xs (outputIndex u (decide (v<0)))) (workWord u v xs 2))), work := Function.update (copied u v xs 2).work 2 (Counter.marked (workWord u v xs 2))}=final u v xs := by
    apply Bank.ext <;> try rfl
    · funext j; fin_cases j <;> rfl
    · funext b; cases b <;> by_cases hv : v<0 <;> simp [final,copied,outputWord,Function.update,hv]
  change Trace u v t (cfg _ _ pos) (cfg _ _ pos) at htr
  rw [hstart,hend] at htr
  have hj := jump_trace u v (.add (.counter 12)) .done (final u v xs) pos rfl
  exact ⟨t+1,by omega,trace_trans htr hj⟩

end TransposeFollowup.SignedLinearForm


/-! Complete paid computation of a signed linear form. Inputs and
template resources return unchanged; the three products remain stored.
Repeated calls must still provide or pay for fresh work/output storage. -/

namespace TransposeFollowup.SignedLinearForm
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def budget (u v : ℤ) (m : ℕ) : ℕ := 48*m+133+(2*u.natAbs+v.natAbs)*(18*m+52)

theorem complete_trace (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (pos : Port → ℤ) :
    ∃ t≤budget u v (xs 0).length, Trace u v t
      (cfg (.init 0 (.init (.erase 0))) (initial xs) pos)
      (cfg .done (final u v xs) pos) := by
  obtain ⟨a,ha,hz⟩ := init_all u v xs pos
  obtain ⟨b,hb,hm⟩ := multiply_all u v xs h pos
  obtain ⟨c,hc,hc'⟩ := copy_all u v xs h pos
  obtain ⟨d,hd,had⟩ := add_stage u v xs h pos
  exact ⟨a+(b+(c+d)),by dsimp [budget]; omega,
    trace_trans hz (trace_trans hm (trace_trans hc' had))⟩

theorem native_complete (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget u v (xs 0).length,
      Transpose.stepN (nativeMachine u v) input t
        ((cfg (.init 0 (.init (.erase 0))) (initial xs) pos).denote
          (nativeEncoding u v) (program u v) inputPos outRev)=
        some ((cfg .done (final u v xs) pos).denote (nativeEncoding u v) (program u v) inputPos outRev) ∧
      Transpose.step (nativeMachine u v) input
        ((cfg .done (final u v xs) pos).denote (nativeEncoding u v) (program u v) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace u v xs h pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding u v) (program u v)
    input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding u v) (program u v) input inputPos outRev _).mpr
  intro hh
  exact hh.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (u v : ℤ)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label u v → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program u v pc≠.halt → program u v pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program u v pc))
    (xs : Fin 3 → List Bool) (h : ∀ j,(xs j).length=(xs 0).length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget u v (xs 0).length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.init 0 (.init (.erase 0))) (initial xs) pos) frame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final u v xs) pos) frame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace u v xs h pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program u v) target
    frame input inputPos outRev hc htr⟩

theorem exact_components (u v : ℤ) (xs : Fin 3 → List Bool)
    (h : ∀ j,(xs j).length=(xs 0).length)
    (hf : (components u v (Counter.value (xs 0)) (Counter.value (xs 1)) (Counter.value (xs 2))).mass<2^(xs 0).length)
    (pos : Port → ℤ) :
    ∃ t≤budget u v (xs 0).length, ∃ w : Bool → List Bool,
      Trace u v t (cfg (.init 0 (.init (.erase 0))) (initial xs) pos) (cfg .done (final u v xs) pos) ∧
      (∀ b,(final u v xs).out b=Counter.marked (w b)) ∧
      (∀ b,(w b).length=(xs 0).length) ∧
      SignedComponents.Pair.mk (Counter.value (w false)) (Counter.value (w true))=
        ((SignedComponents.Pair.ofInt u).mul ⟨Counter.value (xs 0),Counter.value (xs 1)⟩).add
          ((SignedComponents.Pair.ofInt v).mul ⟨Counter.value (xs 2),0⟩) := by
  obtain ⟨t,ht,htr⟩ := complete_trace u v xs h pos
  refine ⟨t,ht,outputWord u v xs,htr,fun _ => rfl,outputWord_length u v xs h,?_⟩
  rw [outputWord_value u v xs h hf false,outputWord_value u v xs h hf true]
  exact components_spec u v _ _ _

theorem total_budget (F : RationalMobius) (u v : ℤ) (N : ℕ) (xs : List Bool)
    (hN : 1≤N) (hl : xs.length≤(N+1).size) :
    let K := 2*u.natAbs+v.natAbs
    N*(N*budget u v (PaddedWord.word (PaddedWord.commonConstant F) id xs).length) ≤
      ((96+36*K)*(F.integerOperandConstant^2).size+1226+464*K)*Transpose.inputLength N := by
  let K := 2*u.natAbs+v.natAbs
  have he : budget u v (PaddedWord.word (PaddedWord.commonConstant F) id xs).length=
      ((48+18*K)*PaddedWord.commonConstant F+133+52*K)+(96+36*K)*xs.length := by
    rw [PaddedWord.word_length]
    unfold budget K
    ring
  have ht := dense_scan_budget ((48+18*K)*PaddedWord.commonConstant F+133+52*K) (96+36*K) N hN
  rw [he]
  calc
    _ ≤ N*(N*(((48+18*K)*PaddedWord.commonConstant F+133+52*K)+(96+36*K)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert ht using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.SignedLinearForm
