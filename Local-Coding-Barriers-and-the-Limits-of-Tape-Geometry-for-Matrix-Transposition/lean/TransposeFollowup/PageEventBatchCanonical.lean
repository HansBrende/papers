import TransposeFollowup.NativeCounter
import TransposeFollowup.MicrocodeEmbedding
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.RationalPageColor
import TransposeFollowup.FamilySelectorMeaning
import TransposeFollowup.NativePairEqualMachine
import TransposeFollowup.BatchMembershipCalls
import TransposeFollowup.NormalizedBatchLoop

/-! Fixed-modulus residue data. The input encoding is little-endian;
the backward scan reads most-significant bits first. -/
namespace TransposeFollowup.NativeResidue
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def update (d : ℕ) (r : Fin (d+1)) (b : Bool) : Fin (d+1) :=
  ⟨(2*r.val+b.toNat)%(d+1),Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
def accumulate (d : ℕ) (r : Fin (d+1)) (bs : List Bool) := bs.foldl (update d) r
def result (d : ℕ) (xs : List Bool) := accumulate d 0 xs.reverse

theorem result_cons (d : ℕ) (b : Bool) (xs : List Bool) :
    result d (b::xs)=update d (result d xs) b := by
  simp only [result,accumulate,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem result_value (d : ℕ) (xs : List Bool) : (result d xs).val=Counter.value xs%(d+1) := by
  induction xs with
  | nil => simp [result,accumulate,Counter.value]
  | cons b xs ih =>
    rw [result_cons]
    cases b <;> simp [update,Counter.value,ih,Nat.mul_mod,Nat.add_mod]

theorem result_binary_value (d : ℕ) (xs : List Bool) : (result d xs).val=BinaryCompare.value xs%(d+1) := by
  rw [result_value,NativeCounter.word_value]

end TransposeFollowup.NativeResidue


/-! Seek STOP,then fold the bits backward into one finite residue. Return
under the first data cell,with every tape symbol and absolute head restored. -/
namespace TransposeFollowup.NativeResidue
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label (d : ℕ)
  | forward
  | forwardStep
  | back (r : Fin (d+1))
  | backStep (r : Fin (d+1))
  | finish (r : Fin (d+1))
  | done (r : Fin (d+1))
  | reject
  deriving DecidableEq,Fintype

def program (d : ℕ) : Microcode.Program (Fin 1) (Label d)
  | .forward => .read 0 (fun s => match s with | .data _ => .forwardStep | .stop => .backStep 0 | _ => .reject)
  | .forwardStep => .act (fun _ => ⟨none,.right⟩) .forward
  | .back r => .read 0 (fun s => match s with | .data b => .backStep (update d r b) | .start => .finish r | _ => .reject)
  | .backStep r => .act (fun _ => ⟨none,.left⟩) (.back r)
  | .finish r => .act (fun _ => ⟨none,.right⟩) (.done r)
  | .done _ => .halt
  | .reject => .reject

def cfg {d : ℕ} (pc : Label d) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) (Label d) :=
  ⟨⟨pc,fun _ => word⟩,pos⟩

theorem forward_two (d : ℕ) (b : Bool) (left right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program d) 2 (cfg .forward ⟨left,.data b::right⟩ pos)=
      cfg .forward ⟨.data b::left,right⟩ (fun p => pos p+1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Microcode.Action.apply,
    Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem forward_run (d : ℕ) (xs : List Bool) (left suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program d) (2*xs.length+1) (cfg .forward ⟨left,symbols xs++(.stop::suffix)⟩ pos)=
      cfg (.backStep 0) ⟨(symbols xs).reverse++left,.stop::suffix⟩ (fun p => pos p+xs.length) := by
  induction xs generalizing left pos with
  | nil => simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,symbols,Tape.read]
  | cons b xs ih =>
    rw [show 2*(b::xs).length+1=2+(2*xs.length+1) by simp;omega,NativeZipper.run_add]
    simp only [symbols,List.map_cons,List.cons_append]
    rw [forward_two]
    rw [show List.map Sym.data xs=symbols xs from rfl,ih]
    congr 1
    · simp [symbols,List.reverse_cons,List.append_assoc]
    · funext p;simp;ring

theorem back_two (d : ℕ) (r : Fin (d+1)) (b : Bool) (left right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program d) 2 (cfg (.backStep r) ⟨.data b::left,right⟩ pos)=
      cfg (.backStep (update d r b)) ⟨left,.data b::right⟩ (fun p => pos p-1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Microcode.Action.apply,
    Tape.moveLeft,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem back_empty (d : ℕ) (r : Fin (d+1)) (ancestor right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program d) 3 (cfg (.backStep r) ⟨.start::ancestor,right⟩ pos)=
      cfg (.done r) ⟨.start::ancestor,right⟩ pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Microcode.Action.apply,
    Tape.moveLeft,Tape.moveRight,Tape.read,NativeMicrocode.direction,Transpose.Dir.shift]

theorem back_run (d : ℕ) (r : Fin (d+1)) (bs : List Bool) (ancestor right : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program d) (2*bs.length+3) (cfg (.backStep r) ⟨symbols bs++(.start::ancestor),right⟩ pos)=
      cfg (.done (accumulate d r bs)) ⟨.start::ancestor,symbols bs.reverse++right⟩ (fun p => pos p-bs.length) := by
  induction bs generalizing r right pos with
  | nil => simpa only [List.length_nil,mul_zero,zero_add,List.reverse_nil,symbols,List.map_nil,List.nil_append,
      Nat.cast_zero,sub_zero,accumulate,List.foldl_nil] using back_empty d r ancestor right pos
  | cons b bs ih =>
    rw [show 2*(b::bs).length+3=2+(2*bs.length+3) by simp;omega,NativeZipper.run_add]
    simp only [symbols,List.map_cons,List.cons_append]
    rw [back_two]
    rw [show List.map Sym.data bs=symbols bs from rfl,ih]
    congr 1
    · simp [symbols,List.reverse_cons,List.append_assoc]
    · funext p;simp;ring

theorem residue_run (d : ℕ) (xs : List Bool) (ancestor suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program d) (4*xs.length+4)
      (cfg .forward ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos)=
      cfg (.done (result d xs)) ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos := by
  rw [show 4*xs.length+4=(2*xs.length+1)+(2*xs.reverse.length+3) by simp;omega,
    NativeZipper.run_add,forward_run]
  rw [show (symbols xs).reverse=symbols xs.reverse by simp [symbols,List.map_reverse],back_run]
  simp only [List.length_reverse,List.reverse_reverse,result]
  congr 1
  funext p;omega

end TransposeFollowup.NativeResidue


namespace TransposeFollowup.NativeResidue
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem residue_trace (d : ℕ) (xs : List Bool) (ancestor suffix : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    ∃ t ≤ 4*xs.length+4,
      OperationalTrace.Trace (NativeMicrocode.step (program d)) (NativeMicrocode.Active (program d)) t
        (cfg .forward ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote
        (cfg (.done (result d xs)) ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote :=
  NativeZipper.trace_of_run (program d) (residue_run d xs ancestor suffix pos)

noncomputable def nativeEncoding (d : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 1) (Label.forward (d:=d))
noncomputable def nativeMachine (d : ℕ) := NativeMicrocode.machine (nativeEncoding d) (program d)

def labelEquiv (d : ℕ) : Label d ≃ Unit ⊕ Unit ⊕ Fin (d+1) ⊕ Fin (d+1) ⊕ Fin (d+1) ⊕ Fin (d+1) ⊕ Unit where
  toFun
    | .forward => .inl ()
    | .forwardStep => .inr (.inl ())
    | .back r => .inr (.inr (.inl r))
    | .backStep r => .inr (.inr (.inr (.inl r)))
    | .finish r => .inr (.inr (.inr (.inr (.inl r))))
    | .done r => .inr (.inr (.inr (.inr (.inr (.inl r)))))
    | .reject => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  invFun
    | .inl _ => .forward
    | .inr (.inl _) => .forwardStep
    | .inr (.inr (.inl r)) => .back r
    | .inr (.inr (.inr (.inl r))) => .backStep r
    | .inr (.inr (.inr (.inr (.inl r)))) => .finish r
    | .inr (.inr (.inr (.inr (.inr (.inl r))))) => .done r
    | .inr (.inr (.inr (.inr (.inr (.inr _))))) => .reject
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨⟩|⟨⟩|r|r|r|r|⟨⟩) <;> rfl

theorem label_card (d : ℕ) : Fintype.card (Label d)=4*(d+1)+3 := by
  rw [Fintype.card_congr (labelEquiv d)]
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
  omega

theorem fixed_resources (d : ℕ) : (nativeMachine d).k=1 ∧ (nativeMachine d).g+1=5 ∧
    (nativeMachine d).q+1=4*(d+1)+3 ∧ (nativeEncoding d).label .forward=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label d)-1+1=_
  rw [label_card];omega

theorem native_residue (d : ℕ) (xs : List Bool) (ancestor suffix : List (Sym Bool)) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+4,
      Transpose.stepN (nativeMachine d) input t
        ((cfg .forward ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote.denote (nativeEncoding d) (program d) ip outRev)=
        some ((cfg (.done (result d xs)) ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote.denote (nativeEncoding d) (program d) ip outRev) ∧
      Transpose.step (nativeMachine d) input
        ((cfg (.done (result d xs)) ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote.denote (nativeEncoding d) (program d) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=residue_trace d xs ancestor suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding d) (program d) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding d) (program d) input ip outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (d : ℕ) (ports : Fin 1 ↪ U) (labels : Label d → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program d pc≠.halt → program d pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program d pc))
    (xs : List Bool) (ancestor suffix : List (Sym Bool)) (pos : Fin 1 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*xs.length+4,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .forward ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg (.done (result d xs)) ⟨.start::ancestor,symbols xs++(.stop::suffix)⟩ pos).denote outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=residue_trace d xs ancestor suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program d) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.NativeResidue


/-! Two fixed-modulus scans,with their residues in finite control.
Both coordinate fields and both absolute heads are preserved. -/
namespace TransposeFollowup.NativeResiduePair
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def scanBinding (t : Fin 2) : FinitePortBinding (Fin 1) (Fin 2) where
  ports:=⟨fun _ => t,by intro a b _;exact Subsingleton.elim a b⟩
  decode:=fun p => if p=t then some 0 else none
  decode_spec:=by intro p j;fin_cases j;simp;tauto

inductive Label (d : ℕ)
  | first (pc : NativeResidue.Label d)
  | second (r : Fin (d+1)) (pc : NativeResidue.Label d)
  | done (r s : Fin (d+1))
  deriving DecidableEq,Fintype

def start (d : ℕ) : Label d := .first .forward
def program (d : ℕ) : Microcode.Program (Fin 2) (Label d)
  | .first (.done r) => .jump (.second r .forward)
  | .first pc => (scanBinding 0).instruction Label.first (NativeResidue.program d pc)
  | .second r (.done s) => .jump (.done r s)
  | .second r pc => (scanBinding 1).instruction (Label.second r) (NativeResidue.program d pc)
  | .done _ _ => .halt

def scanLabel (d : ℕ) (r : Option (Fin (d+1))) : NativeResidue.Label d → Label d :=
  match r with | none => Label.first | some r => Label.second r
def scanPort {d : ℕ} (r : Option (Fin (d+1))) : Fin 2 := if r.isSome then 1 else 0

theorem scan_code (d : ℕ) (r : Option (Fin (d+1))) (pc : NativeResidue.Label d)
    (hh : NativeResidue.program d pc≠.halt) (_ : NativeResidue.program d pc≠.reject) :
    program d (scanLabel d r pc)=MicrocodeEmbedding.instruction (scanBinding (scanPort r)).ports
      (scanLabel d r) (NativeResidue.program d pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => cases r <;> simp [scanLabel,scanPort,program,FinitePortBinding.instruction_eq]

def bank (a b : Tape Bool) : Fin 2 → Tape Bool := ![a,b]
def cfg {d : ℕ} (pc : Label d) (s : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) : NativeMicrocode.Config (Fin 2) (Label d) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) : MicrocodeEmbedding.Frame (Fin 2) := ⟨fun p => (s p).denote,pos⟩
abbrev Trace (d : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program d)) (NativeMicrocode.Active (program d))

theorem embed_scan (d : ℕ) (r : Option (Fin (d+1))) (pc : NativeResidue.Label d)
    (a : Tape Bool) (s : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) :
    MicrocodeEmbedding.embed (scanBinding (scanPort r)).ports (scanLabel d r)
      (NativeResidue.cfg pc a (fun _ => pos (scanPort r))).denote (frame s pos)=
      cfg (scanLabel d r pc) (Function.update s (scanPort r) a) pos := by
  unfold MicrocodeEmbedding.embed NativeResidue.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (scanBinding (scanPort r)).values_eq_extend]
  congr 2 <;> funext p <;> cases r <;> fin_cases p <;> rfl

theorem scan_call (d : ℕ) (r : Option (Fin (d+1))) (xs : List Bool)
    (s : Fin 2 → Tape Bool) (hs : s (scanPort r)=Counter.marked xs) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace d t (cfg (scanLabel d r .forward) s pos)
      (cfg (scanLabel d r (.done (NativeResidue.result d xs))) s pos) := by
  obtain ⟨t,ht,htr⟩:=NativeResidue.residue_trace d xs [] [] (fun _ => pos (scanPort r))
  have he:=MicrocodeEmbedding.trace_embed (scanBinding (scanPort r)).ports (scanLabel d r)
    (NativeResidue.program d) (program d) (frame s pos) (scan_code d r) htr
  exact ⟨t,ht,by simpa only [embed_scan,show (⟨[Sym.start],symbols xs++[Sym.stop]⟩ : Tape Bool)=Counter.marked xs from rfl,
    ← hs,Function.update_eq_self] using he⟩

theorem jump_trace (d : ℕ) (pc next : Label d) (s : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ)
    (h : program d pc=.jump next) : Trace d 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.NativeResiduePair


namespace TransposeFollowup.NativeResiduePair
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def markedBank (a b : List Bool) := bank (Counter.marked a) (Counter.marked b)

theorem pair_trace (d : ℕ) (a b : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 4*a.length+4*b.length+10,Trace d t
      (cfg (start d) (markedBank a b) pos)
      (cfg (.done (NativeResidue.result d a) (NativeResidue.result d b)) (markedBank a b) pos) := by
  obtain ⟨x,hx,tx⟩:=scan_call d none a (markedBank a b) rfl pos
  have j1:=jump_trace d (.first (.done (NativeResidue.result d a))) (.second (NativeResidue.result d a) .forward)
    (markedBank a b) pos rfl
  obtain ⟨y,hy,ty⟩:=scan_call d (some (NativeResidue.result d a)) b (markedBank a b) rfl pos
  have j2:=jump_trace d (.second (NativeResidue.result d a) (.done (NativeResidue.result d b)))
    (.done (NativeResidue.result d a) (NativeResidue.result d b)) (markedBank a b) pos rfl
  exact ⟨x+1+y+1,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j1) ty) j2⟩

noncomputable def nativeEncoding (d : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 2) (start d)
noncomputable def nativeMachine (d : ℕ) := NativeMicrocode.machine (nativeEncoding d) (program d)

def labelEquiv (d : ℕ) : Label d ≃ NativeResidue.Label d ⊕ (Fin (d+1) × NativeResidue.Label d) ⊕ (Fin (d+1) × Fin (d+1)) where
  toFun | .first pc => .inl pc | .second r pc => .inr (.inl (r,pc)) | .done r s => .inr (.inr (r,s))
  invFun | .inl pc => .first pc | .inr (.inl (r,pc)) => .second r pc | .inr (.inr (r,s)) => .done r s
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|⟨r,pc⟩|⟨r,s⟩) <;> rfl

theorem label_card (d : ℕ) : Fintype.card (Label d)=5*(d+1)^2+7*(d+1)+3 := by
  rw [Fintype.card_congr (labelEquiv d)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,NativeResidue.label_card]
  ring

theorem fixed_resources (d : ℕ) : (nativeMachine d).k=2 ∧ (nativeMachine d).g+1=5 ∧
    (nativeMachine d).q+1=5*(d+1)^2+7*(d+1)+3 ∧ (nativeEncoding d).label (start d)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label d)-1+1=_
  rw [label_card];omega

theorem native_pair (d : ℕ) (a b : List Bool) (pos : Fin 2 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*a.length+4*b.length+10,
      Transpose.stepN (nativeMachine d) input t ((cfg (start d) (markedBank a b) pos).denote (nativeEncoding d) (program d) ip outRev)=
        some ((cfg (.done (NativeResidue.result d a) (NativeResidue.result d b)) (markedBank a b) pos).denote (nativeEncoding d) (program d) ip outRev) ∧
      Transpose.step (nativeMachine d) input ((cfg (.done (NativeResidue.result d a) (NativeResidue.result d b)) (markedBank a b) pos).denote (nativeEncoding d) (program d) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=pair_trace d a b pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding d) (program d) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding d) (program d) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (d : ℕ) (ports : Fin 2 ↪ U) (labels : Label d → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program d pc≠.halt → program d pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program d pc))
    (a b : List Bool) (pos : Fin 2 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*a.length+4*b.length+10,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start d) (markedBank a b) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (NativeResidue.result d a) (NativeResidue.result d b)) (markedBank a b) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=pair_trace d a b pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program d) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.NativeResiduePair


/-! A fixed family and its canonical batch tag determine a finite color
table. Two actual scans supply the coordinate residues;one paid jump
returns their color. No coordinate or dimension enters the state type. -/
namespace TransposeFollowup.NativeResidueColor
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def combine (F : Fin c → RationalMobius) (p : Fin c)
    (a b : Fin (rationalFamilyBound F+1)) : Fin (rationalPageCount F) :=
  finProdFinEquiv (p,finProdFinEquiv (a,b))
def valueColor (F : Fin c → RationalMobius) (p : Fin c) (a b : List Bool) : Fin (rationalPageCount F) :=
  combine F p (NativeResidue.result (rationalFamilyBound F) a) (NativeResidue.result (rationalFamilyBound F) b)

inductive Label (F : Fin c → RationalMobius)
  | pair (pc : NativeResiduePair.Label (rationalFamilyBound F))
  | done (color : Fin (rationalPageCount F))
  deriving DecidableEq,Fintype

def identityBinding : FinitePortBinding (Fin 2) (Fin 2) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p j;simp [eq_comm]
def start (F : Fin c → RationalMobius) : Label F := .pair (NativeResiduePair.start (rationalFamilyBound F))
def program (F : Fin c → RationalMobius) (p : Fin c) : Microcode.Program (Fin 2) (Label F)
  | .pair (.done a b) => .jump (.done (combine F p a b))
  | .pair pc => identityBinding.instruction Label.pair (NativeResiduePair.program (rationalFamilyBound F) pc)
  | .done _ => .halt

theorem pair_code (F : Fin c → RationalMobius) (p : Fin c) (pc : NativeResiduePair.Label (rationalFamilyBound F))
    (hh : NativeResiduePair.program (rationalFamilyBound F) pc≠.halt)
    (_ : NativeResiduePair.program (rationalFamilyBound F) pc≠.reject) :
    program F p (.pair pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.pair
      (NativeResiduePair.program (rationalFamilyBound F) pc) := by
  cases pc with
  | done _ _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def cfg {F : Fin c → RationalMobius} (pc : Label F) (s : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) : NativeMicrocode.Config (Fin 2) (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
abbrev Trace (F : Fin c → RationalMobius) (p : Fin c) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F p)) (NativeMicrocode.Active (program F p))

theorem embed_pair (F : Fin c → RationalMobius) (pc : NativeResiduePair.Label (rationalFamilyBound F))
    (s : Fin 2 → Tape Bool) (pos : Fin 2 → ℤ) (frame : MicrocodeEmbedding.Frame (Fin 2)) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.pair (F:=F)) (NativeResiduePair.cfg pc s pos) frame=
      cfg (.pair pc) s pos := by
  unfold MicrocodeEmbedding.embed NativeResiduePair.cfg cfg
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem color_trace (F : Fin c → RationalMobius) (p : Fin c) (a b : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 4*a.length+4*b.length+11,Trace F p t
      (cfg (start F) (NativeResiduePair.markedBank a b) pos)
      (cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeResiduePair.pair_trace (rationalFamilyBound F) a b pos
  have he:=MicrocodeEmbedding.trace_embed identityBinding.ports (Label.pair (F:=F))
    (NativeResiduePair.program (rationalFamilyBound F)) (program F p)
    (NativeResiduePair.frame (NativeResiduePair.markedBank a b) pos) (pair_code F p) htr
  simp only [embed_pair] at he
  refine ⟨t+1,by omega,NativeCountedLoop.trace_trans he ?_⟩
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · exact .refl _

end TransposeFollowup.NativeResidueColor


namespace TransposeFollowup.NativeResidueColor
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

noncomputable def nativeEncoding (F : Fin c → RationalMobius) := NativeMicrocode.initialEncoding (T:=Fin 2) (start F)
noncomputable def nativeMachine (F : Fin c → RationalMobius) (p : Fin c) := NativeMicrocode.machine (nativeEncoding F) (program F p)

def labelEquiv (F : Fin c → RationalMobius) : Label F ≃ NativeResiduePair.Label (rationalFamilyBound F) ⊕ Fin (rationalPageCount F) where
  toFun | .pair pc => .inl pc | .done color => .inr color
  invFun | .inl pc => .pair pc | .inr color => .done color
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|color) <;> rfl

theorem label_card (F : Fin c → RationalMobius) :
    Fintype.card (Label F)=(c+5)*(rationalFamilyBound F+1)^2+7*(rationalFamilyBound F+1)+3 := by
  rw [Fintype.card_congr (labelEquiv F)]
  simp only [Fintype.card_sum,Fintype.card_fin,NativeResiduePair.label_card,rationalPageCount]
  ring

theorem fixed_resources (F : Fin c → RationalMobius) (p : Fin c) :
    (nativeMachine F p).k=2 ∧ (nativeMachine F p).g+1=5 ∧
    (nativeMachine F p).q+1=(c+5)*(rationalFamilyBound F+1)^2+7*(rationalFamilyBound F+1)+3 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F)-1+1=_
  rw [label_card];omega

theorem native_color (F : Fin c → RationalMobius) (p : Fin c) (a b : List Bool) (pos : Fin 2 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*a.length+4*b.length+11,
      Transpose.stepN (nativeMachine F p) input t
        ((cfg (start F) (NativeResiduePair.markedBank a b) pos).denote (nativeEncoding F) (program F p) ip outRev)=
        some ((cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos).denote (nativeEncoding F) (program F p) ip outRev) ∧
      Transpose.step (nativeMachine F p) input
        ((cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos).denote (nativeEncoding F) (program F p) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=color_trace F p a b pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F p) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F p) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (F : Fin c → RationalMobius) (p : Fin c) (ports : Fin 2 ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F p pc≠.halt → program F p pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F p pc))
    (a b : List Bool) (pos : Fin 2 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 4*a.length+4*b.length+11,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (NativeResiduePair.markedBank a b) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=color_trace F p a b pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F p) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.NativeResidueColor


namespace TransposeFollowup.NativeResidueColor
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem valueColor_spec {c n : ℕ} (F : Fin c → RationalMobius) (p : Fin c)
    (a b : List Bool) (i j : Fin n) (ha : BinaryCompare.value a=i.val) (hb : BinaryCompare.value b=j.val) :
    valueColor F p a b=rationalResidueColor F i j p := by
  unfold valueColor combine rationalResidueColor
  apply congrArg finProdFinEquiv
  apply congrArg (fun q => (p,q))
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · apply Fin.ext;simp only [NativeResidue.result_binary_value,ha]
  · apply Fin.ext;simp only [NativeResidue.result_binary_value,hb]

theorem canonical_color {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : Fin (r+1))
    (a b : List Bool) (i j : Fin (Counter.value xs))
    (ha : BinaryCompare.value a=i.val) (hb : BinaryCompare.value b=j.val)
    (hsel : (a,b) ∈ FirstWitness.selected F xs p) :
    rationalColor F i j=some (valueColor F p a b) := by
  have hm : (i.val,j.val) ∈ (FirstWitness.selected F xs p).map RowEnumeration.decodePair :=
    List.mem_map.mpr ⟨(a,b),hsel,by simp [RowEnumeration.decodePair,ha,hb]⟩
  have ht:=(FirstWitness.selected_tag_spec F xs p i j).mp hm
  rw [rationalColor,ht,Option.map_some,valueColor_spec F p a b i j ha hb]

theorem selected_width {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : Fin (r+1))
    (a b : List Bool) (hsel : (a,b) ∈ FirstWitness.selected F xs p) :
    a.length=2*xs.length+FamilyNormalization.common F ∧ b.length=2*xs.length+FamilyNormalization.common F := by
  have hr : ∀ q ∈ FamilyNormalization.records F xs p,
      q.1.length=2*xs.length+PaddedWord.commonConstant (F p) ∧ q.2.length=2*xs.length+PaddedWord.commonConstant (F p) := by
    simpa only [PaddedWord.word_length,FamilyNormalization.records] using
      RowEnumeration.rows_records_width (F p) xs (Counter.value xs) 0
  have hw:=FilteredBatch.selected_width (PaddedWord.commonConstant (F p)) (FamilyNormalization.padding F p)
    xs (FirstWitness.earlierBatches F xs p) (FamilyNormalization.records F xs p) hr (a,b) hsel
  have hc : PaddedWord.commonConstant (F p)+FamilyNormalization.padding F p=FamilyNormalization.common F :=
    Nat.add_sub_of_le (FamilyNormalization.le_common F p)
  simpa only [hc] using hw

theorem selected_color_trace {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : Fin (r+1))
    (a b : List Bool) (hsel : (a,b) ∈ FirstWitness.selected F xs p) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 16*xs.length+8*FamilyNormalization.common F+11,Trace F p t
      (cfg (start F) (NativeResiduePair.markedBank a b) pos)
      (cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos) := by
  obtain ⟨ha,hb⟩:=selected_width F xs p a b hsel
  obtain ⟨t,ht,htr⟩:=color_trace F p a b pos
  exact ⟨t,by rw [ha,hb] at ht;omega,htr⟩

theorem native_selected {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (p : Fin (r+1))
    (a b : List Bool) (i j : Fin (Counter.value xs))
    (ha : BinaryCompare.value a=i.val) (hb : BinaryCompare.value b=j.val)
    (hsel : (a,b) ∈ FirstWitness.selected F xs p) (pos : Fin 2 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    rationalColor F i j=some (valueColor F p a b) ∧
    ∃ t ≤ 4*a.length+4*b.length+11,
      Transpose.stepN (nativeMachine F p) input t
        ((cfg (start F) (NativeResiduePair.markedBank a b) pos).denote (nativeEncoding F) (program F p) ip outRev)=
        some ((cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos).denote (nativeEncoding F) (program F p) ip outRev) ∧
      Transpose.step (nativeMachine F p) input
        ((cfg (.done (valueColor F p a b)) (NativeResiduePair.markedBank a b) pos).denote (nativeEncoding F) (program F p) ip outRev)=none :=
  ⟨canonical_color F xs p a b i j ha hb hsel,native_color F p a b pos input ip outRev⟩

end TransposeFollowup.NativeResidueColor


/-! Test one prepared canonical record against a vertex and a page.
Only the direction,page and map tag are fixed control data;the vertex
and both record coordinates remain on three preserved work tapes. -/
namespace TransposeFollowup.PageRecordTest
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def colorBinding : FinitePortBinding (Fin 2) (Fin 3) where
  ports:=⟨![1,2],by decide +kernel⟩
  decode:=fun p => if p=1 then some 0 else if p=2 then some 1 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def fieldPort (incoming : Bool) : Fin 3 := if incoming then 2 else 1
def compareBinding (incoming : Bool) : FinitePortBinding (Fin 2) (Fin 3) where
  ports:=⟨![0,fieldPort incoming],by cases incoming <;> decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=fieldPort incoming then some 1 else none
  decode_spec:=by intro p j;cases incoming <;> fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label (F : Fin c → RationalMobius)
  | color (pc : NativeResidueColor.Label F)
  | compare (pc : BinaryCompare.Label)
  | done (found : Bool)
  deriving DecidableEq,Fintype
def start (F : Fin c → RationalMobius) : Label F := .color (NativeResidueColor.start F)
def program (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :
    Microcode.Program (Fin 3) (Label F)
  | .color (.done p) => .jump (if p=page then .compare (.scan .equal) else .done false)
  | .color pc => colorBinding.instruction Label.color (NativeResidueColor.program F tag pc)
  | .compare (.done rel) => .jump (.done (decide (rel=.equal)))
  | .compare pc => (compareBinding incoming).instruction Label.compare (BinaryCompare.program pc)
  | .done _ => .halt

theorem color_code (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc : NativeResidueColor.Label F) (hh : NativeResidueColor.program F tag pc≠.halt)
    (_ : NativeResidueColor.program F tag pc≠.reject) :
    program F tag incoming page (.color pc)=MicrocodeEmbedding.instruction colorBinding.ports Label.color
      (NativeResidueColor.program F tag pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem compare_code (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc : BinaryCompare.Label) (hh : BinaryCompare.program pc≠.halt) (_ : BinaryCompare.program pc≠.reject) :
    program F tag incoming page (.compare pc)=MicrocodeEmbedding.instruction (compareBinding incoming).ports Label.compare
      (BinaryCompare.program pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def bank (query first second : Tape Bool) : Fin 3 → Tape Bool := ![query,first,second]
def markedBank (query first second : List Bool) := bank (Counter.marked query) (Counter.marked first) (Counter.marked second)
def cfg {F : Fin c → RationalMobius} (pc : Label F) (s : Fin 3 → Tape Bool) (pos : Fin 3 → ℤ) : NativeMicrocode.Config (Fin 3) (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Fin 3 → Tape Bool) (pos : Fin 3 → ℤ) : MicrocodeEmbedding.Frame (Fin 3) := ⟨fun p => (s p).denote,pos⟩
abbrev Trace (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F tag incoming page)) (NativeMicrocode.Active (program F tag incoming page))

theorem embed_color (F : Fin c → RationalMobius) (pc : NativeResidueColor.Label F)
    (q a b : Tape Bool) (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed colorBinding.ports (Label.color (F:=F))
      (NativeResidueColor.cfg pc (NativeResiduePair.bank a b) (fun p => pos (colorBinding.ports p)))
      (frame (bank q a b) pos)=cfg (.color pc) (bank q a b) pos := by
  unfold MicrocodeEmbedding.embed NativeResidueColor.cfg cfg frame
  simp only [← colorBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem color_call (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (q a b : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 4*a.length+4*b.length+11,Trace F tag incoming page t
      (cfg (start F) (markedBank q a b) pos)
      (cfg (.color (.done (NativeResidueColor.valueColor F tag a b))) (markedBank q a b) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeResidueColor.color_trace F tag a b (fun p => pos (colorBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed colorBinding.ports (Label.color (F:=F)) (NativeResidueColor.program F tag)
    (program F tag incoming page) (frame (markedBank q a b) pos) (color_code F tag incoming page) htr
  exact ⟨t,ht,by simpa only [NativeResiduePair.markedBank,markedBank,embed_color,start] using he⟩

theorem embed_compare (F : Fin c → RationalMobius) (incoming : Bool) (pc : BinaryCompare.Label)
    (a b : Tape Bool) (s : Fin 3 → Tape Bool) (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed (compareBinding incoming).ports (Label.compare (F:=F))
      (BinaryCompare.cfg pc a b (fun p => pos ((compareBinding incoming).ports p))).denote (frame s pos)=
      cfg (.compare pc) (Function.update (Function.update s 0 a) (fieldPort incoming) b) pos := by
  unfold MicrocodeEmbedding.embed BinaryCompare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (compareBinding incoming).values_eq_extend]
  congr 2 <;> funext p <;> cases incoming <;> fin_cases p <;> rfl

theorem compare_call (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (q a b : List Bool) (hqa : q.length=a.length) (hqb : q.length=b.length) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 5*q.length+6,Trace F tag incoming page t
      (cfg (.compare (.scan .equal)) (markedBank q a b) pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (BinaryCompare.value q) (BinaryCompare.value (if incoming then b else a)))))
        (markedBank q a b) pos) := by
  have hw : q.length=(if incoming then b else a).length := by cases incoming <;> assumption
  obtain ⟨t,ht,htr⟩:=BinaryCompare.comparison_trace q (if incoming then b else a) hw
    (fun p => pos ((compareBinding incoming).ports p))
  have he:=MicrocodeEmbedding.trace_embed (compareBinding incoming).ports (Label.compare (F:=F)) BinaryCompare.program
    (program F tag incoming page) (frame (markedBank q a b) pos) (compare_code F tag incoming page) htr
  have ha : BinaryCompare.marked q=markedBank q a b 0 := rfl
  have hb : BinaryCompare.marked (if incoming then b else a)=markedBank q a b (fieldPort incoming) := by cases incoming <;> rfl
  exact ⟨t,ht,by simpa only [embed_compare,ha,hb,Function.update_eq_self] using he⟩

theorem jump_trace (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc next : Label F) (s : Fin 3 → Tape Bool) (pos : Fin 3 → ℤ)
    (h : program F tag incoming page pc=.jump next) : Trace F tag incoming page 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

def hit (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (q a b : List Bool) : Bool :=
  decide (NativeResidueColor.valueColor F tag a b=page) &&
    decide (BinaryCompare.value q=BinaryCompare.value (if incoming then b else a))

end TransposeFollowup.PageRecordTest


namespace TransposeFollowup.PageRecordTest
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

theorem test_trace (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (q a b : List Bool) (hqa : q.length=a.length) (hqb : q.length=b.length) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 13*q.length+19,Trace F tag incoming page t
      (cfg (start F) (markedBank q a b) pos)
      (cfg (.done (hit F tag incoming page q a b)) (markedBank q a b) pos) := by
  obtain ⟨x,hx,tx⟩:=color_call F tag incoming page q a b pos
  rw [← hqa,← hqb] at hx
  by_cases hp : NativeResidueColor.valueColor F tag a b=page
  · have j1:=jump_trace F tag incoming page (.color (.done (NativeResidueColor.valueColor F tag a b)))
      (.compare (.scan .equal)) (markedBank q a b) pos (by simp [program,hp])
    obtain ⟨y,hy,ty⟩:=compare_call F tag incoming page q a b hqa hqb pos
    let rel:=BinaryCompare.numeric .equal (BinaryCompare.value q) (BinaryCompare.value (if incoming then b else a))
    have j2:=jump_trace F tag incoming page (.compare (.done rel)) (.done (decide (rel=.equal))) (markedBank q a b) pos rfl
    have hr : decide (rel=.equal)=hit F tag incoming page q a b := by
      simp [rel,hit,hp,NativePairEqual.numeric_equal_iff]
    refine ⟨x+1+y+1,by omega,?_⟩
    simpa only [hr] using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j1) ty) j2
  · have j:=jump_trace F tag incoming page (.color (.done (NativeResidueColor.valueColor F tag a b)))
      (.done false) (markedBank q a b) pos (by simp [program,hp])
    have hr : hit F tag incoming page q a b=false := by simp [hit,hp]
    refine ⟨x+1,by omega,?_⟩
    simpa only [hr] using NativeCountedLoop.trace_trans tx j

noncomputable def nativeEncoding (F : Fin c → RationalMobius) := NativeMicrocode.initialEncoding (T:=Fin 3) (start F)
noncomputable def nativeMachine (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :=
  NativeMicrocode.machine (nativeEncoding F) (program F tag incoming page)

def labelEquiv (F : Fin c → RationalMobius) : Label F ≃ NativeResidueColor.Label F ⊕ BinaryCompare.Label ⊕ Bool where
  toFun | .color pc => .inl pc | .compare pc => .inr (.inl pc) | .done found => .inr (.inr found)
  invFun | .inl pc => .color pc | .inr (.inl pc) => .compare pc | .inr (.inr found) => .done found
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc|found) <;> rfl

theorem label_card (F : Fin c → RationalMobius) :
    Fintype.card (Label F)=(c+5)*(rationalFamilyBound F+1)^2+7*(rationalFamilyBound F+1)+33 := by
  rw [Fintype.card_congr (labelEquiv F)]
  have hb : Fintype.card BinaryCompare.Label=28 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_bool,NativeResidueColor.label_card,hb]

theorem fixed_resources (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :
    (nativeMachine F tag incoming page).k=3 ∧ (nativeMachine F tag incoming page).g+1=5 ∧
    (nativeMachine F tag incoming page).q+1=(c+5)*(rationalFamilyBound F+1)^2+7*(rationalFamilyBound F+1)+33 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F)-1+1=_
  rw [label_card];omega

theorem native_test (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (q a b : List Bool) (hqa : q.length=a.length) (hqb : q.length=b.length) (pos : Fin 3 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 13*q.length+19,
      Transpose.stepN (nativeMachine F tag incoming page) input t
        ((cfg (start F) (markedBank q a b) pos).denote (nativeEncoding F) (program F tag incoming page) ip outRev)=
        some ((cfg (.done (hit F tag incoming page q a b)) (markedBank q a b) pos).denote (nativeEncoding F) (program F tag incoming page) ip outRev) ∧
      Transpose.step (nativeMachine F tag incoming page) input
        ((cfg (.done (hit F tag incoming page q a b)) (markedBank q a b) pos).denote (nativeEncoding F) (program F tag incoming page) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=test_trace F tag incoming page q a b hqa hqb pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F tag incoming page) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F tag incoming page) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k s : ℕ} (encoding : NativeMicrocode.Encoding U J k s)
    (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (ports : Fin 3 ↪ U) (labels : Label F → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F tag incoming page pc≠.halt → program F tag incoming page pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F tag incoming page pc))
    (q a b : List Bool) (hqa : q.length=a.length) (hqb : q.length=b.length) (pos : Fin 3 → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 13*q.length+19,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (markedBank q a b) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (hit F tag incoming page q a b)) (markedBank q a b) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=test_trace F tag incoming page q a b hqa hqb pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F tag incoming page) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.PageRecordTest


namespace TransposeFollowup.PageRecordTest
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem hit_selected {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1))
    (incoming : Bool) (page : Fin (rationalPageCount F)) (q a b : List Bool) (i j : Fin (Counter.value xs))
    (ha : BinaryCompare.value a=i.val) (hb : BinaryCompare.value b=j.val)
    (hsel : (a,b) ∈ FirstWitness.selected F xs tag) :
    hit F tag incoming page q a b=true ↔ rationalColor F i j=some page ∧
      BinaryCompare.value q=(if incoming then j else i).val := by
  rw [NativeResidueColor.canonical_color F xs tag a b i j ha hb hsel]
  cases incoming <;> simp [hit,ha,hb]

theorem selected_test_trace {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1))
    (incoming : Bool) (page : Fin (rationalPageCount F)) (q a b : List Bool)
    (hq : q.length=2*xs.length+FamilyNormalization.common F) (hsel : (a,b) ∈ FirstWitness.selected F xs tag)
    (pos : Fin 3 → ℤ) :
    ∃ t ≤ 26*xs.length+13*FamilyNormalization.common F+19,Trace F tag incoming page t
      (cfg (start F) (markedBank q a b) pos)
      (cfg (.done (hit F tag incoming page q a b)) (markedBank q a b) pos) := by
  obtain ⟨ha,hb⟩:=NativeResidueColor.selected_width F xs tag a b hsel
  obtain ⟨t,ht,htr⟩:=test_trace F tag incoming page q a b (by omega) (by omega) pos
  exact ⟨t,by rw [hq] at ht;omega,htr⟩

end TransposeFollowup.PageRecordTest


/-! One canonical map batch. Reuse the existing reader/eraser wiring and
tape bank;replace whole-pair equality by the paid vertex-and-color test. -/
namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}
abbrev Bank := BatchMembership.Bank
abbrev bank := BatchMembership.bank
abbrev frame := BatchMembership.frame
abbrev advance := BatchMembership.advance
abbrev readBinding := BatchMembership.readBinding
abbrev eraseBinding := BatchMembership.eraseBinding
abbrev fieldPort := BatchMembership.fieldPort
abbrev liftRead := BatchMembership.liftRead

def testBinding : FinitePortBinding (Fin 3) (Fin 7) where
  ports:=⟨![5,3,4],by decide +kernel⟩
  decode:=fun p => if p=5 then some 0 else if p=3 then some 1 else if p=4 then some 2 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
inductive Label (F : Fin c → RationalMobius) (small : ℕ)
  | read (found : Bool) (pc : PreparedPair.Label small 0)
  | test (found : Bool) (pc : PageRecordTest.Label F)
  | erase (found second : Bool) (pc : NativeErase.Label)
  | done (found : Bool)
  deriving DecidableEq,Fintype
def start (F : Fin c → RationalMobius) (small : ℕ) (found : Bool) : Label F small :=
  .read found (.prepare (.init (.erase 0)))
def program (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :
    Microcode.Program (Fin 7) (Label F small)
  | .read found (.done true) => .jump (.test found (PageRecordTest.start F))
  | .read found (.done false) => .jump (.done found)
  | .read found pc => readBinding.instruction (Label.read found) (PreparedPair.program small 0 pc)
  | .test found (.done hit) => .jump (.erase (found || hit) false 2)
  | .test found pc => testBinding.instruction (Label.test found) (PageRecordTest.program F tag incoming page pc)
  | .erase found second pc => if pc=0 then .jump (if second then start F small found else .erase found true 2)
    else (eraseBinding second).instruction (Label.erase found second) (NativeErase.program pc)
  | .done _ => .halt

theorem read_code (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (pc : PreparedPair.Label small 0) (hh : PreparedPair.program small 0 pc≠.halt)
    (_ : PreparedPair.program small 0 pc≠.reject) :
    program F small tag incoming page (.read found pc)=MicrocodeEmbedding.instruction readBinding.ports
      (Label.read found) (PreparedPair.program small 0 pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem test_code (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (pc : PageRecordTest.Label F) (hh : PageRecordTest.program F tag incoming page pc≠.halt)
    (_ : PageRecordTest.program F tag incoming page pc≠.reject) :
    program F small tag incoming page (.test found pc)=MicrocodeEmbedding.instruction testBinding.ports
      (Label.test found) (PageRecordTest.program F tag incoming page pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]
theorem erase_code (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found second : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program F small tag incoming page (.erase found second pc)=MicrocodeEmbedding.instruction (eraseBinding second).ports
      (Label.erase found second) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

def cfg {F : Fin c → RationalMobius} {small : ℕ} (pc : Label F small) (s : Bank) (pos : Fin 7 → ℤ) : NativeMicrocode.Config (Fin 7) (Label F small) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
abbrev Trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F small tag incoming page)) (NativeMicrocode.Active (program F small tag incoming page))
def queryBank (xs q : List Bool) (input : Tape Bool) : Bank :=
  bank (Counter.marked xs) ⟨[],[]⟩ input ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked q) ⟨[],[]⟩
def matchesRecord (F : Fin c → RationalMobius) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (q : List Bool) (p : List Bool × List Bool) := PageRecordTest.hit F tag incoming page q p.1 p.2

theorem embed_read (F : Fin c → RationalMobius) (small : ℕ) (found : Bool) (pc : PreparedPair.Label small 0)
    (s base : PreparedPair.Bank) (a b : Tape Bool) (rpos : Fin 5 → ℤ) (pos : Fin 7 → ℤ) :
    MicrocodeEmbedding.embed readBinding.ports (Label.read (F:=F) found) (PreparedPair.cfg pc s rpos)
      (frame (liftRead base a b) pos)=cfg (.read found pc) (liftRead s a b) (readBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed PreparedPair.cfg cfg frame BatchMembership.frame
  simp only [← readBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl

theorem read_pair_call (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PreparedPair.pairBudget small 0 xs,Trace F small tag incoming page t
      (cfg (start F small found) (queryBank xs q ⟨pre,symbols (first++second)++suffix⟩) pos)
      (cfg (.read found (.done true)) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked first) (Counter.marked second) (Counter.marked q) ⟨[],[]⟩) (advance pos (2*(2*xs.length+small)))) := by
  obtain ⟨t,ht,htr⟩:=PreparedPair.pair_trace small 0 xs first second hp hf hs pre suffix (fun p => pos (readBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (F:=F) found) (PreparedPair.program small 0)
    (program F small tag incoming page)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)
      (Counter.marked q) ⟨[],[]⟩) pos) (read_code F small tag incoming page found) htr
  simp only [embed_read,BatchMembership.read_positions,BatchMembership.read_final_positions] at he
  exact ⟨t,ht,by simpa only [BatchMembership.liftRead_bank,start,queryBank,NativePaddedField.padded,List.replicate_zero,List.append_nil] using he⟩

theorem read_stop_call (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs,Trace F small tag incoming page t
      (cfg (start F small found) (queryBank xs q ⟨pre,.stop::suffix⟩) pos)
      (cfg (.read found (.done false)) (queryBank xs q ⟨.stop::pre,suffix⟩) (advance pos 1)) := by
  obtain ⟨t,ht,htr⟩:=PreparedPair.stop_trace small 0 xs pre suffix (fun p => pos (readBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (F:=F) found) (PreparedPair.program small 0)
    (program F small tag incoming page)
    (frame (liftRead (PreparedPair.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)
      (Counter.marked q) ⟨[],[]⟩) pos) (read_code F small tag incoming page found) htr
  simp only [embed_read,BatchMembership.read_positions,BatchMembership.read_final_positions] at he
  exact ⟨t,ht,by simpa only [BatchMembership.liftRead_bank,start,queryBank] using he⟩

end TransposeFollowup.PageEventBatch


namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def liftTest (source template input spare : Tape Bool) (s : Fin 3 → Tape Bool) : Bank :=
  bank source template input (s 1) (s 2) (s 0) spare
theorem liftTest_marked (source template input spare : Tape Bool) (q a b : List Bool) :
    liftTest source template input spare (PageRecordTest.markedBank q a b)=
      bank source template input (Counter.marked a) (Counter.marked b) (Counter.marked q) spare := by
  funext p;fin_cases p <;> rfl

theorem embed_test (F : Fin c → RationalMobius) (small : ℕ) (found : Bool) (pc : PageRecordTest.Label F)
    (s base : Fin 3 → Tape Bool) (source template input spare : Tape Bool) (rpos : Fin 3 → ℤ) (pos : Fin 7 → ℤ) :
    MicrocodeEmbedding.embed testBinding.ports (Label.test (small:=small) found) (PageRecordTest.cfg pc s rpos)
      (frame (liftTest source template input spare base) pos)=
      cfg (.test found pc) (liftTest source template input spare s) (testBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed PageRecordTest.cfg cfg frame BatchMembership.frame
  simp only [← testBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl
theorem test_positions (pos : Fin 7 → ℤ) : testBinding.values (fun p => pos (testBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl

theorem test_call (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (q a b : List Bool) (hqa : q.length=a.length) (hqb : q.length=b.length)
    (source template input spare : Tape Bool) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 13*q.length+19,Trace F small tag incoming page t
      (cfg (.test found (PageRecordTest.start F))
        (bank source template input (Counter.marked a) (Counter.marked b) (Counter.marked q) spare) pos)
      (cfg (.test found (.done (PageRecordTest.hit F tag incoming page q a b)))
        (bank source template input (Counter.marked a) (Counter.marked b) (Counter.marked q) spare) pos) := by
  obtain ⟨t,ht,htr⟩:=PageRecordTest.test_trace F tag incoming page q a b hqa hqb (fun p => pos (testBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed testBinding.ports (Label.test (small:=small) found)
    (PageRecordTest.program F tag incoming page) (program F small tag incoming page)
    (frame (liftTest source template input spare (PageRecordTest.markedBank q a b)) pos)
    (test_code F small tag incoming page found) htr
  simp only [embed_test,test_positions] at he
  exact ⟨t,ht,by simpa only [liftTest_marked] using he⟩

theorem embed_erase (F : Fin c → RationalMobius) (small : ℕ) (found second : Bool) (pc : NativeErase.Label)
    (word : Tape Bool) (s : Bank) (pos : Fin 7 → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding second).ports (Label.erase (F:=F) (small:=small) found second)
      (NativeErase.cfg pc word (fun _ => pos (fieldPort second))).denote (frame s pos)=
      cfg (.erase found second pc) (Function.update s (fieldPort second) word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame BatchMembership.frame
  simp only [← (eraseBinding second).values_eq_extend]
  congr 2 <;> funext p <;> cases second <;> fin_cases p <;> rfl

theorem erase_call (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found second : Bool) (xs : List Bool) (s : Bank) (hs : s (fieldPort second)=Counter.marked xs) (pos : Fin 7 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace F small tag incoming page t (cfg (.erase found second 2) s pos)
      (cfg (.erase found second 0) (Function.update s (fieldPort second) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeErase.erase_trace xs (fun _ => pos (fieldPort second))
  have he:=MicrocodeEmbedding.trace_embed (eraseBinding second).ports (Label.erase (F:=F) (small:=small) found second)
    NativeErase.program (program F small tag incoming page) (frame s pos) (erase_code F small tag incoming page found second) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Function.update_eq_self] using he⟩

theorem jump_trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (pc next : Label F small) (s : Bank) (pos : Fin 7 → ℤ)
    (h : program F small tag incoming page pc=.jump next) : Trace F small tag incoming page 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.PageEventBatch


namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def recordBudget (small : ℕ) (xs : List Bool) := 90*xs.length+42*small+92

theorem record_trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (hq : q.length=2*xs.length+small)
    (first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ recordBudget small xs,Trace F small tag incoming page t
      (cfg (start F small found) (queryBank xs q ⟨pre,symbols (first++second)++suffix⟩) pos)
      (cfg (start F small (found || matchesRecord F tag incoming page q (first,second)))
        (queryBank xs q ⟨(symbols (first++second)).reverse++pre,suffix⟩) (advance pos (2*(2*xs.length+small)))) := by
  let source:=Counter.marked xs
  let input : Tape Bool := ⟨(symbols (first++second)).reverse++pre,suffix⟩
  let Q:=Counter.marked q
  let adv:=advance pos (2*(2*xs.length+small))
  let found':=found || matchesRecord F tag incoming page q (first,second)
  obtain ⟨x,hx,tx⟩:=read_pair_call F small tag incoming page found xs q first second hp hf hs pre suffix pos
  have j1:=jump_trace F small tag incoming page (.read found (.done true)) (.test found (PageRecordTest.start F))
    (bank source ⟨[],[]⟩ input (Counter.marked first) (Counter.marked second) Q ⟨[],[]⟩) adv rfl
  obtain ⟨y,hy,ty⟩:=test_call F small tag incoming page found q first second (by omega) (by omega)
    source ⟨[],[]⟩ input ⟨[],[]⟩ adv
  have j2:=jump_trace F small tag incoming page (.test found (.done (PageRecordTest.hit F tag incoming page q first second)))
    (.erase found' false 2) (bank source ⟨[],[]⟩ input (Counter.marked first) (Counter.marked second) Q ⟨[],[]⟩) adv rfl
  obtain ⟨z,hz,tz⟩:=erase_call F small tag incoming page found' false first
    (bank source ⟨[],[]⟩ input (Counter.marked first) (Counter.marked second) Q ⟨[],[]⟩) rfl adv
  rw [BatchMembership.update_first] at tz
  have j3:=jump_trace F small tag incoming page (.erase found' false 0) (.erase found' true 2)
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ (Counter.marked second) Q ⟨[],[]⟩) adv rfl
  obtain ⟨v,hv,tv⟩:=erase_call F small tag incoming page found' true second
    (bank source ⟨[],[]⟩ input ⟨[],[]⟩ (Counter.marked second) Q ⟨[],[]⟩) rfl adv
  rw [BatchMembership.update_second] at tv
  have j4:=jump_trace F small tag incoming page (.erase found' true 0) (start F small found') (queryBank xs q input) adv rfl
  refine ⟨x+1+y+1+z+1+v+1,?_,?_⟩
  · dsimp only [PreparedPair.pairBudget] at hx
    dsimp only [recordBudget]
    omega
  · exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tx j1) ty) j2) tz) j3) tv) j4

theorem stop_trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ PreparedPair.stopBudget small xs+1,Trace F small tag incoming page t
      (cfg (start F small found) (queryBank xs q ⟨pre,.stop::suffix⟩) pos)
      (cfg (.done found) (queryBank xs q ⟨.stop::pre,suffix⟩) (advance pos 1)) := by
  obtain ⟨t,ht,htr⟩:=read_stop_call F small tag incoming page found xs q pre suffix pos
  have tj:=jump_trace F small tag incoming page (.read found (.done false)) (.done found)
    (queryBank xs q ⟨.stop::pre,suffix⟩) (advance pos 1) rfl
  exact ⟨t+1,by omega,NativeCountedLoop.trace_trans htr tj⟩

end TransposeFollowup.PageEventBatch


namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def batchBudget (small : ℕ) (xs : List Bool) (rs : List (List Bool × List Bool)) :=
  rs.length*recordBudget small xs+PreparedPair.stopBudget small xs+1

theorem records_trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ rs.length*recordBudget small xs,Trace F small tag incoming page t
      (cfg (start F small found) (queryBank xs q ⟨pre,symbols (NormalizedBatch.inputBits rs)++suffix⟩) pos)
      (cfg (start F small (found || rs.any (matchesRecord F tag incoming page q)))
        (queryBank xs q ⟨(symbols (NormalizedBatch.inputBits rs)).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBits rs).length)) := by
  induction rs generalizing found pre pos with
  | nil =>
    refine ⟨0,by simp,?_⟩
    simp only [NormalizedBatch.inputBits,List.flatMap_nil,symbols,List.map_nil,List.nil_append,List.reverse_nil,List.length_nil,
      List.any_nil,Bool.or_false,BatchMembership.advance_zero]
    exact .refl _
  | cons p rs ih =>
    have hpw:=hw p (by simp)
    have hrw : ∀ v ∈ rs,v.1.length=2*xs.length+small ∧ v.2.length=2*xs.length+small := by
      intro v hv;exact hw v (by simp [hv])
    have hlen : (p.1++p.2).length=2*(2*xs.length+small) := by simp [hpw.1,hpw.2,two_mul]
    obtain ⟨x,hx,tx⟩:=record_trace F small tag incoming page found xs q hq p.1 p.2 hp hpw.1 hpw.2
      pre (symbols (NormalizedBatch.inputBits rs)++suffix) pos
    rw [← hlen] at tx
    obtain ⟨y,hy,ty⟩:=ih (found || matchesRecord F tag incoming page q p) hrw
      ((symbols (p.1++p.2)).reverse++pre) (advance pos (p.1++p.2).length)
    refine ⟨x+y,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [NormalizedBatch.inputBits,List.flatMap_cons,symbols,List.map_append,List.reverse_append,List.append_assoc,
        List.length_append,BatchMembership.advance_add,Nat.add_assoc,List.any_cons,Bool.or_assoc] using NativeCountedLoop.trace_trans tx ty

theorem batch_trace (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ batchBudget small xs rs,Trace F small tag incoming page t
      (cfg (start F small found) (queryBank xs q ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos)
      (cfg (.done (found || rs.any (matchesRecord F tag incoming page q)))
        (queryBank xs q ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)) := by
  obtain ⟨x,hx,tx⟩:=records_trace F small tag incoming page found xs q hq hp rs hw pre (.stop::suffix) pos
  obtain ⟨y,hy,ty⟩:=stop_trace F small tag incoming page (found || rs.any (matchesRecord F tag incoming page q)) xs q
    ((symbols (NormalizedBatch.inputBits rs)).reverse++pre) suffix (advance pos (NormalizedBatch.inputBits rs).length)
  refine ⟨x+y,by unfold batchBudget;omega,?_⟩
  simpa only [NormalizedBatch.inputBatch,List.append_assoc,List.cons_append,List.nil_append,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.length_append,List.length_cons,List.length_nil,symbols,List.length_map,BatchMembership.advance_add] using NativeCountedLoop.trace_trans tx ty

theorem batch_budget_le (small : ℕ) (xs : List Bool) (rs : List (List Bool × List Bool)) :
    batchBudget small xs rs≤(rs.length+1)*recordBudget small xs := by
  unfold batchBudget
  have h : PreparedPair.stopBudget small xs+1≤recordBudget small xs := by unfold PreparedPair.stopBudget recordBudget;omega
  rw [Nat.add_mul,Nat.one_mul]
  omega

end TransposeFollowup.PageEventBatch


namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

noncomputable def nativeEncoding (F : Fin c → RationalMobius) (small : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Fin 7) (start F small false)
noncomputable def nativeMachine (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :=
  NativeMicrocode.machine (nativeEncoding F small) (program F small tag incoming page)

def labelEquiv (F : Fin c → RationalMobius) (small : ℕ) : Label F small ≃
    (Bool × PreparedPair.Label small 0) ⊕ (Bool × PageRecordTest.Label F) ⊕ (Bool × Bool × NativeErase.Label) ⊕ Bool where
  toFun
    | .read f pc => .inl (f,pc)
    | .test f pc => .inr (.inl (f,pc))
    | .erase f s pc => .inr (.inr (.inl (f,s,pc)))
    | .done f => .inr (.inr (.inr f))
  invFun
    | .inl (f,pc) => .read f pc
    | .inr (.inl (f,pc)) => .test f pc
    | .inr (.inr (.inl (f,s,pc))) => .erase f s pc
    | .inr (.inr (.inr f)) => .done f
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨f,pc⟩|⟨f,pc⟩|⟨f,s,pc⟩|f) <;> rfl

theorem label_card (F : Fin c → RationalMobius) (small : ℕ) :
    Fintype.card (Label F small)=2*small+2*Fintype.card (PageRecordTest.Label F)+362 := by
  rw [Fintype.card_congr (labelEquiv F small)]
  have hs:=(PreparedPair.fixed_resources small 0).2.2.1
  change Fintype.card (PreparedPair.Label small 0)-1+1=small+2*0+164 at hs
  have hp : 0<Fintype.card (PreparedPair.Label small 0) := Fintype.card_pos_iff.mpr ⟨.prepare (.init (.erase 0))⟩
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,he]
  omega

theorem fixed_resources (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F)) :
    (nativeMachine F small tag incoming page).k=7 ∧ (nativeMachine F small tag incoming page).g+1=5 ∧
    (nativeMachine F small tag incoming page).q+1=2*small+2*Fintype.card (PageRecordTest.Label F)+362 ∧
    (nativeEncoding F small).label (start F small false)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F small)-1+1=_
  rw [label_card];omega

theorem native_batch (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (found : Bool) (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small xs rs,
      Transpose.stepN (nativeMachine F small tag incoming page) input t
        ((cfg (start F small found) (queryBank xs q ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos).denote
          (nativeEncoding F small) (program F small tag incoming page) ip outRev)=
        some ((cfg (.done (found || rs.any (matchesRecord F tag incoming page q)))
          (queryBank xs q ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)).denote
          (nativeEncoding F small) (program F small tag incoming page) ip outRev) ∧
      Transpose.step (nativeMachine F small tag incoming page) input
        ((cfg (.done (found || rs.any (matchesRecord F tag incoming page q)))
          (queryBank xs q ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩) (advance pos (NormalizedBatch.inputBatch rs).length)).denote
          (nativeEncoding F small) (program F small tag incoming page) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=batch_trace F small tag incoming page found xs q hq hp rs hw pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F small) (program F small tag incoming page) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F small) (program F small tag incoming page) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k s : ℕ} (encoding : NativeMicrocode.Encoding U J k s)
    (F : Fin c → RationalMobius) (small : ℕ) (tag : Fin c) (incoming : Bool) (page : Fin (rationalPageCount F))
    (ports : Fin 7 ↪ U) (labels : Label F small → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F small tag incoming page pc≠.halt → program F small tag incoming page pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F small tag incoming page pc))
    (found : Bool) (xs q : List Bool) (hq : q.length=2*xs.length+small) (hp : 0<2*xs.length+small)
    (rs : List (List Bool × List Bool)) (hw : ∀ p ∈ rs,p.1.length=2*xs.length+small ∧ p.2.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ batchBudget small xs rs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F small found)
          (queryBank xs q ⟨pre,NormalizedBatch.inputBatch rs++suffix⟩) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (found || rs.any (matchesRecord F tag incoming page q)))
            (queryBank xs q ⟨(NormalizedBatch.inputBatch rs).reverse++pre,suffix⟩)
            (advance pos (NormalizedBatch.inputBatch rs).length)) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩:=batch_trace F small tag incoming page found xs q hq hp rs hw pre suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F small tag incoming page) target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.PageEventBatch


namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem selected_decodes (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1))
    (a : List Bool × List Bool) (ha : a ∈ FirstWitness.selected F xs tag) :
    ∃ i j : Fin (Counter.value xs),RowEnumeration.decodePair a=(i.val,j.val) ∧ rationalTag F i j=some tag := by
  have hm : RowEnumeration.decodePair a ∈ (FirstWitness.selected F xs tag).map RowEnumeration.decodePair :=
    List.mem_map.mpr ⟨a,ha,rfl⟩
  have ho:=((FirstWitness.selected_spec F xs tag _).mp hm).1
  obtain ⟨i,j,_,he⟩:=(RawNormalization.normalized_records_spec F xs tag _).mp ho
  exact ⟨i,j,he,(FirstWitness.selected_tag_spec F xs tag i j).mp (he ▸ hm)⟩

theorem selected_any_iff (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1))
    (incoming : Bool) (page : Fin (rationalPageCount F)) (q : List Bool) :
    (FirstWitness.selected F xs tag).any (matchesRecord F tag incoming page q)=true ↔
      ∃ i j : Fin (Counter.value xs),rationalTag F i j=some tag ∧ rationalColor F i j=some page ∧
        BinaryCompare.value q=(if incoming then j else i).val := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩,hsel,hhit⟩
    obtain ⟨i,j,he,htag⟩:=selected_decodes F xs tag (a,b) hsel
    have ha : BinaryCompare.value a=i.val := congrArg Prod.fst he
    have hb : BinaryCompare.value b=j.val := congrArg Prod.snd he
    exact ⟨i,j,htag,(PageRecordTest.hit_selected F xs tag incoming page q a b i j ha hb hsel).mp hhit⟩
  · rintro ⟨i,j,htag,hcolor,hq⟩
    obtain ⟨⟨a,b⟩,hsel,he⟩:=List.mem_map.mp ((FirstWitness.selected_tag_spec F xs tag i j).mpr htag)
    have ha : BinaryCompare.value a=i.val := congrArg Prod.fst he
    have hb : BinaryCompare.value b=j.val := congrArg Prod.snd he
    exact ⟨(a,b),hsel,(PageRecordTest.hit_selected F xs tag incoming page q a b i j ha hb hsel).mpr ⟨hcolor,hq⟩⟩

theorem selected_count (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    (FirstWitness.selected F xs tag).length≤Counter.value xs*((F tag).distortion+1) := by
  have hf:=List.length_filter_le (fun p => !FilteredBatch.found (FirstWitness.earlierBatches F xs tag) p)
    ((FamilyNormalization.records F xs tag).map (FilteredBatch.paddedPair (FamilyNormalization.padding F tag)))
  rw [List.length_map] at hf
  exact hf.trans (FamilyNormalization.sparse_rows_count (F tag) xs (Counter.value xs) 0)

theorem selected_batch_trace (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1))
    (incoming : Bool) (page : Fin (rationalPageCount F)) (found : Bool) (q : List Bool)
    (hq : q.length=2*xs.length+FamilyNormalization.common F)
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ batchBudget (FamilyNormalization.common F) xs (FirstWitness.selected F xs tag),
      Trace F (FamilyNormalization.common F) tag incoming page t
        (cfg (start F (FamilyNormalization.common F) found)
          (queryBank xs q ⟨pre,NormalizedBatch.inputBatch (FirstWitness.selected F xs tag)++suffix⟩) pos)
        (cfg (.done (found || (FirstWitness.selected F xs tag).any (matchesRecord F tag incoming page q)))
          (queryBank xs q ⟨(NormalizedBatch.inputBatch (FirstWitness.selected F xs tag)).reverse++pre,suffix⟩)
          (advance pos (NormalizedBatch.inputBatch (FirstWitness.selected F xs tag)).length)) := by
  have hp : 0<2*xs.length+FamilyNormalization.common F := by
    have h:=(RowEnumeration.common_positive (F tag) xs)
    rw [PaddedWord.word_length] at h
    have hc:=FamilyNormalization.le_common F tag
    omega
  exact batch_trace F (FamilyNormalization.common F) tag incoming page found xs q hq hp
    (FirstWitness.selected F xs tag) (by intro p hp;exact NativeResidueColor.selected_width F xs tag p.1 p.2 hp) pre suffix pos

theorem selected_budget_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) (tag : Fin (r+1)) :
    batchBudget (FamilyNormalization.common F) xs (FirstWitness.selected F xs tag)≤
      (Counter.value xs*((F tag).distortion+1)+1)*(90*xs.length+42*FamilyNormalization.common F+92) := by
  exact (batch_budget_le _ _ _).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (selected_count F xs tag) 1))

end TransposeFollowup.PageEventBatch


/-! A page already determines its unique canonical map tag. Thus one
specified batch suffices for the event query;other batches need only be
physically skipped,not parsed and tested. -/
namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def pageTag {c : ℕ} (F : Fin c → RationalMobius) (page : Fin (rationalPageCount F)) : Fin c :=
  (finProdFinEquiv.symm page : Fin c × Fin ((rationalFamilyBound F+1)*(rationalFamilyBound F+1))).1

theorem residue_tag {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) (tag : Fin c) :
    pageTag F (rationalResidueColor F i j tag)=tag := by
  unfold pageTag rationalResidueColor
  rw [Equiv.symm_apply_apply]

theorem color_tag {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) (page : Fin (rationalPageCount F))
    (h : rationalColor F i j=some page) : rationalTag F i j=some (pageTag F page) := by
  cases ht : rationalTag F i j with
  | none => simp [rationalColor,ht] at h
  | some tag =>
    have hp : rationalResidueColor F i j tag=page := by simpa [rationalColor,ht] using h
    have he : pageTag F page=tag := by rw [← hp];exact residue_tag F i j tag
    rw [he]

theorem outgoing_iff_color {c n : ℕ} (F : Fin c → RationalMobius) (i : Fin n) (page : Fin (rationalPageCount F)) :
    rationalOutgoingOn F i page=true ↔ ∃ j : Fin n,rationalColor F i j=some page := by
  unfold rationalOutgoingOn
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨j,hj⟩;exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  · rintro ⟨j,hc⟩
    obtain ⟨he,_⟩:=(rationalColor_some_iff F i j page).mp hc
    exact ⟨j,Finset.mem_filter.mpr ⟨(mem_rationalFamilyNeighbors F i j).mpr ((mem_overlapEdges _ _).mp he),hc⟩⟩

theorem incoming_iff_color {c n : ℕ} (F : Fin c → RationalMobius) (j : Fin n) (page : Fin (rationalPageCount F)) :
    rationalIncomingOn F j page=true ↔ ∃ i : Fin n,rationalColor F i j=some page := by
  unfold rationalIncomingOn
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi⟩;exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i,hc⟩
    obtain ⟨he,_⟩:=(rationalColor_some_iff F i j page).mp hc
    exact ⟨i,Finset.mem_filter.mpr ⟨(mem_rationalFamilyIncoming F i j).mpr ((mem_overlapEdges _ _).mp he),hc⟩⟩

theorem selected_outgoing {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs q : List Bool)
    (i : Fin (Counter.value xs)) (hq : BinaryCompare.value q=i.val) (page : Fin (rationalPageCount F)) :
    (FirstWitness.selected F xs (pageTag F page)).any (matchesRecord F (pageTag F page) false page q)=true ↔
      rationalOutgoingOn F i page=true := by
  rw [selected_any_iff,outgoing_iff_color]
  constructor
  · rintro ⟨u,v,_,hc,hv⟩
    have hu : u=i := Fin.ext (by simpa only [Bool.false_eq_true,ite_false,hq] using hv.symm)
    subst u
    exact ⟨v,hc⟩
  · rintro ⟨j,hc⟩
    exact ⟨i,j,color_tag F i j page hc,hc,hq⟩

theorem selected_incoming {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs q : List Bool)
    (j : Fin (Counter.value xs)) (hq : BinaryCompare.value q=j.val) (page : Fin (rationalPageCount F)) :
    (FirstWitness.selected F xs (pageTag F page)).any (matchesRecord F (pageTag F page) true page q)=true ↔
      rationalIncomingOn F j page=true := by
  rw [selected_any_iff,incoming_iff_color]
  constructor
  · rintro ⟨u,v,_,hc,hv⟩
    have he : v=j := Fin.ext (by simpa only [ite_true,hq] using hv.symm)
    subst v
    exact ⟨u,hc⟩
  · rintro ⟨i,hc⟩
    exact ⟨i,j,color_tag F i j page hc,hc,hq⟩

end TransposeFollowup.PageEventBatch


namespace TransposeFollowup.PageEventBatch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def event (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (page : Fin (rationalPageCount F)) : Bool :=
  if incoming then rationalIncomingOn F v page else rationalOutgoingOn F v page

theorem result_eq (F : Fin (r+1) → RationalMobius) (xs q : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val) (page : Fin (rationalPageCount F)) :
    (FirstWitness.selected F xs (pageTag F page)).any (matchesRecord F (pageTag F page) incoming page q)=
      event F xs incoming v page := by
  have h : (FirstWitness.selected F xs (pageTag F page)).any (matchesRecord F (pageTag F page) incoming page q)=true ↔
      event F xs incoming v page=true := by
    cases incoming
    · exact selected_outgoing F xs q v hq page
    · exact selected_incoming F xs q v hq page
  cases ha : (FirstWitness.selected F xs (pageTag F page)).any (matchesRecord F (pageTag F page) incoming page q) <;>
    cases hb : event F xs incoming v page <;> simp_all

theorem canonical_trace (F : Fin (r+1) → RationalMobius) (xs q : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (page : Fin (rationalPageCount F))
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) :
    ∃ t ≤ (Counter.value xs*((F (pageTag F page)).distortion+1)+1)*(90*xs.length+42*FamilyNormalization.common F+92),
      Trace F (FamilyNormalization.common F) (pageTag F page) incoming page t
        (cfg (start F (FamilyNormalization.common F) false)
          (queryBank xs q ⟨pre,NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))++suffix⟩) pos)
        (cfg (.done (event F xs incoming v page))
          (queryBank xs q ⟨(NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))).reverse++pre,suffix⟩)
          (advance pos (NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))).length)) := by
  obtain ⟨t,ht,htr⟩:=selected_batch_trace F xs (pageTag F page) incoming page false q hw pre suffix pos
  exact ⟨t,ht.trans (selected_budget_le F xs (pageTag F page)),by simpa only [Bool.false_or,result_eq F xs q incoming v hq page] using htr⟩

theorem native_canonical (F : Fin (r+1) → RationalMobius) (xs q : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (hq : BinaryCompare.value q=v.val)
    (hw : q.length=2*xs.length+FamilyNormalization.common F) (page : Fin (rationalPageCount F))
    (pre suffix : List (Sym Bool)) (pos : Fin 7 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ (Counter.value xs*((F (pageTag F page)).distortion+1)+1)*(90*xs.length+42*FamilyNormalization.common F+92),
      Transpose.stepN (nativeMachine F (FamilyNormalization.common F) (pageTag F page) incoming page) input t
        ((cfg (start F (FamilyNormalization.common F) false)
          (queryBank xs q ⟨pre,NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))++suffix⟩) pos).denote
          (nativeEncoding F (FamilyNormalization.common F)) (program F (FamilyNormalization.common F) (pageTag F page) incoming page) ip outRev)=
        some ((cfg (.done (event F xs incoming v page))
          (queryBank xs q ⟨(NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))).reverse++pre,suffix⟩)
          (advance pos (NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))).length)).denote
          (nativeEncoding F (FamilyNormalization.common F)) (program F (FamilyNormalization.common F) (pageTag F page) incoming page) ip outRev) ∧
      Transpose.step (nativeMachine F (FamilyNormalization.common F) (pageTag F page) incoming page) input
        ((cfg (.done (event F xs incoming v page))
          (queryBank xs q ⟨(NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))).reverse++pre,suffix⟩)
          (advance pos (NormalizedBatch.inputBatch (FirstWitness.selected F xs (pageTag F page))).length)).denote
          (nativeEncoding F (FamilyNormalization.common F)) (program F (FamilyNormalization.common F) (pageTag F page) incoming page) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=canonical_trace F xs q incoming v hq hw page pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F (FamilyNormalization.common F))
    (program F (FamilyNormalization.common F) (pageTag F page) incoming page) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F (FamilyNormalization.common F))
    (program F (FamilyNormalization.common F) (pageTag F page) incoming page) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem event_opcode (F : Fin (r+1) → RationalMobius) (xs : List Bool) (incoming : Bool)
    (v : Fin (Counter.value xs)) (page : Fin (rationalPageCount F)) :
    rationalPageOpcode F (if incoming then OrderedBipartite.right v else OrderedBipartite.left v) page=
      if event F xs incoming v page then (if incoming then PageOpcode.closeEdge else PageOpcode.openEdge) else PageOpcode.idle := by
  cases incoming
  · exact rationalPageOpcode_left F v page
  · exact rationalPageOpcode_right F v page

end TransposeFollowup.PageEventBatch
