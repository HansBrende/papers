import TransposeFollowup.NativeErase
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.FinitePortBinding

/-! A fixed finite list of physical erasures. The list is part of the
machine, while each erased word and its length may vary with the input.
Unlisted tapes and all absolute head positions are preserved. -/
namespace TransposeFollowup.NativeBatchErase
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {T : Type*} [DecidableEq T] {r : ℕ}

inductive Label (r : ℕ) | erase (j : Fin r) (pc : NativeErase.Label) | done
  deriving DecidableEq, Fintype

def entry (r k : ℕ) : Label r := if h : k<r then .erase ⟨k,h⟩ 2 else .done

def binding (ports : Fin r ↪ T) (j : Fin r) : FinitePortBinding (Fin 1) T where
  ports := ⟨fun _ => ports j,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun t => if t=ports j then some 0 else none
  decode_spec := by
    intro t q
    change (if t=ports j then some (0 : Fin 1) else none)=some q ↔ ports j=t
    fin_cases q
    simp [eq_comm]

def program (ports : Fin r ↪ T) : Microcode.Program T (Label r)
  | .erase j pc => if pc=0 then .jump (entry r (j.val+1)) else
      (binding ports j).instruction (Label.erase j) (NativeErase.program pc)
  | .done => .halt

theorem erase_code (ports : Fin r ↪ T) (j : Fin r) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program ports (.erase j pc)=MicrocodeEmbedding.instruction (binding ports j).ports
      (Label.erase j) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg (pc : Label r) (s : T → Tape Bool) (pos : T → ℤ) : NativeMicrocode.Config T (Label r) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def zipperCfg (pc : Label r) (s : T → Tape Bool) (pos : T → ℤ) : NativeZipper.Config T (Label r) :=
  ⟨⟨pc,s⟩,pos⟩
def frame (s : T → Tape Bool) (pos : T → ℤ) : MicrocodeEmbedding.Frame T :=
  ⟨fun p => (s p).denote,pos⟩

def stage (ports : Fin r ↪ T) (s : T → Tape Bool) (k : ℕ) : T → Tape Bool :=
  fun t => if ∃ j : Fin r,j.val<k ∧ ports j=t then ⟨[],[]⟩ else s t

@[simp] theorem stage_zero (ports : Fin r ↪ T) (s : T → Tape Bool) : stage ports s 0=s := by
  funext t
  simp only [stage,Nat.not_lt_zero,false_and,exists_false,ite_false]

theorem stage_future (ports : Fin r ↪ T) (s : T → Tape Bool) (k : ℕ) (j : Fin r)
    (hj : k ≤ j.val) : stage ports s k (ports j)=s (ports j) := by
  have hn : ¬∃ i : Fin r,i.val<k ∧ ports i=ports j := by
    rintro ⟨i,hi,hij⟩
    have := ports.injective hij
    subst i
    omega
  simp only [stage,hn,ite_false]

theorem stage_step (ports : Fin r ↪ T) (s : T → Tape Bool) (j : Fin r) :
    Function.update (stage ports s j.val) (ports j) ⟨[],[]⟩=stage ports s (j.val+1) := by
  funext t
  by_cases ht : t=ports j
  · subst t
    have hh : ∃ i : Fin r,i.val<j.val+1 ∧ ports i=ports j := ⟨j,by omega,rfl⟩
    simp only [Function.update_self,stage,hh,ite_true]
  · have he : (∃ i : Fin r,i.val<j.val+1 ∧ ports i=t) ↔ ∃ i : Fin r,i.val<j.val ∧ ports i=t := by
      constructor
      · rintro ⟨i,hi,hit⟩
        have hne : i.val≠j.val := by
          intro hij
          have : i=j := Fin.ext hij
          subst i
          exact ht hit.symm
        exact ⟨i,by omega,hit⟩
      · rintro ⟨i,hi,hit⟩
        exact ⟨i,by omega,hit⟩
    simp only [Function.update_of_ne ht,stage,he]

theorem final_at (ports : Fin r ↪ T) (s : T → Tape Bool) (j : Fin r) :
    stage ports s r (ports j)=⟨[],[]⟩ := by
  simp only [stage,ite_eq_left_iff]
  intro hn
  exact False.elim (hn ⟨j,j.isLt,rfl⟩)

theorem stage_outside (ports : Fin r ↪ T) (s : T → Tape Bool) (k : ℕ) (t : T)
    (ht : ¬∃ j,ports j=t) : stage ports s k t=s t := by
  have hn : ¬∃ j : Fin r,j.val<k ∧ ports j=t := by rintro ⟨j,_,hj⟩; exact ht ⟨j,hj⟩
  simp only [stage,hn,ite_false]

theorem embed_erase (ports : Fin r ↪ T) (j : Fin r) (pc : NativeErase.Label)
    (w : Tape Bool) (s : T → Tape Bool) (pos : T → ℤ) :
    MicrocodeEmbedding.embed (binding ports j).ports (Label.erase j)
      (NativeErase.cfg pc w (fun _ => pos (ports j))).denote (frame s pos)=
      cfg (.erase j pc) (Function.update s (ports j) w) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (binding ports j).values_eq_extend]
  congr 2 <;> funext t <;> by_cases ht : t=ports j
  all_goals simp [binding,FinitePortBinding.values,Function.update,ht]

abbrev Trace (ports : Fin r ↪ T) :=
  OperationalTrace.Trace (NativeMicrocode.step (program ports)) (NativeMicrocode.Active (program ports))

theorem erase_call (ports : Fin r ↪ T) (j : Fin r) (xs : List Bool)
    (s : T → Tape Bool) (hs : s (ports j)=Counter.marked xs) (pos : T → ℤ) :
    ∃ t ≤ 4*xs.length+4, Trace ports t (cfg (.erase j 2) s pos)
      (cfg (.erase j 0) (Function.update s (ports j) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos (ports j))
  have he := MicrocodeEmbedding.trace_embed (binding ports j).ports (Label.erase j)
    NativeErase.program (program ports) (frame s pos) (erase_code ports j) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Function.update_eq_self] using he⟩

theorem jump_trace (ports : Fin r ↪ T) (j : Fin r) (s : T → Tape Bool) (pos : T → ℤ) :
    Trace ports 1 (cfg (.erase j 0) s pos) (cfg (entry r (j.val+1)) s pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · change Trace ports 0 (NativeMicrocode.step (program ports) (cfg (.erase j 0) s pos)) _
    have he : NativeMicrocode.step (program ports) (cfg (.erase j 0) s pos)=cfg (entry r (j.val+1)) s pos := by
      simp [NativeMicrocode.step,Microcode.actualStep,cfg,program]
    rw [he]
    exact .refl _

def budgetFrom (words : Fin r → List Bool) (k : ℕ) : ℕ :=
  ∑ j : Fin r,if k ≤ j.val then 4*(words j).length+5 else 0

theorem budgetFrom_end (words : Fin r → List Bool) : budgetFrom words r=0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp [show ¬r ≤ j.val by omega]

theorem budgetFrom_step (words : Fin r → List Bool) (j : Fin r) :
    budgetFrom words j.val=4*(words j).length+5+budgetFrom words (j.val+1) := by
  have he : ∀ i : Fin r,(if j.val ≤ i.val then 4*(words i).length+5 else 0)=
      (if i=j then 4*(words j).length+5 else 0)+(if j.val+1 ≤ i.val then 4*(words i).length+5 else 0) := by
    intro i
    by_cases h : i=j
    · subst i; simp
    · have hv : i.val≠j.val := by intro hi; exact h (Fin.ext hi)
      by_cases hi : j.val ≤ i.val <;> simp [h,hi,show (j.val+1 ≤ i.val) ↔ (j.val ≤ i.val) by omega]
  unfold budgetFrom
  simp only [he,Finset.sum_add_distrib]
  simp

theorem complete_from (ports : Fin r ↪ T) (words : Fin r → List Bool) (s : T → Tape Bool)
    (hs : ∀ j,s (ports j)=Counter.marked (words j)) (pos : T → ℤ) (k : ℕ) (hk : k ≤ r) :
    ∃ t ≤ budgetFrom words k, Trace ports t (cfg (entry r k) (stage ports s k) pos)
      (cfg .done (stage ports s r) pos) := by
  induction h : r-k generalizing k with
  | zero =>
    have he : k=r := by omega
    subst k
    refine ⟨0,by simp [budgetFrom_end],?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte]
    exact .refl _
  | succ d ih =>
    have hkr : k<r := by omega
    let j : Fin r := ⟨k,hkr⟩
    have hw : stage ports s k (ports j)=Counter.marked (words j) :=
      (stage_future ports s k j (by rfl)).trans (hs j)
    obtain ⟨a,ha,ta⟩ := erase_call ports j (words j) (stage ports s k) hw pos
    have tj := jump_trace ports j (stage ports s (k+1)) pos
    have hstep : Function.update (stage ports s k) (ports j) ⟨[],[]⟩=stage ports s (k+1) := stage_step ports s j
    rw [hstep] at ta
    obtain ⟨b,hb,tb⟩ := ih (k+1) (by omega) (by omega)
    refine ⟨a+1+b,?_,?_⟩
    · have hbnd := budgetFrom_step words j
      change budgetFrom words k=4*(words j).length+5+budgetFrom words (k+1) at hbnd
      omega
    · have he : entry r k=.erase j 2 := by simp [entry,hkr,j]
      rw [he]
      exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb

theorem complete_trace (ports : Fin r ↪ T) (words : Fin r → List Bool) (s : T → Tape Bool)
    (hs : ∀ j,s (ports j)=Counter.marked (words j)) (pos : T → ℤ) :
    ∃ t ≤ ∑ j : Fin r,(4*(words j).length+5), Trace ports t
      (cfg (entry r 0) s pos) (cfg .done (stage ports s r) pos) := by
  simpa only [budgetFrom,Nat.zero_le,ite_true,stage_zero] using complete_from ports words s hs pos 0 (by omega)

theorem common_width_trace (ports : Fin r ↪ T) (words : Fin r → List Bool) (m : ℕ)
    (hw : ∀ j,(words j).length=m) (s : T → Tape Bool)
    (hs : ∀ j,s (ports j)=Counter.marked (words j)) (pos : T → ℤ) :
    ∃ t ≤ r*(4*m+5), Trace ports t (cfg (entry r 0) s pos) (cfg .done (stage ports s r) pos) := by
  simpa only [hw,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
    complete_trace ports words s hs pos

noncomputable def nativeEncoding [Fintype T] := NativeMicrocode.initialEncoding (T := T) (entry r 0)
noncomputable def nativeMachine [Fintype T] (ports : Fin r ↪ T) :=
  NativeMicrocode.machine (nativeEncoding (T := T) (r := r)) (program ports)

def labelEquiv (r : ℕ) : Label r ≃ (Fin r × NativeErase.Label) ⊕ Unit where
  toFun | .erase j pc => .inl (j,pc) | .done => .inr ()
  invFun | .inl (j,pc) => .erase j pc | .inr _ => .done
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (⟨j,pc⟩ | ⟨⟩) <;> rfl

theorem fixed_resources [Fintype T] (ports : Fin r ↪ T) :
    (nativeMachine ports).k=Fintype.card T ∧ (nativeMachine ports).g+1=5 ∧
    (nativeMachine ports).q+1=8*r+1 ∧ (nativeEncoding (T := T) (r := r)).label (entry r 0)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label r)-1+1=_
  rw [Fintype.card_congr (labelEquiv r)]
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,he]
  omega

theorem native_complete [Fintype T] (ports : Fin r ↪ T) (words : Fin r → List Bool)
    (s : T → Tape Bool) (hs : ∀ j,s (ports j)=Counter.marked (words j)) (pos : T → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ ∑ j : Fin r,(4*(words j).length+5),
      Transpose.stepN (nativeMachine ports) input t
        ((cfg (entry r 0) s pos).denote nativeEncoding (program ports) inputPos outRev)=
        some ((cfg .done (stage ports s r) pos).denote nativeEncoding (program ports) inputPos outRev) ∧
      Transpose.step (nativeMachine ports) input
        ((cfg .done (stage ports s r) pos).denote nativeEncoding (program ports) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace ports words s hs pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding (program ports) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding (program ports) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (ports : Fin r ↪ T)
    (encoding : NativeMicrocode.Encoding U J k q) (outerPorts : T ↪ U) (labels : Label r → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program ports pc≠.halt → program ports pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction outerPorts labels (program ports pc))
    (words : Fin r → List Bool) (s : T → Tape Bool)
    (hs : ∀ j,s (ports j)=Counter.marked (words j)) (pos : T → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ ∑ j : Fin r,(4*(words j).length+5),
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed outerPorts labels (cfg (entry r 0) s pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed outerPorts labels (cfg .done (stage ports s r) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace ports words s hs pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding outerPorts labels (program ports) target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeBatchErase
