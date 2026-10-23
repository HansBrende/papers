import TransposeFollowup.NativeExpanderShearFrames
import TransposeFollowup.NativeCountedLoop

/-! Shared frame-preserving call rules for literal fixed-port microprograms. -/
namespace BitWord.NativeBankCalls
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames

variable {U L J : Type*} [DecidableEq U]

def singleBinding (t : U) : FinitePortBinding (Fin 1) U where
  ports := ⟨fun _ => t,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun u => if u=t then some 0 else none
  decode_spec := by
    intro u i
    change (if u=t then some (0:Fin 1) else none) = some i ↔ t=u
    fin_cases i
    by_cases h : u=t
    · subst u; simp
    · simp [h,Ne.symm h]

theorem single_values {A : Type*} (t : U) (a : A) (s : U → A) :
    (singleBinding t).values (fun _ => a) s = Function.update s t a := by
  funext u
  by_cases h : u=t <;> simp [singleBinding,FinitePortBinding.values,h]

def pairBinding (s t : U) (hne : s ≠ t) : FinitePortBinding (Fin 2) U where
  ports := ⟨![s,t],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
  decode := fun u => if u=s then some 0 else if u=t then some 1 else none
  decode_spec := by
    intro u i
    change (if u=s then some (0:Fin 2) else if u=t then some 1 else none) = some i ↔
      (![s,t] : Fin 2 → U) i = u
    fin_cases i <;> by_cases hs : u=s <;> by_cases ht : u=t <;> simp_all [eq_comm]

theorem pair_values {A : Type*} (a b : U) (hne : a ≠ b) (x y : A) (s : U → A) :
    (pairBinding a b hne).values ![x,y] s = Function.update (Function.update s a x) b y := by
  funext u
  by_cases hub : u=b
  · subst u
    simp [pairBinding,FinitePortBinding.values,Ne.symm hne]
  · by_cases hua : u=a
    · subst u
      simp [pairBinding,FinitePortBinding.values,hne]
    · simp [pairBinding,FinitePortBinding.values,hua,hub]

@[simp] theorem fin_one_update {A : Type*} (s : Fin 1 → A) (a : A) :
    Function.update s 0 a = fun _ => a := by funext i; fin_cases i; rfl

@[simp] theorem fin_two_update {A : Type*} (s : Fin 2 → A) (a b : A) :
    Function.update (Function.update s 0 a) 1 b = ![a,b] := by
  funext i; fin_cases i <;> rfl

/-- Lift a checked one-port trace while retaining the caller's other tapes. -/
theorem call_single (t : U) (labels : L → J) (sub : Microcode.Program (Fin 1) L)
    (prog : Microcode.Program U J)
    (hcode : ∀ pc, sub pc ≠ .halt → sub pc ≠ .reject →
      prog (labels pc) = MicrocodeEmbedding.instruction (singleBinding t).ports labels (sub pc))
    (pc qc : L) (bank : U → Tape Bool) (pos : U → ℤ) (out : Tape Bool) (endPos : ℤ) (n : ℕ)
    (htrace : OperationalTrace.Trace (NativeMicrocode.step sub) (NativeMicrocode.Active sub) n
      (workCfg pc (fun _ => bank t) (fun _ => pos t))
      (workCfg qc (fun _ => out) (fun _ => endPos))) :
    OperationalTrace.Trace (NativeMicrocode.step prog) (NativeMicrocode.Active prog) n
      (workCfg (labels pc) bank pos)
      (workCfg (labels qc) (Function.update bank t out) (Function.update pos t endPos)) := by
  have hh := MicrocodeEmbedding.trace_embed (singleBinding t).ports labels sub prog
    (frame bank pos) hcode htrace
  rw [embed_work,embed_work,single_values,single_values,single_values,single_values] at hh
  simpa only [Function.update_eq_self] using hh

/-- Lift a checked two-port trace with arbitrary distinct fixed ports. -/
theorem call_pair (a b : U) (hne : a ≠ b) (labels : L → J)
    (sub : Microcode.Program (Fin 2) L) (prog : Microcode.Program U J)
    (hcode : ∀ pc, sub pc ≠ .halt → sub pc ≠ .reject →
      prog (labels pc) = MicrocodeEmbedding.instruction (pairBinding a b hne).ports labels (sub pc))
    (pc qc : L) (bank : U → Tape Bool) (pos : U → ℤ)
    (out₁ out₂ : Tape Bool) (end₁ end₂ : ℤ) (n : ℕ)
    (htrace : OperationalTrace.Trace (NativeMicrocode.step sub) (NativeMicrocode.Active sub) n
      (workCfg pc ![bank a,bank b] ![pos a,pos b])
      (workCfg qc ![out₁,out₂] ![end₁,end₂])) :
    OperationalTrace.Trace (NativeMicrocode.step prog) (NativeMicrocode.Active prog) n
      (workCfg (labels pc) bank pos)
      (workCfg (labels qc) (Function.update (Function.update bank a out₁) b out₂)
        (Function.update (Function.update pos a end₁) b end₂)) := by
  have hh := MicrocodeEmbedding.trace_embed (pairBinding a b hne).ports labels sub prog
    (frame bank pos) hcode htrace
  rw [embed_work,embed_work,pair_values,pair_values,pair_values,pair_values] at hh
  simpa only [Function.update_eq_self] using hh

end BitWord.NativeBankCalls
