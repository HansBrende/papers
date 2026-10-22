import TransposeFollowup.InPlaceAdd

/-! A fixed multiplier is compiled into finitely many call labels. No
runtime integer or unpaid coefficient/fuel word is hidden in finite control. -/

namespace TransposeFollowup.FixedMultiple

open FixedTapeCompiler
open RepeatedAdd (Port Bank ready)
set_option autoImplicit false

def binding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

inductive Label (K : ℕ)
  | call (remaining : Fin (K+1)) (pc : RepeatedAdd.Label)
  | done
  deriving DecidableEq, Fintype

def start (K : ℕ) : Label K := .call ⟨K, Nat.lt_succ_self K⟩ (.counter 0)

def program (K : ℕ) : Microcode.Program Port (Label K)
  | .call i pc => if h : i.val = 0 then .jump .done
      else if pc = .counter 12 then
        .jump (.call ⟨i.val-1, by omega⟩ (.counter 0))
      else binding.instruction (Label.call i) (RepeatedAdd.program pc)
  | .done => .halt

theorem call_code (K : ℕ) (i : Fin (K+1)) (hi : 0 < i.val) (pc : RepeatedAdd.Label)
    (hh : RepeatedAdd.program pc ≠ .halt) (_ : RepeatedAdd.program pc ≠ .reject) :
    program K (.call i pc) = MicrocodeEmbedding.instruction binding.ports
      (Label.call i) (RepeatedAdd.program pc) := by
  have hp : pc ≠ .counter 12 := by intro h; subst pc; exact hh rfl
  simp [program, Nat.ne_of_gt hi, hp, FinitePortBinding.instruction_eq]

def cfg {K : ℕ} (pc : Label K) (b : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label K) :=
  ⟨⟨pc, fun t => (b.tapes t).denote⟩, pos⟩
def zipperCfg {K : ℕ} (pc : Label K) (b : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label K) :=
  ⟨⟨pc, b.tapes⟩, pos⟩

def labelEquiv (K : ℕ) : Label K ≃ (Fin (K+1) × RepeatedAdd.Label) ⊕ Unit where
  toFun | .call i pc => .inl (i,pc) | .done => .inr ()
  invFun | .inl (i,pc) => .call i pc | .inr () => .done
  left_inv := by intro p; cases p <;> rfl
  right_inv := by rintro (⟨i,pc⟩ | ⟨⟩) <;> rfl

theorem label_card (K : ℕ) : Fintype.card (Label K) = 99*(K+1)+1 := by
  have h := Fintype.card_congr (labelEquiv K)
  have hr : Fintype.card RepeatedAdd.Label = 99 := by decide +kernel
  simpa [hr, Nat.mul_comm] using h

noncomputable def nativeEncoding (K : ℕ) := NativeMicrocode.initialEncoding (T := Port) (start K)
noncomputable def nativeMachine (K : ℕ) := NativeMicrocode.machine (nativeEncoding K) (program K)

theorem fixed_resources (K : ℕ) : (nativeMachine K).k = 5 ∧
    (nativeMachine K).g+1 = 5 ∧ (nativeMachine K).q+1 = 99*(K+1)+1 ∧
    (nativeEncoding K).label (start K) = 0 := by
  refine ⟨?_, rfl, ?_, NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port = 5
    decide +kernel
  · change Fintype.card (Label K)-1+1 = 99*(K+1)+1
    rw [label_card]
    omega

end TransposeFollowup.FixedMultiple
