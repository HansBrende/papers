import TransposeFollowup.MicrocodeEmbedding

/-! Executable fixed wiring for a finite caller. The decoder is a static
port table, not a tape address computed at runtime. -/

namespace TransposeFollowup

open FixedTapeCompiler
set_option autoImplicit false
variable {T U L J A : Type*}

structure FinitePortBinding (T U : Type*) where
  ports : T ↪ U
  decode : U → Option T
  decode_spec : ∀ u t, decode u = some t ↔ ports t = u

namespace FinitePortBinding

def values (b : FinitePortBinding T U) (g : T → A) (fallback : U → A) : U → A :=
  fun u => match b.decode u with | some t => g t | none => fallback u

theorem values_eq_extend (b : FinitePortBinding T U) (g : T → A) (fallback : U → A) :
    b.values g fallback = Function.extend b.ports g fallback := by
  funext u
  cases h : b.decode u with
  | some t =>
    have hu : b.ports t = u := (b.decode_spec u t).mp h
    rw [values, h, ← hu, MicrocodeEmbedding.extend_at]
  | none =>
    have hu : ¬∃ t, b.ports t = u := by
      rintro ⟨t, ht⟩
      have := (b.decode_spec u t).mpr ht
      simp [h] at this
    rw [values, h, MicrocodeEmbedding.extend_outside b.ports u hu]

def instruction (b : FinitePortBinding T U) (labels : L → J) :
    Microcode.Instruction T L → Microcode.Instruction U J
  | .read t next => .read (b.ports t) (labels ∘ next)
  | .act acts next => .act (b.values acts (fun _ => MicrocodeEmbedding.idle)) (labels next)
  | .jump next => .jump (labels next)
  | .halt => .halt
  | .reject => .reject

theorem instruction_eq (b : FinitePortBinding T U) (labels : L → J)
    (i : Microcode.Instruction T L) :
    b.instruction labels i = MicrocodeEmbedding.instruction b.ports labels i := by
  cases i <;> simp only [instruction, MicrocodeEmbedding.instruction, values_eq_extend]

end FinitePortBinding
end TransposeFollowup
