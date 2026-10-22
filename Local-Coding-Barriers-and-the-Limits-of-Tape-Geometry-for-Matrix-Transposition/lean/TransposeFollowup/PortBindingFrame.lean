import TransposeFollowup.PortBindingValues

namespace TransposeFollowup.FinitePortBinding
set_option autoImplicit false
variable {T U A : Type*}

theorem values_at (b : FinitePortBinding T U) (g : T → A) (fallback : U → A) (t : T) :
    b.values g fallback (b.ports t)=g t := by
  rw [values_eq_extend,MicrocodeEmbedding.extend_at]

theorem values_overwrite (b : FinitePortBinding T U) (g h : T → A) (fallback : U → A) :
    b.values g (b.values h fallback)=b.values g fallback := by
  funext u
  unfold values
  cases b.decode u <;> rfl

theorem values_project (b : FinitePortBinding T U) (f : U → A) :
    b.values (fun t => f (b.ports t)) f=f := by
  funext u
  cases h : b.decode u with
  | none => simp only [values,h]
  | some t =>
    have he:=(b.decode_spec u t).mp h
    simp only [values,h,he]

theorem values_update [DecidableEq T] [DecidableEq U] (b : FinitePortBinding T U) (g : T → A) (fallback : U → A)
    (t : T) (a : A) :
    Function.update (b.values g fallback) (b.ports t) a=b.values (Function.update g t a) fallback := by
  funext u
  by_cases hu : u=b.ports t
  · subst u;rw [Function.update_self,values_at,Function.update_self]
  · rw [Function.update_of_ne hu]
    cases h : b.decode u with
    | none => simp only [values,h]
    | some j =>
      have hj : j≠t := by
        intro he;subst j
        exact hu ((b.decode_spec u t).mp h).symm
      simp only [values,h,Function.update_of_ne hj]

/-- Arbitrary fixed wiring transports the bank and preserves the caller's heads. -/
theorem embed_bank_project {L J : Type*} (b : FinitePortBinding T U) (labels : L → J)
    (pc : L) (inner : T → FixedTapeCompiler.CopyMachine.Tape Bool)
    (outer : U → FixedTapeCompiler.CopyMachine.Tape Bool) (pos : U → ℤ) :
    MicrocodeEmbedding.embed b.ports labels
      (⟨⟨pc,fun t => (inner t).denote⟩,fun t => pos (b.ports t)⟩ : NativeMicrocode.Config T L)
      ⟨fun u => (outer u).denote,pos⟩ =
      ⟨⟨labels pc,fun u => (b.values inner outer u).denote⟩,pos⟩ := by
  simp only [MicrocodeEmbedding.embed,← values_eq_extend,map_values,values_project]

end TransposeFollowup.FinitePortBinding
