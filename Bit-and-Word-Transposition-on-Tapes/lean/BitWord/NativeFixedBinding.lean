import TransposeFollowup.PortBindingFrame

/-! A fixed injection of finite control ports determines a static decoder table.
The construction is independent of every runtime input and dimension. -/
namespace BitWord
open TransposeFollowup
set_option autoImplicit false
variable {T U : Type*}
noncomputable def fixedBinding (e : T ↪ U) : FinitePortBinding T U where
  ports := e
  decode := by
    classical
    exact fun u => if h : ∃ t,e t=u then some h.choose else none
  decode_spec := by
    classical
    intro u t
    by_cases h : ∃ a,e a=u
    · simp only [h,↓reduceDIte,Option.some.injEq]
      constructor
      · rintro rfl; exact h.choose_spec
      · intro ht; exact e.injective (h.choose_spec.trans ht.symm)
    · simp only [h,↓reduceDIte,reduceCtorEq,false_iff]
      exact fun ht => h ⟨t,ht⟩
@[simp] theorem fixedBinding_ports (e : T ↪ U) : (fixedBinding e).ports=e := rfl
@[simp] theorem fixedBinding_values_at {A : Type*} (e : T ↪ U) (a : T → A) (b : U → A) (i : T) :
    (fixedBinding e).values a b (e i)=a i := (fixedBinding e).values_at a b i

theorem fixedBinding_values_outside {A : Type*} (e : T ↪ U) (a : T → A) (b : U → A) (u : U)
    (h : ¬∃ i,e i=u) : (fixedBinding e).values a b u=b u := by
  rw [(fixedBinding e).values_eq_extend, fixedBinding_ports,
    MicrocodeEmbedding.extend_outside e u h]
end BitWord
