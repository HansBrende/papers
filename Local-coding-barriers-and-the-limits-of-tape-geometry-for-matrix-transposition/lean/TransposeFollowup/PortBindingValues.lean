import TransposeFollowup.FinitePortBinding

namespace TransposeFollowup.FinitePortBinding
set_option autoImplicit false

theorem map_values {T U A B : Type*} (b : FinitePortBinding T U) (f : A → B) (g : T → A) (fallback : U → A) :
    b.values (fun t => f (g t)) (fun u => f (fallback u))=fun u => f (b.values g fallback u) := by
  funext u
  unfold values
  cases b.decode u <;> rfl

end TransposeFollowup.FinitePortBinding
