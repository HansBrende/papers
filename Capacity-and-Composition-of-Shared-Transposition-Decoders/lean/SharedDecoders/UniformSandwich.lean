import SharedDecoders.Model
import Mathlib.Data.Fintype.EquivFin

/-!
# A single nonuniform layer between equivariant maps

This is an exact complete-map theorem over any nontrivial alphabet. Only the
outer map needs injectivity; no finiteness is used in the main proof.
-/

namespace SharedDecoders

variable {d : ℕ} {A κ : Type*} [Nontrivial A]

/-- An exact sandwich with equivariant outer maps forces every receiver class
to be a singleton. The source is the whole matrix space, not a linear code. -/
theorem uniform_sandwich_injective_classes
    {p : ZMod d → κ} {U K V : State d A → State d A}
    (hU : Equivariant U) (hV : Equivariant V)
    (hUi : Function.Injective U) (hK : ClassUniform p K)
    (hexact : ∀ X, U (K (V X)) = swap X) : Function.Injective p := by
  classical
  intro c e hp
  by_contra hce
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  let X : State d A := fun i _ => if i = c then a else b
  have htransport : ∀ s Y, K (V (rowRot s Y)) = rot s (K (V Y)) := by
    intro s Y
    apply hUi
    rw [hexact, hU s, hexact, swap_rowRot]
  have hfix : rot (e - c) (K (V X)) = K (V X) := by
    funext i j
    let s : ZMod d := j - c
    have hv : rot (e - c) (V (rowRot s X)) = V (rowRot s X) := by
      rw [← hV (e - c)]
      rfl
    have heq := hK.columns_of_same_class hp (V (rowRot s X)) i
    rw [hv, htransport] at heq
    change K (V X) i (e + s) = K (V X) i (c + s) at heq
    change K (V X) i (j + (e - c)) = K (V X) i j
    have h1 : e + s = j + (e - c) := by simp [s, sub_eq_add_neg, add_left_comm]
    have h2 : c + s = j := by simp [s, sub_eq_add_neg]
    simpa only [h1, h2] using heq
  have hout : rot (e - c) (swap X) = swap X := by
    rw [← hexact X, ← hU, hfix]
  have hv := congrFun (congrFun hout 0) c
  have hsum : c + (e - c) = e := by
    rw [← add_sub_assoc, add_sub_cancel_left]
  have hval : b = a := by
    simpa [rot, swap, X, hsum, Ne.symm hce] using hv
  exact hab hval.symm

/-- For a finite alphabet, exactness on the complete square state space supplies
the outer injectivity automatically. -/
theorem uniform_sandwich_finite [Finite A] [NeZero d]
    {p : ZMod d → κ} {U K V : State d A → State d A}
    (hU : Equivariant U) (hV : Equivariant V) (hK : ClassUniform p K)
    (hexact : ∀ X, U (K (V X)) = swap X) : Function.Injective p := by
  have hUs : Function.Surjective U := by
    intro Y
    refine ⟨K (V (swap Y)), ?_⟩
    rw [hexact, swap_swap]
  exact uniform_sandwich_injective_classes hU hV
    ((Finite.injective_iff_surjective).mpr hUs) hK hexact

end SharedDecoders
