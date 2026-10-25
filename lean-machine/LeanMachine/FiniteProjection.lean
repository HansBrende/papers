import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic

/-! Finite-coordinate restriction and the cost of adjoining one coordinate.
These lemmas apply to arbitrary finite-dimensional linear codes, independently
of any recovery graph or choice of field. -/

namespace LeanMachine.FiniteProjection

open Module

variable {V K A : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]

/-- Codewords that vanish on the observed coordinates. -/
def vanishing (C : Submodule K (V → A)) (S : Finset V) : Submodule K C where
  carrier := {f | ∀ v ∈ S, (f : V → A) v = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg v hv; simp [hf v hv, hg v hv]
  smul_mem' := by intro c f hf v hv; simp [hf v hv]

omit [Fintype V] [DecidableEq V] [FiniteDimensional K A] in
@[simp] theorem mem_vanishing {C : Submodule K (V → A)} {S : Finset V} {f : C} :
    f ∈ vanishing C S ↔ ∀ v ∈ S, (f : V → A) v = 0 := Iff.rfl

omit [Fintype V] [DecidableEq V] [FiniteDimensional K A] in
theorem vanishing_antitone (C : Submodule K (V → A)) {S T : Finset V} (hST : S ⊆ T) :
    vanishing C T ≤ vanishing C S := fun _ hf v hv => hf v (hST hv)

omit [DecidableEq V] [FiniteDimensional K A] in
@[simp] theorem vanishing_univ (C : Submodule K (V → A)) : vanishing C Finset.univ = ⊥ := by
  ext f
  simp only [mem_vanishing, Finset.mem_univ, forall_const, Submodule.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    funext v
    exact h v
  · rintro rfl
    simp

omit [DecidableEq V] in
/-- Recording `S` costs at most its total coordinate capacity. -/
theorem dimension_le (C : Submodule K (V → A)) (S : Finset V) :
    finrank K C ≤ S.card * finrank K A + finrank K (vanishing C S) := by
  let f : C →ₗ[K] (S → A) :=
    { toFun := fun c v => (c : V → A) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker f = vanishing C S := by
    ext c
    simp only [LinearMap.mem_ker, mem_vanishing]
    change (fun v : S => (c : V → A) v) = 0 ↔ _
    simp only [funext_iff, Pi.zero_apply, Subtype.forall]
  have hn := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at hn
  have hr : finrank K (LinearMap.range f) ≤ S.card * finrank K A := by
    simpa [Module.finrank_pi_fintype] using (Submodule.finrank_le (LinearMap.range f))
  omega

/-- If the unknown target lies in `ker B`, adjoining that target reduces the
remaining dimension by at most the actual nullity of `B`. -/
theorem step_bound (C : Submodule K (V → A)) (S : Finset V) (x : V) (B : A →ₗ[K] A)
    (hB : ∀ f : C, f ∈ vanishing C S → B ((f : V → A) x) = 0) :
    finrank K (vanishing C S) ≤ finrank K (LinearMap.ker B) +
      finrank K (vanishing C (insert x S)) := by
  let Z := vanishing C S
  let f : Z →ₗ[K] LinearMap.ker B :=
    { toFun := fun c => ⟨(c.val : V → A) x, hB c.val c.property⟩
      map_add' := by intro a b; rfl
      map_smul' := by intro a b; rfl }
  have hle : vanishing C (insert x S) ≤ Z :=
    vanishing_antitone C (Finset.subset_insert _ _)
  have hker : LinearMap.ker f = (vanishing C (insert x S)).comap Z.subtype := by
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_comap, mem_vanishing, Finset.mem_insert,
      forall_eq_or_imp]
    change (⟨(c.val : V → A) x, hB c.val c.property⟩ : LinearMap.ker B) = 0 ↔ _
    constructor
    · intro h
      exact ⟨congrArg Subtype.val h, c.property⟩
    · intro h
      exact Subtype.ext h.1
  have heq := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [← hker] at heq
  have hn := LinearMap.finrank_range_add_finrank_ker (K := K) (V := Z) (V₂ := LinearMap.ker B) f
  have hr := Submodule.finrank_le (LinearMap.range f)
  change finrank K Z ≤ _
  omega

end LeanMachine.FiniteProjection
