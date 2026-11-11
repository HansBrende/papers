import SharedDecoders.Model
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Linear shared decoding and projections of coupled lane groups

No assumption is made that a decoder acts separately on the two lane groups.
The restriction to zero in one group is constructed from the full decoder.
-/

namespace SharedDecoders

section LinearDecoders

variable {F A B κ : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] {d : ℕ}

def IsLinearSharedCode (p : ZMod d → κ) (C : Submodule F (State d A)) : Prop :=
  ∃ f : κ → State d A →ₗ[F] (ZMod d → A),
    ∀ X ∈ C, ∀ c, X c = f (p c) (rot c X)

theorem IsLinearSharedCode.isSharedCode {p : ZMod d → κ}
    {C : Submodule F (State d A)} (h : IsLinearSharedCode p C) :
    IsSharedCode F p C := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun j => f j, hf⟩

def entryLinear (f : A →ₗ[F] B) : State d A →ₗ[F] State d B where
  toFun X i j := f (X i j)
  map_add' X Y := by ext i j; exact f.map_add _ _
  map_smul' r X := by ext i j; exact f.map_smul r _

def wordLinear (f : A →ₗ[F] B) : (ZMod d → A) →ₗ[F] (ZMod d → B) where
  toFun X j := f (X j)
  map_add' X Y := by ext j; exact f.map_add _ _
  map_smul' r X := by ext j; exact f.map_smul r _

@[simp] theorem entryLinear_apply (f : A →ₗ[F] B) (X : State d A) (i j) :
    entryLinear f X i j = f (X i j) := rfl

@[simp] theorem entryLinear_rot (f : A →ₗ[F] B) (s : ZMod d) (X : State d A) :
    entryLinear f (rot s X) = rot s (entryLinear f X) := rfl

/-- Restrict a cross-lane decoder to zero in the first group and project its
output to the second group. -/
theorem IsLinearSharedCode.inr_comap {p : ZMod d → κ}
    {C : Submodule F (State d (A × B))} (hC : IsLinearSharedCode p C) :
    IsLinearSharedCode p (C.comap (entryLinear (LinearMap.inr F A B))) := by
  obtain ⟨f, hf⟩ := hC
  refine ⟨fun j => (wordLinear (LinearMap.snd F A B)).comp
    ((f j).comp (entryLinear (LinearMap.inr F A B))), ?_⟩
  intro X hX c
  have h := congrArg (fun v : ZMod d → A × B => fun j => (v j).2)
    (hf _ hX c)
  exact h

/-- Projection bounds a linearly decoded subcode by the dimension of the
first group plus the actual linear-decoder capacity of the second group. -/
theorem linear_subcode_lane_bound [NeZero d]
    [FiniteDimensional F A] [FiniteDimensional F B]
    {p : ZMod d → κ} (G : Submodule F (State d A))
    (H : Submodule F (State d B)) (C : Submodule F (State d (A × B)))
    (hC : IsLinearSharedCode p C)
    (hG : ∀ X ∈ C, entryLinear (LinearMap.fst F A B) X ∈ G)
    (hH : ∀ X ∈ C, entryLinear (LinearMap.snd F A B) X ∈ H)
    (L : ℕ) (hL : ∀ D : Submodule F (State d B), D ≤ H →
      IsLinearSharedCode p D → Module.finrank F D ≤ L) :
    Module.finrank F C ≤ Module.finrank F G + L := by
  let R := C.comap (entryLinear (LinearMap.inr F A B))
  have hRH : R ≤ H := by
    intro X hX
    exact hH _ hX
  have hRL : Module.finrank F R ≤ L := hL R hRH hC.inr_comap
  let π : C →ₗ[F] G :=
    { toFun := fun X => ⟨entryLinear (LinearMap.fst F A B) X, hG X X.property⟩
      map_add' := fun X Y => by ext i j; rfl
      map_smul' := fun r X => by ext i j; rfl }
  let ι : LinearMap.ker π →ₗ[F] R :=
    { toFun := fun X => ⟨entryLinear (LinearMap.snd F A B) X.val.val, by
        have hz : entryLinear (LinearMap.fst F A B) X.val.val = 0 :=
          congrArg Subtype.val X.property
        have he : entryLinear (LinearMap.inr F A B)
            (entryLinear (LinearMap.snd F A B) X.val.val) = X.val.val := by
          ext i j <;> simp only [entryLinear_apply, LinearMap.inr_apply,
            LinearMap.snd_apply]
          exact (congrFun (congrFun hz i) j).symm
        change entryLinear (LinearMap.inr F A B)
          (entryLinear (LinearMap.snd F A B) X.val.val) ∈ C
        rw [he]
        exact X.val.property⟩
      map_add' := fun X Y => by ext i j; rfl
      map_smul' := fun r X => by ext i j; rfl }
  have hι : Function.Injective ι := by
    intro X Y h
    apply Subtype.ext
    apply Subtype.ext
    have h2 := congrArg Subtype.val h
    have hx : entryLinear (LinearMap.fst F A B) X.val.val = 0 :=
      congrArg Subtype.val X.property
    have hy : entryLinear (LinearMap.fst F A B) Y.val.val = 0 :=
      congrArg Subtype.val Y.property
    funext i j
    apply Prod.ext
    · exact congrFun (congrFun (hx.trans hy.symm) i) j
    · exact congrFun (congrFun h2 i) j
  have hk := LinearMap.finrank_le_finrank_of_injective hι
  have hr := Submodule.finrank_le (LinearMap.range π)
  have hn := LinearMap.finrank_range_add_finrank_ker π
  omega

/-- A linear decoder must respect a three-view dependence. The labels are the
actual labels of the three receiver positions. -/
theorem IsLinearSharedCode.triple_rows_zero {p : ZMod d → κ}
    {C : Submodule F (State d A)} (hC : IsLinearSharedCode p C)
    {X : State d A} (hX : X ∈ C) (s c : ZMod d)
    (hzero : X + rot s X + rot (2 * s) X = 0)
    (h₁ : p (c + s) = p c) (h₂ : p (c + 2 * s) = p c) :
    X c + X (c + s) + X (c + 2 * s) = 0 := by
  obtain ⟨f, hf⟩ := hC
  have hz : rot c X + rot (c + s) X + rot (c + 2 * s) X = 0 := by
    ext i j
    simpa [rot, add_assoc] using congrFun (congrFun hzero i) (j + c)
  calc
    X c + X (c + s) + X (c + 2 * s) =
        f (p c) (rot c X + rot (c + s) X + rot (c + 2 * s) X) := by
      rw [map_add, map_add, hf X hX c, hf X hX (c + s), hf X hX (c + 2 * s), h₁, h₂]
    _ = 0 := by rw [hz, map_zero]

/-- Each independent row triple loses one whole row-space dimension. The
bound holds for an arbitrary subspace, including subspaces mixing all lanes. -/
theorem triple_row_finrank_bound [NeZero d] [FiniteDimensional F A]
    {J : Type*} [Fintype J] (e : (Fin 3 × J) ≃ ZMod d)
    (R : Submodule F (ZMod d → A)) (C : Submodule F (State d A))
    (hR : ∀ X ∈ C, ∀ c, X c ∈ R)
    (hzero : ∀ X ∈ C, ∀ j, X (e (0, j)) + X (e (1, j)) + X (e (2, j)) = 0) :
    Module.finrank F C ≤ 2 * Fintype.card J * Module.finrank F R := by
  let f : C →ₗ[F] (J → Fin 2 → R) :=
    { toFun := fun X j i => ⟨X.val (e (⟨i.val + 1, by omega⟩, j)), hR X X.property _⟩
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }
  have hf : Function.Injective f := by
    intro X Y h
    have h₁ (j : J) : X.val (e (1, j)) = Y.val (e (1, j)) :=
      congrArg Subtype.val (congrFun (congrFun h j) 0)
    have h₂ (j : J) : X.val (e (2, j)) = Y.val (e (2, j)) :=
      congrArg Subtype.val (congrFun (congrFun h j) 1)
    apply Subtype.ext
    funext c
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective c
    fin_cases i
    · have hx := hzero X X.property j
      have hy := hzero Y Y.property j
      rw [h₁, h₂] at hx
      exact add_right_cancel (add_right_cancel (hx.trans hy.symm))
    · exact h₁ j
    · exact h₂ j
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using h

end LinearDecoders

end SharedDecoders
