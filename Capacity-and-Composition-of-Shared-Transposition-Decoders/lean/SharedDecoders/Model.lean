import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Logic.Function.Iterate

/-!
# Shared column decoders on the complete matrix space

The entry alphabet can itself be a vector of lanes. A decoder receives a rotated
matrix and its receiver class, but not the receiver index. The code predicate
allows arbitrary total decoders on a linear source; it does not assert that the
decoders are linear. Composition results concern complete maps instead.
-/

namespace SharedDecoders

abbrev State (d : ℕ) (A : Type*) := ZMod d → ZMod d → A

variable {d : ℕ} {A κ : Type*}

def rot (s : ZMod d) (X : State d A) : State d A := fun i j => X i (j + s)

def rowRot (s : ZMod d) (X : State d A) : State d A := fun i j => X (i + s) j

def swap (X : State d A) : State d A := fun i j => X j i

@[simp] theorem rot_apply (s : ZMod d) (X : State d A) (i j : ZMod d) :
    rot s X i j = X i (j + s) := rfl

@[simp] theorem rowRot_apply (s : ZMod d) (X : State d A) (i j : ZMod d) :
    rowRot s X i j = X (i + s) j := rfl

@[simp] theorem swap_apply (X : State d A) (i j : ZMod d) : swap X i j = X j i := rfl

@[simp] theorem rot_zero (X : State d A) : rot 0 X = X := by
  funext i j
  simp [rot]

theorem rot_rot (s t : ZMod d) (X : State d A) : rot s (rot t X) = rot (s + t) X := by
  funext i j
  simp [rot, add_assoc]

@[simp] theorem rot_neg_rot (s : ZMod d) (X : State d A) : rot (-s) (rot s X) = X := by
  rw [rot_rot, neg_add_cancel, rot_zero]

@[simp] theorem rot_rot_neg (s : ZMod d) (X : State d A) : rot s (rot (-s) X) = X := by
  rw [rot_rot, add_neg_cancel, rot_zero]

def rotEquiv (s : ZMod d) : State d A ≃ State d A where
  toFun := rot s
  invFun := rot (-s)
  left_inv := rot_neg_rot s
  right_inv := rot_rot_neg s

@[simp] theorem swap_swap (X : State d A) : swap (swap X) = X := rfl

def swapEquiv : State d A ≃ State d A where
  toFun := swap
  invFun := swap
  left_inv := swap_swap
  right_inv := swap_swap

theorem swap_rot (s : ZMod d) (X : State d A) : swap (rot s X) = rowRot s (swap X) := rfl

theorem swap_rowRot (s : ZMod d) (X : State d A) : swap (rowRot s X) = rot s (swap X) := rfl

theorem rowRot_rot (s t : ZMod d) (X : State d A) :
    rowRot s (rot t X) = rot t (rowRot s X) := rfl

theorem rowRot_rowRot (s t : ZMod d) (X : State d A) :
    rowRot s (rowRot t X) = rowRot (s + t) X := by
  funext i j
  simp [rowRot, add_assoc]

@[simp] theorem rowRot_zero (X : State d A) : rowRot 0 X = X := by
  funext i j
  simp [rowRot]

def Equivariant (H : State d A → State d A) : Prop :=
  ∀ s X, H (rot s X) = rot s (H X)

def ClassUniform (p : ZMod d → κ) (K : State d A → State d A) : Prop :=
  ∃ f : κ → State d A → (ZMod d → A),
    ∀ X c i, K X i c = f (p c) (rot c X) i

theorem ClassUniform.columns_of_same_class {p : ZMod d → κ}
    {K : State d A → State d A} (hK : ClassUniform p K)
    {c e : ZMod d} (hp : p c = p e) (X : State d A) (i : ZMod d) :
    K X i e = K (rot (e - c) X) i c := by
  obtain ⟨f, hf⟩ := hK
  rw [hf, hf, ← hp, rot_rot]
  congr 2
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem ClassUniform.commutes_of_period {p : ZMod d → κ}
    {K : State d A → State d A} (hK : ClassUniform p K)
    {s : ZMod d} (hp : ∀ c, p (c + s) = p c) (X : State d A) :
    K (rot s X) = rot s (K X) := by
  obtain ⟨f, hf⟩ := hK
  funext i c
  simp only [rot_apply, hf, hp, rot_rot]

theorem equivariant_comp {H K : State d A → State d A}
    (hH : Equivariant H) (hK : Equivariant K) : Equivariant (H ∘ K) := by
  intro s X
  exact (congrArg H (hK s X)).trans (hH s (K X))

theorem equivariant_iff_one_class (K : State d A → State d A) :
    Equivariant K ↔ ClassUniform (fun _ : ZMod d => ()) K := by
  constructor
  · intro h
    refine ⟨fun _ X i => K X i 0, ?_⟩
    intro X c i
    simp [h c X]
  · intro h s X
    exact h.commutes_of_period (fun _ => rfl) X

section Linear

variable (F : Type*) [Field F] [AddCommGroup A] [Module F A]

def rotLinear (s : ZMod d) : State d A →ₗ[F] State d A where
  toFun := rot s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


/-- Column rotation as a linear equivalence, shared by the dimension arguments. -/
def rotLinearEquiv (s : ZMod d) : State d A ≃ₗ[F] State d A where
  toLinearMap := rotLinear F s
  invFun := rot (-s)
  left_inv := rot_neg_rot s
  right_inv := rot_rot_neg s

@[simp] theorem rotLinearEquiv_toLinearMap (s : ZMod d) :
    (rotLinearEquiv F (A := A) s).toLinearMap = rotLinear F s := rfl

def swapLinear : State d A →ₗ[F] State d A where
  toFun := swap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def IsSharedCode (p : ZMod d → κ) (C : Submodule F (State d A)) : Prop :=
  ∃ f : κ → State d A → (ZMod d → A),
    ∀ X ∈ C, ∀ c, X c = f (p c) (rot c X)

@[simp] theorem rotLinear_apply (s : ZMod d) (X : State d A) :
    rotLinear F s X = rot s X := rfl

@[simp] theorem swapLinear_apply (X : State d A) : swapLinear F X = swap X := rfl

end Linear

end SharedDecoders
