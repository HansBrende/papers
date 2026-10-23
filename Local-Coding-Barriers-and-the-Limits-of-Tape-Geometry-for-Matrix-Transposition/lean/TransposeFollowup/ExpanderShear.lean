import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! The binary row shear and its support graph.  The row indices distinguish
the two halves; changing to consecutive finite row indices is an equivalence.
No expansion or native implementation is assumed by these definitions. -/

namespace TransposeFollowup.ExpanderShear

open scoped BigOperators
set_option autoImplicit false

abbrev Bit := ZMod 2
abbrev Row (m : ℕ) := Fin m ⊕ Fin m
abbrev Bank (m W : ℕ) := Row m → Fin W → Bit

def ofBool (a : Bool) : Bit := if a then 1 else 0

@[simp] theorem ofBool_false : ofBool false = 0 := rfl
@[simp] theorem ofBool_true : ofBool true = 1 := rfl

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofBool]

theorem ofBool_xor (a b : Bool) : ofBool (a.xor b) = ofBool a + ofBool b := by
  cases a <;> cases b <;> simp [ofBool, CharTwo.add_self_eq_zero]

noncomputable def boolEquiv : Bool ≃ Bit :=
  Equiv.ofBijective ofBool
    ((Fintype.bijective_iff_injective_and_card ofBool).mpr
      ⟨ofBool_injective, by simp [Bit, ZMod.card]⟩)

@[simp] theorem boolEquiv_apply (a : Bool) : boolEquiv a = ofBool a := rfl

def rowEquiv (m : ℕ) : Row m ≃ Fin (m + m) := finSumFinEquiv

def matrix {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) :
    Matrix (Row m) (Row m) Bit := Matrix.fromBlocks 1 0 L 1

def shear {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit) (x : Bank m W) : Bank m W
  | .inl i, w => x (.inl i) w
  | .inr j, w => x (.inr j) w + ∑ i, L j i * x (.inl i) w

@[simp] theorem shear_left {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x : Bank m W) (i : Fin m) (w : Fin W) :
    shear L x (.inl i) w = x (.inl i) w := rfl

@[simp] theorem shear_right {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x : Bank m W) (j : Fin m) (w : Fin W) :
    shear L x (.inr j) w = x (.inr j) w + ∑ i, L j i * x (.inl i) w := rfl

theorem shear_involutive {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit) :
    Function.Involutive (shear (W := W) L) := by
  intro x
  funext r w
  cases r <;> simp [shear, add_assoc, CharTwo.add_self_eq_zero]

def shearLinear {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit) :
    Bank m W →ₗ[Bit] Bank m W where
  toFun := shear L
  map_add' x y := by
    funext r w
    cases r with
    | inl i => rfl
    | inr j =>
      simp only [shear, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring
  map_smul' a x := by
    funext r w
    cases r with
    | inl i => rfl
    | inr j =>
      simp only [shear, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

def shearEquiv {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit) :
    Bank m W ≃ₗ[Bit] Bank m W :=
  { shearLinear L with
    invFun := shear L
    left_inv := shear_involutive L
    right_inv := shear_involutive L }

@[simp] theorem shearEquiv_apply {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x : Bank m W) : shearEquiv L x = shear L x := rfl

theorem shear_eq_mulVec {m W : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (x : Bank m W) (r : Row m) (w : Fin W) :
    shear L x r w = (matrix L).mulVec (fun i => x i w) r := by
  cases r <;> simp [shear, matrix, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply, add_comm]

def coreGraph {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit) : SimpleGraph (Row m) where
  Adj a b := match a, b with
    | .inl i, .inr j => L j i ≠ 0
    | .inr j, .inl i => L j i ≠ 0
    | _, _ => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> exact h⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

noncomputable def nnz {α β F : Type*} [Fintype α] [Fintype β] [Zero F]
    (M : Matrix α β F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : α × β => M p.1 p.2 ≠ 0)).card

def crossMatrix {α F : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α F) (J I : Finset α) : Matrix J (↑(Iᶜ) : Finset α) F :=
  M.submatrix Subtype.val Subtype.val

end TransposeFollowup.ExpanderShear
