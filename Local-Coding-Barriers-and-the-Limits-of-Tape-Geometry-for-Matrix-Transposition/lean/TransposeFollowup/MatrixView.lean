import Transpose.Eventually
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finite views of the original paper's matrix encoding

This is a finite-coordinate adapter for counting input families. The matrix
encoding and transpose operation are imported from the original framework.
No machine model, encoding order, or transpose specification is replaced.
-/

namespace TransposeFollowup

set_option autoImplicit false

abbrev Row (n b : ℕ) := Fin n → Fin b → Bool
abbrev FiniteMatrix (n b : ℕ) := Fin n → Row n b
abbrev MatrixBit (n b : ℕ) := Fin n × (Fin n × Fin b)

def matrixBits {n b : ℕ} (x : FiniteMatrix n b) : MatrixBit n b → Bool :=
  fun i => x i.1 i.2.1 i.2.2

def bitsMatrix {n b : ℕ} (x : MatrixBit n b → Bool) : FiniteMatrix n b :=
  fun i j t => x (i, (j, t))

@[simp] theorem bitsMatrix_matrixBits {n b : ℕ} (x : FiniteMatrix n b) :
    bitsMatrix (matrixBits x) = x := rfl

@[simp] theorem matrixBits_bitsMatrix {n b : ℕ} (x : MatrixBit n b → Bool) :
    matrixBits (bitsMatrix x) = x := rfl

theorem matrixBits_injective (n b : ℕ) :
    Function.Injective (matrixBits (n := n) (b := b)) := by
  intro x y h
  exact congrArg bitsMatrix h

def restrictMatrix (n b : ℕ) (A : Transpose.Matrix) : FiniteMatrix n b :=
  fun i j t => A i j t

def extendMatrix {n b : ℕ} (x : FiniteMatrix n b) : Transpose.Matrix :=
  fun i j t => if hi : i < n then
    if hj : j < n then
      if ht : t < b then x ⟨i, hi⟩ ⟨j, hj⟩ ⟨t, ht⟩ else false
    else false
  else false

@[simp] theorem extendMatrix_apply {n b : ℕ} (x : FiniteMatrix n b)
    (i j : Fin n) (t : Fin b) : extendMatrix x i j t = x i j t := by
  simp [extendMatrix]

@[simp] theorem restrict_extendMatrix {n b : ℕ} (x : FiniteMatrix n b) :
    restrictMatrix n b (extendMatrix x) = x := by
  funext i j t
  exact extendMatrix_apply x i j t

theorem encode_extend_restrict (n b : ℕ) (A : Transpose.Matrix) :
    Transpose.encode n b (extendMatrix (restrictMatrix n b A)) =
      Transpose.encode n b A := by
  apply Transpose.encode_eq_of_pointwise
  intro i j t hi hj ht
  simp [extendMatrix, restrictMatrix, hi, hj, ht]

def encodeFinite {n b : ℕ} (x : FiniteMatrix n b) : List Bool :=
  Transpose.encode n b (extendMatrix x)

theorem encodeFinite_injective (n b : ℕ) :
    Function.Injective (encodeFinite (n := n) (b := b)) := by
  intro x y h
  funext i j t
  have he := Transpose.pointwise_of_encode_eq h i j t i.isLt j.isLt t.isLt
  simpa using he

def transposed {n b : ℕ} (x : FiniteMatrix n b) : FiniteMatrix n b :=
  restrictMatrix n b (Transpose.transpose (extendMatrix x))

@[simp] theorem transposed_apply {n b : ℕ} (x : FiniteMatrix n b)
    (i j : Fin n) (t : Fin b) : transposed x i j t = x j i t := by
  simp [transposed, restrictMatrix, Transpose.transpose]

theorem encodeFinite_transposed {n b : ℕ} (x : FiniteMatrix n b) :
    encodeFinite (transposed x) = Transpose.encode n b
      (Transpose.transpose (extendMatrix x)) :=
  encode_extend_restrict n b (Transpose.transpose (extendMatrix x))

theorem card_finiteMatrix (n b : ℕ) :
    Fintype.card (FiniteMatrix n b) = 2 ^ (n * n * b) := by
  simp only [FiniteMatrix, Row, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

end TransposeFollowup
