import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Fintype.Fin

/-!
# The flag bound for swap codes (Theorem FL)

For a field `F` and two finite families `A B : α → Matrix (Fin n) (Fin n) F`, the *swap code* is the
space of solutions `X` of the linear matrix equation

  `Xᵀ = ∑ a, A a * X * (B a)ᵀ`.

It is the kernel of `τ - K` on `V ⊗ V`, where `τ` is the swap and `K = ∑ a, A a ⊗ B a`.

## Main results

* `SwapRigidity.finrank_swapCode_le_of_staircase`: if column `b'` of every `B a` vanishes from row
  `g b'` on, the swap code has dimension at most `∑ b', min (g b') n`, whatever the `A a` are.
* `SwapRigidity.swapCodeEquiv`, `SwapRigidity.finrank_swapCode_conj`: the dimension is invariant
  under a change of bases `A a ↦ Q * A a * P⁻¹`, `B a ↦ P * B a * Q⁻¹`.
* `SwapRigidity.finrank_swapCode_le_of_flag`: the staircase bound after a change of bases (the flag
  form of Theorem FL in coordinates).
* `SwapRigidity.two_mul_finrank_swapCode_le_of_triangular`: if the `B a` are simultaneously upper
  triangular after a change of bases, the dimension is at most `n * (n + 1) / 2`.
* `SwapRigidity.finrank_swapCode_swap`: the two tensor sides can be exchanged, and with it the
  `_left` versions of the bounds (hypotheses on the `A a`).
* `SwapRigidity.exists_staircase_finrank_eq`: every staircase bound with `g ≤ n` is attained.
-/

namespace SwapRigidity

open Matrix Module

variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [Fintype α]

/-! ### The swap code -/

/-- The *swap code* of two families `A B` of `n × n` matrices: the space of all matrices `X` with
`Xᵀ = ∑ a, A a * X * (B a)ᵀ`. -/
def swapCode (A B : α → Matrix (Fin n) (Fin n) F) : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {X | Xᵀ = ∑ a, A a * X * (B a)ᵀ}
  add_mem' := by
    intro X Y hX hY
    change Xᵀ = _ at hX
    change Yᵀ = _ at hY
    change (X + Y)ᵀ = _
    simp only [transpose_add, hX, hY, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  zero_mem' := by
    change (0 : Matrix (Fin n) (Fin n) F)ᵀ = _
    simp
  smul_mem' := by
    intro c X hX
    change Xᵀ = _ at hX
    change (c • X)ᵀ = _
    simp only [transpose_smul, hX, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- Membership in the swap code is the defining matrix equation. -/
@[simp]
theorem mem_swapCode {A B : α → Matrix (Fin n) (Fin n) F} {X : Matrix (Fin n) (Fin n) F} :
    X ∈ swapCode A B ↔ Xᵀ = ∑ a, A a * X * (B a)ᵀ :=
  Iff.rfl

/-- Membership in the swap code, entry by entry: the entry `X b a` is the sum over the terms `t` and
over all `a'`, `b'` of `A t a a' * X a' b' * B t b b'`. -/
theorem mem_swapCode_iff_apply {A B : α → Matrix (Fin n) (Fin n) F}
    {X : Matrix (Fin n) (Fin n) F} :
    X ∈ swapCode A B ↔
      ∀ b a, X b a = ∑ t, ∑ a', ∑ b', A t a a' * X a' b' * B t b b' := by
  have entry : ∀ a b, (∑ t, A t * X * (B t)ᵀ) a b
      = ∑ t, ∑ a', ∑ b', A t a a' * X a' b' * B t b b' := by
    intro a b
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [mem_swapCode, ← Matrix.ext_iff]
  constructor
  · intro h b a
    rw [← entry, ← h a b, transpose_apply]
  · intro h a b
    rw [entry, ← h b a, transpose_apply]

/-! ### The staircase bound -/

/-- The elimination step of the staircase theorem. Suppose that column `b'` of every `B t` vanishes
from row `g b'` on. Then a solution `X` whose entries `X a' b'` with `a' < g b'` all vanish is
zero. -/
theorem eq_zero_of_mem_swapCode_of_staircase {A B : α → Matrix (Fin n) (Fin n) F}
    (g : Fin n → ℕ) (hB : ∀ t (b b' : Fin n), g b' ≤ (b : ℕ) → B t b b' = 0)
    {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ swapCode A B)
    (h0 : ∀ a' b' : Fin n, (a' : ℕ) < g b' → X a' b' = 0) : X = 0 := by
  rw [mem_swapCode_iff_apply] at hX
  -- Rows are eliminated from the last one upwards: row `b` is handled at stage `m` if `n ≤ b + m`.
  have key : ∀ m : ℕ, ∀ b : Fin n, n ≤ (b : ℕ) + m → ∀ a, X b a = 0 := by
    intro m
    induction m with
    | zero => intro b hb; have := b.isLt; omega
    | succ m ih =>
      intro b hb a
      rw [hX b a]
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun a' _ =>
        Finset.sum_eq_zero fun b' _ => ?_
      by_cases h1 : (b : ℕ) < a'
      · -- a later row: already known to vanish
        rw [ih a' (by omega) b', mul_zero, zero_mul]
      · by_cases h2 : g b' ≤ (b : ℕ)
        · -- the coefficient vanishes by the staircase hypothesis
          rw [hB t b b' h2, mul_zero]
        · -- `a' ≤ b < g b'`: an entry of the staircase
          rw [h0 a' b' (by omega), mul_zero, zero_mul]
  ext b a
  exact key n b (by omega) a

/-- The index set of the staircase of `g`: the positions `(a', b')` with `a' < g b'`. -/
abbrev Staircase (g : Fin n → ℕ) : Type :=
  {p : Fin n × Fin n // (p.1 : ℕ) < g p.2}

/-- The staircase of `g` has `∑ b', min (g b') n` positions. -/
theorem card_staircase (g : Fin n → ℕ) :
    Fintype.card (Staircase g) = ∑ b', min (g b') n := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← Finset.card_filter]
  rw [min_comm]
  exact Fin.card_filter_val_lt (n := n) (m := g b')

/-- Restriction of a solution to the positions of the staircase, as a linear map. -/
def staircaseRestrict (A B : α → Matrix (Fin n) (Fin n) F) (g : Fin n → ℕ) :
    swapCode A B →ₗ[F] (Staircase g → F) where
  toFun X p := (X : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Under the staircase hypothesis, a solution is determined by its entries on the staircase. -/
theorem staircaseRestrict_injective {A B : α → Matrix (Fin n) (Fin n) F} (g : Fin n → ℕ)
    (hB : ∀ t (b b' : Fin n), g b' ≤ (b : ℕ) → B t b b' = 0) :
    Function.Injective (staircaseRestrict A B g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  apply Subtype.ext
  refine eq_zero_of_mem_swapCode_of_staircase g hB X.2 fun a' b' h => ?_
  exact congrFun hX ⟨(a', b'), h⟩

/-- **Staircase theorem** (Theorem FL in coordinates). If column `b'` of every `B a` vanishes from
row `g b'` on, then the swap code has dimension at most `∑ b', min (g b') n`, for arbitrary `A a`.
No monotonicity of `g` is assumed. -/
theorem finrank_swapCode_le_of_staircase {A B : α → Matrix (Fin n) (Fin n) F} (g : Fin n → ℕ)
    (hB : ∀ a (b b' : Fin n), g b' ≤ (b : ℕ) → B a b b' = 0) :
    finrank F (swapCode A B) ≤ ∑ b', min (g b') n :=
  calc finrank F (swapCode A B)
      ≤ finrank F (Staircase g → F) :=
        LinearMap.finrank_le_finrank_of_injective (staircaseRestrict_injective g hB)
    _ = ∑ b', min (g b') n := by rw [Module.finrank_fintype_fun_eq_card, card_staircase]

/-! ### Invariance under a change of bases -/

/-- A change of bases maps solutions to solutions: if `P' * P = 1` and `Q' * Q = 1` and `X` solves
the equation of `A`, `B`, then `P * X * Qᵀ` solves the equation of the families `Q * A a * P'` and
`P * B a * Q'`. -/
theorem mul_mul_transpose_mem_swapCode {A B : α → Matrix (Fin n) (Fin n) F}
    {P P' Q Q' : Matrix (Fin n) (Fin n) F} (hP : P' * P = 1) (hQ : Q' * Q = 1)
    {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ swapCode A B) :
    P * X * Qᵀ ∈ swapCode (fun a => Q * A a * P') (fun a => P * B a * Q') := by
  rw [mem_swapCode] at hX ⊢
  have hP' : ∀ Z : Matrix (Fin n) (Fin n) F, P' * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
  have hQ' : ∀ Z : Matrix (Fin n) (Fin n) F, Qᵀ * (Q'ᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← transpose_mul, hQ, transpose_one, Matrix.one_mul]
  calc (P * X * Qᵀ)ᵀ
      = Q * Xᵀ * Pᵀ := by simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    _ = ∑ a, Q * (A a * X * (B a)ᵀ) * Pᵀ := by rw [hX, Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ a, Q * A a * P' * (P * X * Qᵀ) * (P * B a * Q')ᵀ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [transpose_mul, Matrix.mul_assoc, hP', hQ']

/-- **Equivalence invariance.** For `P' * P = 1` and `Q' * Q = 1`, the map `X ↦ P * X * Qᵀ` is a
linear equivalence from the swap code of `A`, `B` onto the swap code of the families
`Q * A a * P'` and `P * B a * Q'`. Its inverse is `Y ↦ P' * Y * Q'ᵀ`. -/
def swapCodeEquiv (A B : α → Matrix (Fin n) (Fin n) F) {P P' Q Q' : Matrix (Fin n) (Fin n) F}
    (hP : P' * P = 1) (hQ : Q' * Q = 1) :
    swapCode A B ≃ₗ[F] swapCode (fun a => Q * A a * P') (fun a => P * B a * Q') where
  toFun X := ⟨P * X.1 * Qᵀ, mul_mul_transpose_mem_swapCode hP hQ X.2⟩
  invFun Y := ⟨P' * Y.1 * Q'ᵀ, by
    have h := mul_mul_transpose_mem_swapCode (mul_eq_one_comm.mp hP) (mul_eq_one_comm.mp hQ) Y.2
    have hA : (fun a => Q' * (Q * A a * P') * P) = A := by
      funext a
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.mul_assoc, hP,
        Matrix.mul_one]
    have hB : (fun a => P' * (P * B a * Q') * Q) = B := by
      funext a
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul, Matrix.mul_assoc, hQ,
        Matrix.mul_one]
    rwa [hA, hB] at h⟩
  map_add' X Y := Subtype.ext (by simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul])
  map_smul' c X := Subtype.ext (by
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply])
  left_inv X := Subtype.ext (by
    have hQt : Qᵀ * Q'ᵀ = 1 := by rw [← transpose_mul, hQ, transpose_one]
    change P' * (P * X.1 * Qᵀ) * Q'ᵀ = X.1
    rw [Matrix.mul_assoc P, ← Matrix.mul_assoc P', hP, Matrix.one_mul, Matrix.mul_assoc, hQt,
      Matrix.mul_one])
  right_inv Y := Subtype.ext (by
    have hQt : Q'ᵀ * Qᵀ = 1 := by
      rw [← transpose_mul, mul_eq_one_comm.mp hQ, transpose_one]
    change P * (P' * Y.1 * Q'ᵀ) * Qᵀ = Y.1
    rw [Matrix.mul_assoc P', ← Matrix.mul_assoc P, mul_eq_one_comm.mp hP, Matrix.one_mul,
      Matrix.mul_assoc, hQt, Matrix.mul_one])

/-- The equivalence `swapCodeEquiv` is `X ↦ P * X * Qᵀ`. -/
@[simp]
theorem coe_swapCodeEquiv_apply (A B : α → Matrix (Fin n) (Fin n) F)
    {P P' Q Q' : Matrix (Fin n) (Fin n) F} (hP : P' * P = 1) (hQ : Q' * Q = 1)
    (X : swapCode A B) :
    (swapCodeEquiv A B hP hQ X : Matrix (Fin n) (Fin n) F) = P * X.1 * Qᵀ :=
  rfl

/-- The inverse of `swapCodeEquiv` is `Y ↦ P' * Y * Q'ᵀ`. -/
@[simp]
theorem coe_swapCodeEquiv_symm_apply (A B : α → Matrix (Fin n) (Fin n) F)
    {P P' Q Q' : Matrix (Fin n) (Fin n) F} (hP : P' * P = 1) (hQ : Q' * Q = 1)
    (Y : swapCode (fun a => Q * A a * P') (fun a => P * B a * Q')) :
    ((swapCodeEquiv A B hP hQ).symm Y : Matrix (Fin n) (Fin n) F) = P' * Y.1 * Q'ᵀ :=
  rfl

/-- **Equivalence invariance**, dimension form: for invertible `P`, `Q` the swap code of the
families `Q * A a * P⁻¹` and `P * B a * Q⁻¹` has the same dimension as the swap code of `A`, `B`. -/
theorem finrank_swapCode_conj (A B : α → Matrix (Fin n) (Fin n) F)
    {P Q : Matrix (Fin n) (Fin n) F} (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    finrank F (swapCode (fun a => Q * A a * P⁻¹) (fun a => P * B a * Q⁻¹))
      = finrank F (swapCode A B) :=
  (swapCodeEquiv A B (Matrix.nonsing_inv_mul P hP) (Matrix.nonsing_inv_mul Q hQ)).finrank_eq.symm

/-- **Flag form of Theorem FL, in coordinates.** If, after the change of bases given by invertible
matrices `P` and `Q`, column `b'` of every `P⁻¹ * B a * Q` vanishes from row `g b'` on, then the
swap code of `A`, `B` has dimension at most `∑ b', min (g b') n`, for arbitrary `A a`. -/
theorem finrank_swapCode_le_of_flag {A B : α → Matrix (Fin n) (Fin n) F}
    {P Q : Matrix (Fin n) (Fin n) F} (hP : IsUnit P.det) (hQ : IsUnit Q.det) (g : Fin n → ℕ)
    (hB : ∀ a (b b' : Fin n), g b' ≤ (b : ℕ) → (P⁻¹ * B a * Q) b b' = 0) :
    finrank F (swapCode A B) ≤ ∑ b', min (g b') n := by
  rw [(swapCodeEquiv A B (Matrix.mul_nonsing_inv P hP) (Matrix.mul_nonsing_inv Q hQ)).finrank_eq]
  exact finrank_swapCode_le_of_staircase g hB

/-- Twice the sum of `i + 1` over `i : Fin n` is `n * (n + 1)`. -/
theorem two_mul_sum_fin_succ (n : ℕ) : 2 * ∑ i : Fin n, ((i : ℕ) + 1) = n * (n + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

/-- **Triangular corollary.** If, after the change of bases given by invertible matrices `P` and
`Q`, every `P⁻¹ * B a * Q` is upper triangular, then the swap code of `A`, `B` has dimension at most
`n * (n + 1) / 2`, the dimension of the symmetric matrices, for arbitrary `A a`. -/
theorem two_mul_finrank_swapCode_le_of_triangular {A B : α → Matrix (Fin n) (Fin n) F}
    {P Q : Matrix (Fin n) (Fin n) F} (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hB : ∀ a (b b' : Fin n), b' < b → (P⁻¹ * B a * Q) b b' = 0) :
    2 * finrank F (swapCode A B) ≤ n * (n + 1) := by
  have h := finrank_swapCode_le_of_flag (A := A) hP hQ (fun b' => (b' : ℕ) + 1)
    (fun a b b' hb => hB a b b' (Fin.lt_def.mpr hb))
  have hmin : ∀ b' : Fin n, min ((b' : ℕ) + 1) n = (b' : ℕ) + 1 := fun b' =>
    min_eq_left b'.isLt
  simp only [hmin] at h
  calc 2 * finrank F (swapCode A B)
      ≤ 2 * ∑ b' : Fin n, ((b' : ℕ) + 1) := Nat.mul_le_mul_left 2 h
    _ = n * (n + 1) := two_mul_sum_fin_succ n

/-! ### Exchanging the two sides -/

/-- Transposition exchanges the two sides: `Xᵀ` solves the equation of `B`, `A` if `X` solves the
equation of `A`, `B`. -/
theorem transpose_mem_swapCode {A B : α → Matrix (Fin n) (Fin n) F}
    {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ swapCode A B) : Xᵀ ∈ swapCode B A := by
  rw [mem_swapCode] at hX ⊢
  rw [transpose_transpose]
  calc X = (Xᵀ)ᵀ := (transpose_transpose X).symm
    _ = (∑ a, A a * X * (B a)ᵀ)ᵀ := congrArg transpose hX
    _ = ∑ a, B a * Xᵀ * (A a)ᵀ := by
        rw [transpose_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- Transposition as a linear equivalence between the swap code of `A`, `B` and the swap code of
`B`, `A`. -/
def swapCodeTransposeEquiv (A B : α → Matrix (Fin n) (Fin n) F) :
    swapCode A B ≃ₗ[F] swapCode B A where
  toFun X := ⟨X.1ᵀ, transpose_mem_swapCode X.2⟩
  invFun Y := ⟨Y.1ᵀ, transpose_mem_swapCode Y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := Subtype.ext (transpose_transpose X.1)
  right_inv Y := Subtype.ext (transpose_transpose Y.1)

/-- The equivalence `swapCodeTransposeEquiv` is transposition. -/
@[simp]
theorem coe_swapCodeTransposeEquiv_apply (A B : α → Matrix (Fin n) (Fin n) F) (X : swapCode A B) :
    (swapCodeTransposeEquiv A B X : Matrix (Fin n) (Fin n) F) = X.1ᵀ :=
  rfl

/-- **Exchanged sides.** The swap codes of `A`, `B` and of `B`, `A` have the same dimension. -/
theorem finrank_swapCode_swap (A B : α → Matrix (Fin n) (Fin n) F) :
    finrank F (swapCode A B) = finrank F (swapCode B A) :=
  (swapCodeTransposeEquiv A B).finrank_eq

/-- The staircase theorem with the hypothesis on the first factors `A a`. -/
theorem finrank_swapCode_le_of_staircase_left {A B : α → Matrix (Fin n) (Fin n) F}
    (g : Fin n → ℕ) (hA : ∀ a (b b' : Fin n), g b' ≤ (b : ℕ) → A a b b' = 0) :
    finrank F (swapCode A B) ≤ ∑ b', min (g b') n := by
  rw [finrank_swapCode_swap]
  exact finrank_swapCode_le_of_staircase g hA

/-- The flag form of Theorem FL with the hypothesis on the first factors `A a`. -/
theorem finrank_swapCode_le_of_flag_left {A B : α → Matrix (Fin n) (Fin n) F}
    {P Q : Matrix (Fin n) (Fin n) F} (hP : IsUnit P.det) (hQ : IsUnit Q.det) (g : Fin n → ℕ)
    (hA : ∀ a (b b' : Fin n), g b' ≤ (b : ℕ) → (P⁻¹ * A a * Q) b b' = 0) :
    finrank F (swapCode A B) ≤ ∑ b', min (g b') n := by
  rw [finrank_swapCode_swap]
  exact finrank_swapCode_le_of_flag hP hQ g hA

/-- The triangular corollary with the hypothesis on the first factors `A a`. -/
theorem two_mul_finrank_swapCode_le_of_triangular_left {A B : α → Matrix (Fin n) (Fin n) F}
    {P Q : Matrix (Fin n) (Fin n) F} (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hA : ∀ a (b b' : Fin n), b' < b → (P⁻¹ * A a * Q) b b' = 0) :
    2 * finrank F (swapCode A B) ≤ n * (n + 1) := by
  rw [finrank_swapCode_swap]
  exact two_mul_finrank_swapCode_le_of_triangular hP hQ hA

/-! ### The staircase bound is attained -/

variable (F) in
/-- First factors of the extremal family of a staircase: the single-entry matrix `E_{ik}` for the
position `(k, i)` of the staircase (so `k < g i`). -/
def staircaseA (g : Fin n → ℕ) (p : Staircase g) : Matrix (Fin n) (Fin n) F :=
  single p.1.2 p.1.1 1

variable (F) in
/-- Second factors of the extremal family of a staircase: the single-entry matrix `E_{ki}` for the
position `(k, i)` of the staircase (so `k < g i`). -/
def staircaseB (g : Fin n → ℕ) (p : Staircase g) : Matrix (Fin n) (Fin n) F :=
  single p.1.1 p.1.2 1

/-- The second factors of the extremal family satisfy the staircase hypothesis. -/
theorem staircaseB_apply_eq_zero (g : Fin n → ℕ) (p : Staircase g) (b b' : Fin n)
    (h : g b' ≤ (b : ℕ)) : staircaseB F g p b b' = 0 := by
  apply single_apply_of_ne
  rintro ⟨h1, h2⟩
  have := p.2
  rw [h1, h2] at this
  omega

/-- The swap code of the extremal family consists of the matrices supported on the staircase. -/
theorem mem_swapCode_staircase_iff (g : Fin n → ℕ) {X : Matrix (Fin n) (Fin n) F} :
    X ∈ swapCode (staircaseA F g) (staircaseB F g) ↔
      ∀ k i : Fin n, ¬ (k : ℕ) < g i → X k i = 0 := by
  -- each term is `E_{ik} * X * E_{ik} = X k i • E_{ik}`
  have hsum : ∑ p : Staircase g, staircaseA F g p * X * (staircaseB F g p)ᵀ
      = ∑ p : Staircase g, single p.1.2 p.1.1 (X p.1.1 p.1.2) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [staircaseA, staircaseB, transpose_single, single_mul_mul_single, one_mul, mul_one]
  -- so the right-hand side is `Xᵀ` cut down to the transposed staircase
  have entry : ∀ i k : Fin n, (∑ p : Staircase g, single p.1.2 p.1.1 (X p.1.1 p.1.2)) i k
      = if (k : ℕ) < g i then X k i else 0 := by
    intro i k
    rw [Matrix.sum_apply]
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨(k, i), h⟩ : Staircase g)]
      · exact single_apply_same _ _ _
      · intro p _ hp
        apply single_apply_of_ne
        rintro ⟨h1, h2⟩
        exact hp (Subtype.ext (Prod.ext h2 h1))
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · refine Finset.sum_eq_zero fun p _ => ?_
      apply single_apply_of_ne
      rintro ⟨h1, h2⟩
      have := p.2
      rw [h1, h2] at this
      exact h this
  rw [mem_swapCode, hsum, ← Matrix.ext_iff]
  constructor
  · intro hX k i hki
    have := hX i k
    rwa [entry, ite_eq_right hki, transpose_apply] at this
  · intro hX i k
    rw [entry, transpose_apply]
    split_ifs with h
    · rfl
    · exact hX k i h

/-- For the extremal family, every assignment of values to the staircase extends to a solution. -/
theorem staircaseRestrict_surjective (g : Fin n → ℕ) :
    Function.Surjective (staircaseRestrict (staircaseA F g) (staircaseB F g) g) := by
  intro f
  -- extend `f` by zero outside the staircase
  let X : Matrix (Fin n) (Fin n) F :=
    Matrix.of fun k i : Fin n => if h : (k : ℕ) < g i then f ⟨(k, i), h⟩ else 0
  have hX : X ∈ swapCode (staircaseA F g) (staircaseB F g) := by
    rw [mem_swapCode_staircase_iff]
    intro k i h
    exact dite_eq_right h
  refine ⟨⟨X, hX⟩, funext fun p => ?_⟩
  change X p.1.1 p.1.2 = f p
  exact dite_eq_left p.2

/-- The swap code of the extremal family of a staircase has dimension exactly
`∑ b', min (g b') n`. -/
theorem finrank_swapCode_staircase (g : Fin n → ℕ) :
    finrank F (swapCode (staircaseA F g) (staircaseB F g)) = ∑ b', min (g b') n := by
  rw [(LinearEquiv.ofBijective _ ⟨staircaseRestrict_injective g (staircaseB_apply_eq_zero g),
    staircaseRestrict_surjective g⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    card_staircase]

variable (F) in
/-- **The staircase bound is attained.** For every `g` with `g b' ≤ n` there are a finite family
`A`, `B` that satisfies the staircase hypothesis and whose swap code has dimension exactly
`∑ b', g b'`. -/
theorem exists_staircase_finrank_eq (g : Fin n → ℕ) (hg : ∀ b', g b' ≤ n) :
    ∃ (α : Type) (_ : Fintype α) (A B : α → Matrix (Fin n) (Fin n) F),
      (∀ a (b b' : Fin n), g b' ≤ (b : ℕ) → B a b b' = 0) ∧
        finrank F (swapCode A B) = ∑ b', g b' :=
  ⟨Staircase g, inferInstance, staircaseA F g, staircaseB F g, staircaseB_apply_eq_zero g, by
    rw [finrank_swapCode_staircase]
    exact Finset.sum_congr rfl fun b' _ => min_eq_left (hg b')⟩

end SwapRigidity
