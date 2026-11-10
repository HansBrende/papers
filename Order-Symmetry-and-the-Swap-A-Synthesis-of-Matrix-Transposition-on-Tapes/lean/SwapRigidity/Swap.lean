import SwapRigidity.Pigeonhole
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Group.Nat.Even

/-!
# The swap: the best case of the pigeonhole lemma is the pairing value

The swap `τ` is transposition, as a linear endomorphism of the square matrices over a field
`F` indexed by a finite type `ι` of size `n`.

* `two_mul_finrank_ker_swap_sub_one`: the symmetric matrices `ker (τ - 1)` have dimension
  `n (n + 1) / 2`, in every characteristic.
* `two_mul_finrank_range_swap_sub_one`: `τ - 1` has rank `n (n - 1) / 2`, in every
  characteristic.
* `card_le_finrank_ker_swap_commutator`: every linear map `T` on matrices commutes with the
  swap on a subspace of dimension at least `n`.  So the pigeonhole lemma never gives
  less than the pairing value `n (n + 1) / 2`.
-/

namespace SwapRigidity

open Module LinearMap

variable (F : Type*) [Field F] (ι : Type*)

/-- The swap: transposition as a linear endomorphism of the square matrices. -/
def swap : Matrix ι ι F →ₗ[F] Matrix ι ι F :=
  (Matrix.transposeLinearEquiv ι ι F F).toLinearMap

/-- The swap sends a matrix to its transpose. -/
@[simp]
theorem swap_apply (X : Matrix ι ι F) : swap F ι X = X.transpose :=
  rfl

/-- The symmetric matrix with entries given by a function on unordered pairs of indices. -/
def ofSym2 : (Sym2 ι → F) →ₗ[F] Matrix ι ι F where
  toFun f := Matrix.of fun i j => f s(i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Entries of the symmetric matrix `ofSym2 F ι f`. -/
@[simp]
theorem ofSym2_apply (f : Sym2 ι → F) (i j : ι) : ofSym2 F ι f i j = f s(i, j) :=
  rfl

/-- A symmetric matrix determines the function on unordered pairs it comes from. -/
theorem ofSym2_injective : Function.Injective (ofSym2 F ι) := by
  intro f g hfg
  funext z
  induction z using Sym2.ind with
  | _ i j => exact congrFun (congrFun hfg i) j

/-- The matrices fixed by the swap are exactly those that come from a function on unordered
pairs of indices. -/
theorem range_ofSym2 : range (ofSym2 F ι) = ker (swap F ι - 1) := by
  ext X
  rw [mem_range, mem_ker, sub_apply, sub_eq_zero, swap_apply, Module.End.one_apply]
  constructor
  · rintro ⟨f, rfl⟩
    ext i j
    rw [Matrix.transpose_apply, ofSym2_apply, ofSym2_apply, Sym2.eq_swap]
  · intro hX
    have hsymm : ∀ i j, X i j = X j i := fun i j => congrFun (congrFun hX.symm i) j
    refine ⟨Sym2.lift ⟨fun i j => X i j, hsymm⟩, ?_⟩
    ext i j
    rfl

variable [Fintype ι]

/-- **Symmetric matrices.**  The fixed space of the swap on `n × n` matrices has dimension
`n (n + 1) / 2`, in every characteristic. -/
theorem two_mul_finrank_ker_swap_sub_one :
    2 * finrank F (ker (swap F ι - 1)) = Fintype.card ι * (Fintype.card ι + 1) := by
  rw [← range_ofSym2, LinearMap.finrank_range_of_inj (ofSym2_injective F ι),
    Module.finrank_fintype_fun_eq_card, Sym2.card, Nat.choose_two_right,
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self _), Nat.add_sub_cancel, mul_comm]

/-- **Rank of `τ - 1`.**  On `n × n` matrices the map `X ↦ Xᵀ - X` has rank `n (n - 1) / 2`,
in every characteristic. -/
theorem two_mul_finrank_range_swap_sub_one :
    2 * finrank F (range (swap F ι - 1)) = Fintype.card ι * (Fintype.card ι - 1) := by
  have h1 := two_mul_finrank_ker_swap_sub_one F ι
  have h2 := finrank_range_add_finrank_ker (swap F ι - 1)
  rw [Module.finrank_matrix, finrank_self, mul_one] at h2
  generalize Fintype.card ι = m at h1 h2 ⊢
  cases m with
  | zero => omega
  | succ m =>
    rw [Nat.add_sub_cancel]
    have e1 : (m + 1) * (m + 1 + 1) = (m + 1) * m + 2 * (m + 1) := by ring
    have e2 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    omega

/-- **The swap against any operator.**  Every linear map `T` on `n × n` matrices commutes
with the swap on a subspace of dimension at least `n`: `n ≤ dim ker [τ, T]`. -/
theorem card_le_finrank_ker_swap_commutator (T : Matrix ι ι F →ₗ[F] Matrix ι ι F) :
    Fintype.card ι ≤ finrank F (ker (swap F ι ∘ₗ T - T ∘ₗ swap F ι)) := by
  have h := two_mul_finrank_ker_sub_le_ker (swap F ι) 1 T
  have e : (swap F ι - 1) ∘ₗ T - T ∘ₗ (swap F ι - 1) = swap F ι ∘ₗ T - T ∘ₗ swap F ι := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.comp_id, sub_sub_sub_cancel_right]
  rw [e, two_mul_finrank_ker_swap_sub_one, Module.finrank_matrix, finrank_self, mul_one,
    mul_add, mul_one] at h
  omega

end SwapRigidity
