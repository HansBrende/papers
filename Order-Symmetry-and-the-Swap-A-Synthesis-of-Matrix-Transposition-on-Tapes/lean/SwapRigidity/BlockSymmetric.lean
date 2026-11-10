import SwapRigidity.ClassUniform
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Group.Nat.Even

/-!
# Block-symmetric matrices: the class-uniform bound is attained (sharpness of Theorem TP)

Let `n = M * m` and cut the index set `ZMod n` into `M` intervals of length `m`; the class of a
row `c` is `c.val / m`.  A matrix is *block-symmetric* if each of its `M * M` blocks of size
`m × m` is symmetric.

* `isClassUniformCode_blockSymmetric`: the block-symmetric matrices are a class-uniform code
  for these classes.
* `two_mul_finrank_blockSymmetric`: their dimension is `(n ^ 2 + M * n) / 2`.

So the bound `IsClassUniformCode.two_mul_finrank_le` is an equality for `M` equal interval
classes (`blockSymmetric_attains_bound`).
-/

namespace SwapRigidity

open Module LinearMap

variable (F : Type*) [Field F] (M m : ℕ)

/-- The index `a * m + k` of the row (or column) at offset `k` of block `a`, as an element of
`ZMod (M * m)`. -/
def blockIdx (a : Fin M) (k : Fin m) : ZMod (M * m) :=
  ((a.val * m + k.val : ℕ) : ZMod (M * m))

/-- The block-symmetric matrices: for all blocks `a`, `b` and offsets `k`, `l`,
`X (a * m + k) (b * m + l) = X (a * m + l) (b * m + k)`. -/
def blockSymmetric : Submodule F (Matrix (ZMod (M * m)) (ZMod (M * m)) F) where
  carrier := {X | ∀ (a b : Fin M) (k l : Fin m),
    X (blockIdx M m a k) (blockIdx M m b l) = X (blockIdx M m a l) (blockIdx M m b k)}
  add_mem' := fun hX hY a b k l => by
    rw [Matrix.add_apply, Matrix.add_apply, hX a b k l, hY a b k l]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c X hX a b k l => by
    rw [Matrix.smul_apply, Matrix.smul_apply, hX a b k l]

variable {F M m} in
/-- Membership in the block-symmetric matrices, unfolded. -/
theorem mem_blockSymmetric {X : Matrix (ZMod (M * m)) (ZMod (M * m)) F} :
    X ∈ blockSymmetric F M m ↔ ∀ (a b : Fin M) (k l : Fin m),
      X (blockIdx M m a k) (blockIdx M m b l) = X (blockIdx M m a l) (blockIdx M m b k) :=
  Iff.rfl

variable {M m} in
/-- The representative of `blockIdx M m a k` in `[0, M * m)` is `a * m + k`. -/
theorem val_blockIdx (a : Fin M) (k : Fin m) : (blockIdx M m a k).val = a.val * m + k.val := by
  apply ZMod.val_cast_of_lt
  calc a.val * m + k.val < a.val * m + m := Nat.add_lt_add_left k.isLt _
    _ = (a.val + 1) * m := by ring
    _ ≤ M * m := Nat.mul_le_mul_right m a.isLt

section BlockCoordinates

variable {M m} [NeZero M] [NeZero m]

/-- The block `i.val / m` containing the index `i`. -/
def blockOf (i : ZMod (M * m)) : Fin M :=
  ⟨i.val / m, Nat.div_lt_of_lt_mul ((ZMod.val_lt i).trans_eq (Nat.mul_comm M m))⟩

/-- The offset `i.val % m` of the index `i` inside its block. -/
def offsetOf (i : ZMod (M * m)) : Fin m :=
  ⟨i.val % m, Nat.mod_lt _ (NeZero.pos m)⟩

/-- An index is recovered from its block and its offset. -/
theorem blockIdx_blockOf_offsetOf (i : ZMod (M * m)) :
    blockIdx M m (blockOf i) (offsetOf i) = i := by
  unfold blockIdx blockOf offsetOf
  rw [Nat.div_add_mod', ZMod.natCast_zmod_val]

/-- The block of the index `a * m + k` is `a`. -/
theorem blockOf_blockIdx (a : Fin M) (k : Fin m) : blockOf (blockIdx M m a k) = a := by
  apply Fin.ext
  show (blockIdx M m a k).val / m = a.val
  rw [val_blockIdx, Nat.add_comm, Nat.add_mul_div_right _ _ (NeZero.pos m),
    Nat.div_eq_of_lt k.isLt, Nat.zero_add]

omit [NeZero M] in
/-- The offset of the index `a * m + k` is `k`. -/
theorem offsetOf_blockIdx (a : Fin M) (k : Fin m) : offsetOf (blockIdx M m a k) = k := by
  apply Fin.ext
  show (blockIdx M m a k).val % m = k.val
  rw [val_blockIdx, Nat.mul_add_mod_of_lt k.isLt]

end BlockCoordinates

variable [NeZero M] [NeZero m]

/-- **The block-symmetric matrices are a class-uniform code** for the `M` interval classes
`c ↦ c.val / m`.  The decoder of block `a` reads entry `j = b * m + l` of a row from row
`a * m + l`, column `(b - a) * m`, of the rotated matrix. -/
theorem isClassUniformCode_blockSymmetric :
    IsClassUniformCode (fun c : ZMod (M * m) => c.val / m) (blockSymmetric F M m) := by
  refine ⟨fun a =>
    { toFun := fun Y j => Y ((a * m + j.val % m : ℕ) : ZMod (M * m))
        (((j.val / m * m : ℕ) : ZMod (M * m)) - ((a * m : ℕ) : ZMod (M * m)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, ?_⟩
  intro X hX c
  funext j
  have key := hX (blockOf c) (blockOf j) (offsetOf c) (offsetOf j)
  rw [blockIdx_blockOf_offsetOf, blockIdx_blockOf_offsetOf] at key
  have e : blockIdx M m (blockOf j) (offsetOf c) =
      ((j.val / m * m : ℕ) : ZMod (M * m)) - ((c.val / m * m : ℕ) : ZMod (M * m)) + c :=
    calc blockIdx M m (blockOf j) (offsetOf c)
        = ((j.val / m * m + c.val % m : ℕ) : ZMod (M * m)) := rfl
      _ = ((j.val / m * m : ℕ) : ZMod (M * m)) - ((c.val / m * m : ℕ) : ZMod (M * m)) +
            ((c.val / m * m + c.val % m : ℕ) : ZMod (M * m)) := by
          push_cast
          ring
      _ = _ := by rw [Nat.div_add_mod' c.val m, ZMod.natCast_zmod_val]
  rw [key, e]
  rfl

/-- The block-symmetric matrix whose block `(a, b)` is the symmetric matrix with entries
`f (a, b, s(k, l))`. -/
def ofBlockSym2 :
    (Fin M × Fin M × Sym2 (Fin m) → F) →ₗ[F] Matrix (ZMod (M * m)) (ZMod (M * m)) F where
  toFun f := Matrix.of fun i j => f (blockOf i, blockOf j, s(offsetOf i, offsetOf j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Entries of `ofBlockSym2 F M m f` in block coordinates. -/
theorem ofBlockSym2_apply_blockIdx (f : Fin M × Fin M × Sym2 (Fin m) → F) (a b : Fin M)
    (k l : Fin m) :
    ofBlockSym2 F M m f (blockIdx M m a k) (blockIdx M m b l) = f (a, b, s(k, l)) := by
  show f (blockOf (blockIdx M m a k), blockOf (blockIdx M m b l),
    s(offsetOf (blockIdx M m a k), offsetOf (blockIdx M m b l))) = _
  rw [blockOf_blockIdx, blockOf_blockIdx, offsetOf_blockIdx, offsetOf_blockIdx]

/-- A block-symmetric matrix determines the function it comes from. -/
theorem ofBlockSym2_injective : Function.Injective (ofBlockSym2 F M m) := by
  intro f g hfg
  funext ⟨a, b, z⟩
  induction z using Sym2.ind with
  | _ k l => rw [← ofBlockSym2_apply_blockIdx F M m f, ← ofBlockSym2_apply_blockIdx F M m g, hfg]

/-- The block-symmetric matrices are exactly the matrices of the form `ofBlockSym2 F f`. -/
theorem range_ofBlockSym2 : range (ofBlockSym2 F M m) = blockSymmetric F M m := by
  ext X
  constructor
  · rintro ⟨f, rfl⟩ a b k l
    rw [ofBlockSym2_apply_blockIdx, ofBlockSym2_apply_blockIdx, Sym2.eq_swap]
  · intro hX
    refine ⟨fun p => Sym2.lift ⟨fun k l => X (blockIdx M m p.1 k) (blockIdx M m p.2.1 l),
      fun k l => hX p.1 p.2.1 k l⟩ p.2.2, ?_⟩
    ext i j
    show X (blockIdx M m (blockOf i) (offsetOf i)) (blockIdx M m (blockOf j) (offsetOf j)) =
      X i j
    rw [blockIdx_blockOf_offsetOf, blockIdx_blockOf_offsetOf]

/-- **Dimension of the block-symmetric matrices.**  With `n = M * m`, the block-symmetric
matrices have dimension `(n ^ 2 + M * n) / 2`. -/
theorem two_mul_finrank_blockSymmetric :
    2 * finrank F (blockSymmetric F M m) = (M * m) ^ 2 + M * (M * m) := by
  rw [← range_ofBlockSym2, LinearMap.finrank_range_of_inj (ofBlockSym2_injective F M m),
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Sym2.card, Fintype.card_fin, Nat.choose_two_right]
  have h := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (m + 1))
  calc 2 * (M * (M * ((m + 1) * (m + 1 - 1) / 2)))
      = M * M * (2 * ((m + 1) * (m + 1 - 1) / 2)) := by ring
    _ = M * M * ((m + 1) * m) := by rw [h, Nat.add_sub_cancel]
    _ = (M * m) ^ 2 + M * (M * m) := by ring

/-! ### Sharpness of the class-uniform bound -/

/-- The first rows of the `M` blocks: the rows `a * m`. -/
def blockStarts : Finset (ZMod (M * m)) :=
  Finset.univ.image fun a : Fin M => blockIdx M m a 0

/-- There are `M` block starts. -/
theorem card_blockStarts : (blockStarts M m).card = M := by
  rw [blockStarts, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  have h := congrArg blockOf hab
  rwa [blockOf_blockIdx, blockOf_blockIdx] at h

/-- A row that is not the first row of a block has the same class as the row before it. -/
theorem val_sub_one_div_eq_of_notMem_blockStarts {c : ZMod (M * m)}
    (hc : c ∉ blockStarts M m) : (c - 1).val / m = c.val / m := by
  have hm : 0 < m := NeZero.pos m
  have hr : c.val % m ≠ 0 := by
    intro h0
    apply hc
    rw [blockStarts, Finset.mem_image]
    refine ⟨blockOf c, Finset.mem_univ _, ?_⟩
    have h1 : offsetOf c = 0 := Fin.ext h0
    rw [← h1, blockIdx_blockOf_offsetOf]
  have hpos : 1 ≤ c.val := by
    rcases Nat.eq_zero_or_pos c.val with h | h
    · rw [h, Nat.zero_mod] at hr
      exact absurd rfl hr
    · exact h
  have hval : (c - 1).val = c.val - 1 := by
    have e : c - 1 = ((c.val - 1 : ℕ) : ZMod (M * m)) := by
      rw [Nat.cast_sub hpos, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [e]
    exact ZMod.val_cast_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) c.val_lt)
  have hdecomp : c.val - 1 = (c.val % m - 1) + c.val / m * m := by
    have := Nat.div_add_mod' c.val m
    omega
  have hlt : c.val % m - 1 < m := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hm)
  rw [hval, hdecomp, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- **The class-uniform bound is attained for `M` equal interval classes.**  The set
`blockStarts M m` of `M` rows satisfies the hypotheses of
`IsClassUniformCode.two_mul_finrank_le` for the classes `c ↦ c.val / m`, and for the
class-uniform code `blockSymmetric F M m` the bound `2 * dim 𝒳 ≤ n ^ 2 + n * |S|` is an
equality. -/
theorem blockSymmetric_attains_bound :
    (blockStarts M m).Nonempty ∧ (∀ c ∉ blockStarts M m, (c - 1).val / m = c.val / m) ∧
      2 * finrank F (blockSymmetric F M m) = (M * m) ^ 2 + M * m * (blockStarts M m).card := by
  refine ⟨?_, fun c hc => val_sub_one_div_eq_of_notMem_blockStarts M m hc, ?_⟩
  · rw [← Finset.card_pos, card_blockStarts]
    exact NeZero.pos M
  · rw [two_mul_finrank_blockSymmetric, card_blockStarts]
    ring

end SwapRigidity
