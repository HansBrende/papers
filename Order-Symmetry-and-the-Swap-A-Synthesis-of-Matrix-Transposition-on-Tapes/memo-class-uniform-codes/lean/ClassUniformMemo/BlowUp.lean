import SwapRigidity.ClassUniform
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Blow-ups of class-uniform codes

Write a point of `ZMod (n * k)` as `c = k * a + u` with `a = ⌊c / k⌋` in `ZMod n` (its *block*,
`hi`) and `u = c mod k` in `Fin k` (its *position*, `lo`); `emb k a u` is the point `k * a + u`.
Block `(u, v)` of a matrix `X` indexed by `ZMod (n * k)` is the `n × n` matrix of the entries of
`X` in the rows at position `u` and the columns at position `v` (`block`).

The *blow-up* of a code `𝒳` of `n × n` matrices (`blowUp k 𝒳`) consists of the matrices all of whose
`k * k` blocks lie in `𝒳`.  If `𝒳` is a class-uniform code for a colouring `cls` of `ZMod n`, its
blow-up is a class-uniform code for the colouring `c ↦ (cls ⌊c / k⌋, c mod k)` of `ZMod (n * k)`
(`isClassUniformCode_blowUp`), and its dimension is `k * k * dim 𝒳` (`finrank_blowUp`).  The new
colouring has `k` times as many classes.

The point of the decoders: rotating the columns of `X` by `c = k * a' + u` moves the columns at
position `v` to position `v - u` (with a borrow), and the decoder of the class `(cls a', u)` knows
`u`, so it can read every block of the rotated matrix in place (`rot_block`).

## Main results

* `isClassUniformCode_blowUp`: the blow-up of a class-uniform code is class-uniform.
* `finrank_blowUp`: `dim (blowUp k 𝒳) = k * k * dim 𝒳`.
* `two_mul_finrank_blowUp_sub`: the excess `2 * dim 𝒳 - (n ^ 2 + n * M)` over the interval value
  is multiplied by `k ^ 2`.
-/

namespace ClassUniformMemo

open Module SwapRigidity

variable {F : Type*} [Field F] {κ : Type*} {n : ℕ}

/-! ### Blocks and positions -/

/-- The point `k * a + u` of `ZMod (n * k)`: position `u` of block `a`. -/
def emb (k : ℕ) (a : ZMod n) (u : Fin k) : ZMod (n * k) :=
  ((k * a.val + u.val : ℕ) : ZMod (n * k))

/-- The block `⌊c / k⌋` of a point `c` of `ZMod (n * k)`. -/
def hi (k : ℕ) (c : ZMod (n * k)) : ZMod n :=
  ((c.val / k : ℕ) : ZMod n)

/-- The position `c mod k` of a point `c` of `ZMod (n * k)` in its block. -/
def lo {k : ℕ} [NeZero k] (c : ZMod (n * k)) : Fin k :=
  ⟨c.val % k, Nat.mod_lt _ (NeZero.pos k)⟩

variable {k : ℕ} [NeZero n] [NeZero k]

omit [NeZero k] in
theorem val_emb (a : ZMod n) (u : Fin k) : (emb k a u).val = k * a.val + u.val := by
  rw [emb, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have ha := ZMod.val_lt a
  have hu := u.isLt
  calc k * a.val + u.val < k * a.val + k := by omega
    _ = k * (a.val + 1) := by ring
    _ ≤ k * n := Nat.mul_le_mul_left k ha
    _ = n * k := Nat.mul_comm k n

/-- The block of `k * a + u` is `a`. -/
@[simp]
theorem hi_emb (a : ZMod n) (u : Fin k) : hi k (emb k a u) = a := by
  rw [hi, val_emb, Nat.mul_add_div (NeZero.pos k), Nat.div_eq_of_lt u.isLt, add_zero,
    ZMod.natCast_zmod_val]

/-- The position of `k * a + u` is `u`. -/
@[simp]
theorem lo_emb (a : ZMod n) (u : Fin k) : lo (emb k a u) = u := by
  ext
  simp only [lo, val_emb, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]

/-- Every point is `k * ⌊c / k⌋ + c mod k`. -/
@[simp]
theorem emb_hi_lo (c : ZMod (n * k)) : emb k (hi k c) (lo c) = c := by
  have hlt : c.val / k < n := by
    rw [Nat.div_lt_iff_lt_mul (NeZero.pos k)]
    exact ZMod.val_lt c
  rw [emb, hi, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  simp only [lo]
  rw [Nat.div_add_mod, ZMod.natCast_zmod_val]

omit [NeZero k] in
/-- Shifting: `(k * t + v) - u + (k * a + u) = k * (t + a) + v` in `ZMod (n * k)`. -/
theorem emb_sub_add_emb (t a : ZMod n) (u v : Fin k) :
    emb k t v - ((u.val : ℕ) : ZMod (n * k)) + emb k a u = emb k (t + a) v := by
  have hmod : ((k * (t + a).val : ℕ) : ZMod (n * k)) = ((k * (t.val + a.val) : ℕ) : ZMod (n * k)) := by
    rw [ZMod.natCast_eq_natCast_iff', ZMod.val_add, Nat.mul_comm n k, Nat.mul_mod_mul_left,
      Nat.mul_mod_mul_left, Nat.mod_mod]
  simp only [emb]
  rw [Nat.cast_add (k * (t + a).val), hmod]
  push_cast
  ring

/-- Stepping back by one inside a block: if the position of `c` is not `0`, then `c - 1` lies in
the same block. -/
theorem hi_sub_one_of_lo_ne_zero (c : ZMod (n * k)) (h : (lo c).val ≠ 0) :
    hi k (c - 1) = hi k c := by
  have hlt : (lo c).val - 1 < k := by have := (lo c).isLt; omega
  have hc : c - 1 = emb k (hi k c) ⟨(lo c).val - 1, hlt⟩ := by
    conv_lhs => rw [← emb_hi_lo c]
    simp only [emb]
    have e : k * (hi k c).val + (lo c).val = (k * (hi k c).val + ((lo c).val - 1)) + 1 := by omega
    rw [e, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [hc, hi_emb]

/-- Stepping back by one from the first position of a block lands in the previous block. -/
theorem hi_sub_one_of_lo_eq_zero (c : ZMod (n * k)) (h : (lo c).val = 0) :
    hi k (c - 1) = hi k c - 1 := by
  have hk : k - 1 < k := Nat.sub_lt (NeZero.pos k) one_pos
  have hc : c - 1 = emb k (hi k c - 1) ⟨k - 1, hk⟩ := by
    rw [sub_eq_iff_eq_add]
    conv_lhs => rw [← emb_hi_lo c]
    simp only [emb, h, add_zero]
    have hmod : (hi k c).val ≡ (hi k c - 1).val + 1 [MOD n] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        Nat.cast_one, sub_add_cancel]
    have hmul : k * (hi k c).val ≡ k * (hi k c - 1).val + (k - 1) + 1 [MOD n * k] := by
      have e : k * (hi k c - 1).val + (k - 1) + 1 = k * ((hi k c - 1).val + 1) := by
        have := NeZero.pos k
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [e, Nat.mul_comm n k]
      exact Nat.ModEq.mul_left' k hmod
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hmul, Nat.cast_add, Nat.cast_one]
  rw [hc, hi_emb]

/-! ### Blocks of a matrix -/

/-- Block `(u, v)` of a matrix indexed by `ZMod (n * k)`: entry `(a, t)` is the entry of `X` in
row `k * a + u` and column `k * t + v`. -/
def block (u v : Fin k) :
    Matrix (ZMod (n * k)) (ZMod (n * k)) F →ₗ[F] Matrix (ZMod n) (ZMod n) F where
  toFun X := Matrix.of fun a t => X (emb k a u) (emb k t v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero n] [NeZero k] in
@[simp]
theorem block_apply (u v : Fin k) (X : Matrix (ZMod (n * k)) (ZMod (n * k)) F) (a t : ZMod n) :
    block u v X a t = X (emb k a u) (emb k t v) :=
  rfl

/-- The matrix that the decoder of a class at position `u` reads for the output columns at
position `v`: entry `(a, t)` is the entry of `Y` in row `k * a + u` and column `k * t + v - u`. -/
def readBlock (u v : Fin k) :
    Matrix (ZMod (n * k)) (ZMod (n * k)) F →ₗ[F] Matrix (ZMod n) (ZMod n) F where
  toFun Y := Matrix.of fun a t => Y (emb k a u) (emb k t v - ((u.val : ℕ) : ZMod (n * k)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Rotation acts blockwise.**  Rotating the columns of block `(u, v)` by the block `⌊c / k⌋`
of `c`, where `u = c mod k`, gives what `readBlock u v` reads from `X` rotated by `c`. -/
theorem rot_block (c : ZMod (n * k)) (v : Fin k) (X : Matrix (ZMod (n * k)) (ZMod (n * k)) F) :
    rot (hi k c) (block (lo c) v X) = readBlock (lo c) v (rot c X) := by
  ext a t
  simp only [rot_apply, block_apply, readBlock]
  congr 1
  have h := emb_sub_add_emb t (hi k c) (lo c) v
  rw [emb_hi_lo] at h
  exact h.symm

/-! ### The blow-up -/

variable (k) in
/-- The blow-up of a code `𝒳` of `n × n` matrices: the matrices indexed by `ZMod (n * k)` all of
whose blocks lie in `𝒳`. -/
def blowUp (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    Submodule F (Matrix (ZMod (n * k)) (ZMod (n * k)) F) where
  carrier := {X | ∀ u v, block u v X ∈ 𝒳}
  add_mem' {X Y} hX hY u v := by
    rw [map_add]
    exact 𝒳.add_mem (hX u v) (hY u v)
  zero_mem' u v := by
    rw [map_zero]
    exact 𝒳.zero_mem
  smul_mem' a X hX u v := by
    rw [map_smul]
    exact 𝒳.smul_mem a (hX u v)

omit [NeZero n] [NeZero k] in
theorem mem_blowUp {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)}
    {X : Matrix (ZMod (n * k)) (ZMod (n * k)) F} :
    X ∈ blowUp k 𝒳 ↔ ∀ u v, block u v X ∈ 𝒳 :=
  Iff.rfl

variable (k) in
/-- The blown-up colouring of `ZMod (n * k)`: the class of `c` is the class of its block together
with its position. -/
def blowCls (cls : ZMod n → κ) (c : ZMod (n * k)) : κ × Fin k :=
  (cls (hi k c), lo c)

/-- The decoders of the blow-up: the decoder of the class `(b, u)` sends `Y` to the function whose
value at `j` is coordinate `⌊j / k⌋` of `dec b (readBlock u (j mod k) Y)`. -/
def blowDec (dec : κ → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F))) (p : κ × Fin k) :
    Matrix (ZMod (n * k)) (ZMod (n * k)) F →ₗ[F] (ZMod (n * k) → F) :=
  LinearMap.pi fun j => LinearMap.proj (hi k j) ∘ₗ dec p.1 ∘ₗ readBlock p.2 (lo j)

/-- **The blow-up of a class-uniform code is class-uniform**, for the blown-up colouring. -/
theorem isClassUniformCode_blowUp {cls : ZMod n → κ}
    {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)} (h : IsClassUniformCode cls 𝒳) :
    IsClassUniformCode (blowCls k cls) (blowUp k 𝒳) := by
  obtain ⟨dec, hdec⟩ := h
  refine ⟨blowDec dec, fun X hX c => ?_⟩
  funext j
  have hrow := hdec (block (lo c) (lo j) X) (hX (lo c) (lo j)) (hi k c)
  have h1 : X c j = block (lo c) (lo j) X (hi k c) (hi k j) := by
    rw [block_apply, emb_hi_lo, emb_hi_lo]
  rw [h1, hrow, rot_block]
  rfl

/-! ### The dimension of the blow-up -/

/-- Reassemble a matrix indexed by `ZMod (n * k)` from its blocks. -/
def assemble (f : Fin k × Fin k → Matrix (ZMod n) (ZMod n) F) :
    Matrix (ZMod (n * k)) (ZMod (n * k)) F :=
  Matrix.of fun i j => f (lo i, lo j) (hi k i) (hi k j)

theorem block_assemble (f : Fin k × Fin k → Matrix (ZMod n) (ZMod n) F) (u v : Fin k) :
    block u v (assemble f) = f (u, v) := by
  ext a t
  simp [assemble]

theorem assemble_block (X : Matrix (ZMod (n * k)) (ZMod (n * k)) F) :
    assemble (fun p => block p.1 p.2 X) = X := by
  ext i j
  simp [assemble]

variable (k) in
/-- The blow-up of `𝒳` is isomorphic to `k * k` copies of `𝒳`, one for each block. -/
def blowUpEquiv (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    blowUp k 𝒳 ≃ₗ[F] (Fin k × Fin k → 𝒳) where
  toFun X p := ⟨block p.1 p.2 X.1, X.2 p.1 p.2⟩
  map_add' X Y := by
    funext p
    ext1
    simp
  map_smul' a X := by
    funext p
    ext1
    simp
  invFun f := ⟨assemble fun p => (f p).1, fun u v => by
    rw [block_assemble]
    exact (f (u, v)).2⟩
  left_inv X := by
    ext1
    exact assemble_block X.1
  right_inv f := by
    funext p
    ext1
    exact block_assemble (fun q => (f q).1) p.1 p.2

variable (k) in
/-- **The dimension of the blow-up** is `k * k` times the dimension of the code. -/
theorem finrank_blowUp (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    finrank F (blowUp k 𝒳) = k * k * finrank F 𝒳 := by
  rw [(blowUpEquiv k 𝒳).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]

variable (k) in
/-- **The excess is multiplied by `k ^ 2`.**  If the colouring has `M` classes, the blown-up
colouring has `k * M` classes, and the excess of twice the dimension over the interval value
`n ^ 2 + n * M` is multiplied by `k ^ 2`. -/
theorem two_mul_finrank_blowUp_sub (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) (M : ℕ) :
    2 * finrank F (blowUp k 𝒳) - ((n * k) ^ 2 + (n * k) * (k * M)) =
      k ^ 2 * (2 * finrank F 𝒳 - (n ^ 2 + n * M)) := by
  rw [finrank_blowUp, Nat.mul_sub]
  congr 1 <;> ring

end ClassUniformMemo
