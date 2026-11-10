import ClassUniformMemo.Transfer
import ClassUniformMemo.ParityCosetData
import Mathlib.Data.ZMod.Basic

/-!
# Two classes: the parity-coset codes

For `d = 4k` the *parity-coset colouring* of `ZMod d` (`parityCosetCls`) has the two classes
`J₀ = {0, 2, …, d - 4}`, the even residues other than `d - 2`, and `J₁`, the rest.

This file proves that it carries a class-uniform code of dimension `(d ^ 2 + 2 d) / 2 + (d / 4 - 1)`,
an excess of `d / 4 - 1` over the interval value `(d ^ 2 + 2 d) / 2` of two classes, at `d = 8, 12, 16`,
over every field in which `2 ≠ 0`, from the certificates of `ClassUniformMemo.ParityCosetData`
(dimensions `41`, `86`, `147`; excess `1`, `2`, `3`).  The memo proves the same excess for every
`d = 4k ≥ 8` in its text; that proof is not formalized here.  The finite facts about the data are
proved by `decide +kernel`.

## Main results

* `parityCosetCls`: the colouring; `parityCosetCls_eq_true_iff`.
* `exists_parityCoset_code_d8`, `exists_parityCoset_code_d12`, `exists_parityCoset_code_d16`.
-/

namespace ClassUniformMemo

open Module SwapRigidity

/-- The parity-coset colouring of `ZMod d`: the class `true` is `J₀ = {0, 2, …, d - 4}`, the even
residues other than `d - 2`, and the class `false` is the rest. -/
def parityCosetCls (d : ℕ) (c : ZMod d) : Bool :=
  decide (c.val % 2 = 0 ∧ c.val + 2 ≠ d)

/-- The class `true` of the parity-coset colouring is the set of even residues other than `d - 2`. -/
theorem parityCosetCls_eq_true_iff (d : ℕ) (c : ZMod d) :
    parityCosetCls d c = true ↔ c.val % 2 = 0 ∧ c.val + 2 ≠ d := by
  simp [parityCosetCls]

/-- Entry `(i, j)` of a matrix given by the list of its nonzero entries. -/
def sparseEntry {n : ℕ} : List ((ZMod n × ZMod n) × ℤ) → ZMod n → ZMod n → ℤ
  | [], _, _ => 0
  | (p, v) :: t, i, j => if p = (i, j) then v else sparseEntry t i j

/-! ### `d = 8` -/

/-- The certificate of the parity-coset code at `d = 8`, from `tools/data/parity_coset_d8.json`. -/
def parityCosetD8 : Certificate ℤ 8 41 Bool where
  cls := parityCosetCls 8
  gen k := Matrix.of fun i j => sparseEntry (pcGenD8.getD k.val []) i j
  coef := pcCoefD8
  scale := pcScaleD8
  pivot l := pcPivotsD8.getD l.val (0, 0)
  pivotScale := pcPivotScaleD8

/-- The rule holds for the generators at `d = 8`, multiplied by `2` (by `decide`, evaluated by the kernel). -/
theorem parityCosetD8_rowsHold : parityCosetD8.RowsHold := by
  unfold Certificate.RowsHold
  decide +kernel

/-- The private positions of the generators at `d = 8` (by `decide`, evaluated by the kernel). -/
theorem parityCosetD8_pivotsHold : parityCosetD8.PivotsHold := by
  unfold Certificate.PivotsHold
  decide +kernel

/-! ### `d = 12` -/

/-- The certificate of the parity-coset code at `d = 12`, from `tools/data/parity_coset_d12.json`. -/
def parityCosetD12 : Certificate ℤ 12 86 Bool where
  cls := parityCosetCls 12
  gen k := Matrix.of fun i j => sparseEntry (pcGenD12.getD k.val []) i j
  coef := pcCoefD12
  scale := pcScaleD12
  pivot l := pcPivotsD12.getD l.val (0, 0)
  pivotScale := pcPivotScaleD12

/-- The rule holds for the generators at `d = 12`, multiplied by `2` (by `decide`, evaluated by the kernel). -/
theorem parityCosetD12_rowsHold : parityCosetD12.RowsHold := by
  unfold Certificate.RowsHold
  decide +kernel

/-- The private positions of the generators at `d = 12` (by `decide`, evaluated by the kernel). -/
theorem parityCosetD12_pivotsHold : parityCosetD12.PivotsHold := by
  unfold Certificate.PivotsHold
  decide +kernel

/-! ### `d = 16` -/

/-- The certificate of the parity-coset code at `d = 16`, from `tools/data/parity_coset_d16.json`. -/
def parityCosetD16 : Certificate ℤ 16 147 Bool where
  cls := parityCosetCls 16
  gen k := Matrix.of fun i j => sparseEntry (pcGenD16.getD k.val []) i j
  coef := pcCoefD16
  scale := pcScaleD16
  pivot l := pcPivotsD16.getD l.val (0, 0)
  pivotScale := pcPivotScaleD16

/-- The rule holds for the generators at `d = 16`, multiplied by `2` (by `decide`, evaluated by the kernel). -/
theorem parityCosetD16_rowsHold : parityCosetD16.RowsHold := by
  unfold Certificate.RowsHold
  decide +kernel

/-- The private positions of the generators at `d = 16` (by `decide`, evaluated by the kernel). -/
theorem parityCosetD16_pivotsHold : parityCosetD16.PivotsHold := by
  unfold Certificate.PivotsHold
  decide +kernel

/-! ### The codes -/

/-- Over a field with `2 ≠ 0`, the two scales of the parity-coset certificates map to nonzero
elements. -/
theorem intCast_two_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    Int.castRingHom F 2 ≠ 0 := by
  simpa using h2

/-- **The parity-coset code at `d = 8`**: over every field with `2 ≠ 0`, a class-uniform code of
dimension `41 = (8 ^ 2 + 2 * 8) / 2 + 1` for the classes `{0, 2, 4}` and `{1, 3, 5, 6, 7}`. -/
theorem exists_parityCoset_code_d8 (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ 𝒳 : Submodule F (Matrix (ZMod 8) (ZMod 8) F),
      IsClassUniformCode (parityCosetCls 8) 𝒳 ∧ finrank F 𝒳 = 41 ∧
        2 * finrank F 𝒳 = 8 ^ 2 + 2 * 8 + 2 * 1 :=
  ⟨parityCosetD8.code (Int.castRingHom F),
    parityCosetD8.isClassUniformCode parityCosetD8_rowsHold (intCast_two_ne_zero h2),
    parityCosetD8.finrank_code parityCosetD8_pivotsHold (intCast_two_ne_zero h2),
    by rw [parityCosetD8.finrank_code parityCosetD8_pivotsHold (intCast_two_ne_zero h2)]; norm_num⟩

/-- **The parity-coset code at `d = 12`**: over every field with `2 ≠ 0`, a class-uniform code of
dimension `86 = (12 ^ 2 + 2 * 12) / 2 + 2`. -/
theorem exists_parityCoset_code_d12 (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ 𝒳 : Submodule F (Matrix (ZMod 12) (ZMod 12) F),
      IsClassUniformCode (parityCosetCls 12) 𝒳 ∧ finrank F 𝒳 = 86 ∧
        2 * finrank F 𝒳 = 12 ^ 2 + 2 * 12 + 2 * 2 :=
  ⟨parityCosetD12.code (Int.castRingHom F),
    parityCosetD12.isClassUniformCode parityCosetD12_rowsHold (intCast_two_ne_zero h2),
    parityCosetD12.finrank_code parityCosetD12_pivotsHold (intCast_two_ne_zero h2),
    by rw [parityCosetD12.finrank_code parityCosetD12_pivotsHold (intCast_two_ne_zero h2)]; norm_num⟩

/-- **The parity-coset code at `d = 16`**: over every field with `2 ≠ 0`, a class-uniform code of
dimension `147 = (16 ^ 2 + 2 * 16) / 2 + 3`. -/
theorem exists_parityCoset_code_d16 (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ 𝒳 : Submodule F (Matrix (ZMod 16) (ZMod 16) F),
      IsClassUniformCode (parityCosetCls 16) 𝒳 ∧ finrank F 𝒳 = 147 ∧
        2 * finrank F 𝒳 = 16 ^ 2 + 2 * 16 + 2 * 3 :=
  ⟨parityCosetD16.code (Int.castRingHom F),
    parityCosetD16.isClassUniformCode parityCosetD16_rowsHold (intCast_two_ne_zero h2),
    parityCosetD16.finrank_code parityCosetD16_pivotsHold (intCast_two_ne_zero h2),
    by rw [parityCosetD16.finrank_code parityCosetD16_pivotsHold (intCast_two_ne_zero h2)]; norm_num⟩

end ClassUniformMemo
