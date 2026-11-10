import ClassUniformMemo.Transfer
import ClassUniformMemo.RationalData
import SwapRigidity.AperiodicExample
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The code of dimension 25 over every field of characteristic other than 3

The parent paper exhibits, for `n = 6` and the classes `{0, 1, 3}` and `{2, 4, 5}` of `ZMod 6`
(`SwapRigidity.aperiodicCls`), a class-uniform code of dimension `25` over `ZMod 2`
(`SwapRigidity.exists_classUniformCode_gt`), one more than the value `(6 ^ 2 + 2 * 6) / 2 = 24`
that every interval rule with two classes obeys.  This file shows that the gain does not depend
on the characteristic: the same classes carry a class-uniform code of dimension `25` over every
field in which `3 ≠ 0` (`exists_code_of_three_ne_zero`), in particular over every field of
characteristic zero and over `ZMod p` for every prime `p ≠ 3`.

Three certificates (`ClassUniformMemo.Certificate`) cover the fields:

* `rationalA`: a code over `ℚ` whose decoders have denominator `1008 = 2 ^ 4 * 3 ^ 2 * 7` and whose
  reduced kernel basis has denominator `3`; it serves every field in which `2`, `3` and `7` are
  nonzero.
* `rationalB`: a second code over `ℚ`, with denominators `187200 = 2 ^ 6 * 3 ^ 2 * 5 ^ 2 * 13` and
  `15`; it serves characteristic `7`.
* `binary`: the code of the parent paper over `ZMod 2`, which serves characteristic `2`.

The finite facts about the rational data (`rationalA_rowsHold`, `rationalA_pivotsHold` and the
same for `rationalB`) are proved by `decide`; the facts about `binary` are the parent paper's.

## Main results

* `exists_code_of_three_ne_zero`: a class-uniform code of dimension `25` for the classes
  `{0, 1, 3}` and `{2, 4, 5}` over every field with `(3 : F) ≠ 0`.
* `exists_classUniformCode_gt_of_three_ne_zero`: so `6 ^ 2 + 6 * 2 < 2 * dim 𝒳` over every such
  field.
* `exists_code_of_charZero`, `exists_code_zmod`: characteristic zero, and `ZMod p` for primes
  `p ≠ 3`.
-/

namespace ClassUniformMemo

open Module SwapRigidity

/-- Entry `(i, j)` of a `6 × 6` matrix given as the list of its entries in row-major order. -/
def entryOf (row : List ℤ) (i j : ZMod 6) : ℤ :=
  row.getD (i.val * 6 + j.val) 0

/-! ### The rational code `A` -/

/-- The certificate of the rational code `A`, from `tools/data/rational_a.json`. -/
def rationalA : Certificate ℤ 6 25 Bool where
  cls := aperiodicCls
  gen k := Matrix.of fun i j => entryOf (ratGenRowsA.getD k.val []) i j
  coef := ratCoefA
  scale := ratScaleA
  pivot l := ratPivotsA.getD l.val (0, 0)
  pivotScale := ratPivotScaleA

/-- The rule holds for the generators of `A`, multiplied by `1008` (`25 * 6 * 6` equations over
`ℤ`, by `decide`). -/
theorem rationalA_rowsHold : rationalA.RowsHold := by
  unfold Certificate.RowsHold
  decide

/-- The generators of `A` are `3` times the standard kernel basis at their private positions
(`25 * 25` entries, by `decide`). -/
theorem rationalA_pivotsHold : rationalA.PivotsHold := by
  unfold Certificate.PivotsHold
  decide

/-! ### The rational code `B` -/

/-- The certificate of the rational code `B`, from `tools/data/rational_b.json`. -/
def rationalB : Certificate ℤ 6 25 Bool where
  cls := aperiodicCls
  gen k := Matrix.of fun i j => entryOf (ratGenRowsB.getD k.val []) i j
  coef := ratCoefB
  scale := ratScaleB
  pivot l := ratPivotsB.getD l.val (0, 0)
  pivotScale := ratPivotScaleB

/-- The rule holds for the generators of `B`, multiplied by `187200` (`25 * 6 * 6` equations over
`ℤ`, by `decide`). -/
theorem rationalB_rowsHold : rationalB.RowsHold := by
  unfold Certificate.RowsHold
  decide

/-- The generators of `B` are `15` times the standard kernel basis at their private positions
(`25 * 25` entries, by `decide`). -/
theorem rationalB_pivotsHold : rationalB.PivotsHold := by
  unfold Certificate.PivotsHold
  decide

/-! ### The binary code of the parent paper -/

/-- The certificate of the parent paper's code over `ZMod 2`: its generators, decoders with all
coefficients `1`, and private positions. -/
def binary : Certificate (ZMod 2) 6 25 Bool where
  cls := aperiodicCls
  gen := aperiodicGen
  coef b r := (aperiodicDecSupport b r).map fun p => (p, 1)
  scale := 1
  pivot := aperiodicPivot
  pivotScale := 1

/-- The rule holds for the generators of the binary code (from the parent paper). -/
theorem binary_rowsHold : binary.RowsHold := by
  intro k c r
  have h := row_apply_of_mem_aperiodicCode (aperiodicGen_mem_aperiodicCode k) c r
  simp only [binary, one_mul, List.map_map, Function.comp_def]
  exact h

/-- The private positions of the binary code (from the parent paper). -/
theorem binary_pivotsHold : binary.PivotsHold :=
  aperiodicGen_pivot

/-! ### Every field of characteristic other than 3 -/

/-- **The code of dimension 25 over every field with `3 ≠ 0`.**  For the classes `{0, 1, 3}` and
`{2, 4, 5}` of `ZMod 6` there is a class-uniform code of dimension `25` over every field `F` in
which `3 ≠ 0`: the code `binary` in characteristic `2`, the code `rationalB` in characteristic
`7`, and the code `rationalA` otherwise. -/
theorem exists_code_of_three_ne_zero (F : Type*) [Field F] (h3 : (3 : F) ≠ 0) :
    ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
      IsClassUniformCode aperiodicCls 𝒳 ∧ finrank F 𝒳 = 25 := by
  by_cases h2 : (2 : F) = 0
  · -- characteristic `2`: the parent paper's code, mapped from `ZMod 2`
    have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
    let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
    have hone : φ 1 ≠ 0 := by simp
    exact ⟨binary.code φ, binary.isClassUniformCode binary_rowsHold hone,
      binary.finrank_code binary_pivotsHold hone⟩
  by_cases h7 : (7 : F) = 0
  · -- characteristic `7`: the code `B`, whose denominators are prime to `7`
    have hN : Int.castRingHom F rationalB.scale ≠ 0 := by
      have e : (187200 : F) = 7 * 26742 + 2 * 3 := by norm_num
      simp only [rationalB, ratScaleB, eq_intCast, Int.cast_ofNat]
      rw [e, h7, zero_mul, zero_add]
      exact mul_ne_zero h2 h3
    have hP : Int.castRingHom F rationalB.pivotScale ≠ 0 := by
      have e : (15 : F) = 7 * 2 + 1 := by norm_num
      simp only [rationalB, ratPivotScaleB, eq_intCast, Int.cast_ofNat]
      rw [e, h7, zero_mul, zero_add]
      exact one_ne_zero
    exact ⟨rationalB.code (Int.castRingHom F), rationalB.isClassUniformCode rationalB_rowsHold hN,
      rationalB.finrank_code rationalB_pivotsHold hP⟩
  · -- otherwise `2`, `3` and `7` are nonzero: the code `A`
    have hN : Int.castRingHom F rationalA.scale ≠ 0 := by
      have e : (1008 : F) = 2 ^ 4 * 3 ^ 2 * 7 := by norm_num
      simp only [rationalA, ratScaleA, eq_intCast, Int.cast_ofNat]
      rw [e]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) h7
    have hP : Int.castRingHom F rationalA.pivotScale ≠ 0 := by
      simpa only [rationalA, ratPivotScaleA, eq_intCast, Int.cast_ofNat] using h3
    exact ⟨rationalA.code (Int.castRingHom F), rationalA.isClassUniformCode rationalA_rowsHold hN,
      rationalA.finrank_code rationalA_pivotsHold hP⟩

/-- **The interval bound fails over every field with `3 ≠ 0`.**  For two classes there is a
class-uniform code over `F` with `6 ^ 2 + 6 * 2 < 2 * dim 𝒳`. -/
theorem exists_classUniformCode_gt_of_three_ne_zero (F : Type*) [Field F] (h3 : (3 : F) ≠ 0) :
    ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
      IsClassUniformCode aperiodicCls 𝒳 ∧ 6 ^ 2 + 6 * 2 < 2 * finrank F 𝒳 := by
  obtain ⟨𝒳, h𝒳, hdim⟩ := exists_code_of_three_ne_zero F h3
  exact ⟨𝒳, h𝒳, by rw [hdim]; norm_num⟩

/-- Characteristic zero, for example `ℚ`, `ℝ` and `ℂ`. -/
theorem exists_code_of_charZero (F : Type*) [Field F] [CharZero F] :
    ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
      IsClassUniformCode aperiodicCls 𝒳 ∧ finrank F 𝒳 = 25 :=
  exists_code_of_three_ne_zero F (by norm_num)

/-- The prime fields `ZMod p` for every prime `p ≠ 3`. -/
theorem exists_code_zmod (p : ℕ) [hp : Fact p.Prime] (h3 : p ≠ 3) :
    ∃ 𝒳 : Submodule (ZMod p) (Matrix (ZMod 6) (ZMod 6) (ZMod p)),
      IsClassUniformCode aperiodicCls 𝒳 ∧ finrank (ZMod p) 𝒳 = 25 := by
  refine exists_code_of_three_ne_zero (ZMod p) ?_
  intro h
  have hdvd : p ∣ 3 := by
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact (ZMod.natCast_eq_zero_iff 3 p).1 h'
  exact h3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 hdvd)

end ClassUniformMemo
