import BoundedArityDecoders.ExtensionLinearRun
import SwapRigidity.AperiodicExample
import SwapRigidity.ClassUniform
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Bounds.Basic

/-!
# Extension Result 2: Exact Solution of `Problem 9.1(b)` in Characteristic `∉ {2, 3}`

Formal statement specifications corresponding to **Result 2** (`Theorem 2`) in `extension.md`:

* Over **every** field `F` with `char F ∉ {2, 3}` (`ringChar F ≠ 2 ∧ ringChar F ≠ 3`, equivalently
  `(2 : F) ≠ 0 ∧ (3 : F) ≠ 0`), every class-uniform code `𝒳` for the two-class partition
  `{0, 1, 3} | {2, 4, 5}` (`SwapRigidity.aperiodicCls`) on `ZMod 6` satisfies
  `dim_F (𝒳 ∩ σ⁻¹ 𝒳) ≤ 14`, hence `2 * dim_F 𝒳 ≤ 36 + 14 = 50` and `dim_F 𝒳 ≤ 25`.
* Combined with the lower-bound construction of dimension `25` over every field with `3 ≠ 0`
  (`Theorem A` / `ClassUniformMemo.exists_code_of_three_ne_zero`), the maximum dimension of a
  class-uniform code for `{0, 1, 3} | {2, 4, 5}` on `ZMod 6` is **exact and equal to `25`** over
  every field `F` with `char F ∉ {2, 3}` (`IsGreatest ... 25` and
  `linearClassUniformMaxDim F 1 SwapRigidity.aperiodicCls = 25`), including every partition
  `cls : ZMod 6 → κ` with the same fibers `{0, 1, 3}` and `{2, 4, 5}`.
-/

namespace BoundedArityDecoders

open Module

/-- Predicate that a row coloring `cls : ZMod 6 → κ` induces the exact two-class partition
`{0, 1, 3} | {2, 4, 5}` of `Problem 9.1(b)` (`SwapRigidity.aperiodicCls`). -/
def IsAperiodicSixPartition {κ : Type*} (cls : ZMod 6 → κ) : Prop :=
  ∀ c c' : ZMod 6, cls c = cls c' ↔ SwapRigidity.aperiodicCls c = SwapRigidity.aperiodicCls c'

/-- **Partition & Characteristic Bridge (`Result 2` Preliminaries).**
1. `SwapRigidity.aperiodicCls` has classes `{0, 1, 3}` (`true`) and `{2, 4, 5}` (`false`) and
   satisfies `IsAperiodicSixPartition`;
2. For any field `F`, `ringChar F ≠ 2 ∧ ringChar F ≠ 3` holds if and only if
   `(2 : F) ≠ 0 ∧ (3 : F) ≠ 0` (equivalently `CoprimeToChar F 6`). -/
def Extension_Theorem2_PreliminariesSpec : Prop :=
  ((∀ c : ZMod 6, SwapRigidity.aperiodicCls c = true ↔ (c = 0 ∨ c = 1 ∨ c = 3)) ∧
    (∀ c : ZMod 6, SwapRigidity.aperiodicCls c = false ↔ (c = 2 ∨ c = 4 ∨ c = 5)) ∧
    IsAperiodicSixPartition SwapRigidity.aperiodicCls) ∧
  (∀ (F : Type*) [Field F],
    ((ringChar F ≠ 2 ∧ ringChar F ≠ 3) ↔ ((2 : F) ≠ 0 ∧ (3 : F) ≠ 0)) ∧
    ((ringChar F ≠ 2 ∧ ringChar F ≠ 3) ↔ CoprimeToChar F 6))

/-- **`Theorem 2` (Exact Solution `D({0, 1, 3}, {2, 4, 5}) = 25` in Every Characteristic `∉ {2, 3}`).**
For every field `F` with `ringChar F ≠ 2 ∧ ringChar F ≠ 3`:
1. **Single-shift intersection ceiling `≤ 14` & code ceiling `≤ 25`**: For every class-uniform
   code `𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F)` of `SwapRigidity.aperiodicCls` (and more
   generally of any `cls : ZMod 6 → κ` satisfying `IsAperiodicSixPartition cls`),
   * `finrank F (𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1)) ≤ 14`;
   * `2 * finrank F 𝒳 ≤ 36 + 14` (`= 50`);
   * `finrank F 𝒳 ≤ 25`;
2. **Exactness `D({0, 1, 3}, {2, 4, 5}) = 25`**: There exists a class-uniform code `𝒳` of
   dimension `25`, so `25` is the greatest element of
   `{k : ℕ | ∃ 𝒳, SwapRigidity.IsClassUniformCode cls 𝒳 ∧ finrank F 𝒳 = k}` and
   `linearClassUniformMaxDim F 1 cls = 25`. -/
def Extension_Theorem2_AperiodicSixExactSpec : Prop :=
  ∀ (F : Type*) [Field F],
    ringChar F ≠ 2 → ringChar F ≠ 3 →
      (∀ (𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F)),
        SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 →
          finrank F ↥(𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1)) ≤ 14 ∧
          2 * finrank F 𝒳 ≤ 36 + 14 ∧
          finrank F 𝒳 ≤ 25) ∧
      IsGreatest
        {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
          SwapRigidity.IsClassUniformCode SwapRigidity.aperiodicCls 𝒳 ∧ finrank F 𝒳 = k}
        25 ∧
      linearClassUniformMaxDim F 1 SwapRigidity.aperiodicCls = 25 ∧
      (∀ (κ : Type*) (cls : ZMod 6 → κ),
        IsAperiodicSixPartition cls →
          (∀ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
            SwapRigidity.IsClassUniformCode cls 𝒳 →
              finrank F ↥(𝒳 ⊓ 𝒳.comap (SwapRigidity.rot 1)) ≤ 14 ∧
              finrank F 𝒳 ≤ 25) ∧
          IsGreatest
            {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod 6) (ZMod 6) F),
              SwapRigidity.IsClassUniformCode cls 𝒳 ∧ finrank F 𝒳 = k}
            25 ∧
          linearClassUniformMaxDim F 1 cls = 25)

end BoundedArityDecoders
