import SwapRigidity.AperiodicExampleData
import SwapRigidity.ClassUniform
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-!
# A class-uniform code of dimension 25 for two classes that are not intervals

For a colouring `cls` of the rows `ZMod n`, `IsClassUniformCode.two_mul_finrank_le` bounds a
class-uniform code by `2 * dim 𝒳 ≤ n ^ 2 + n * |S|`, where `S` contains every row at which the
class changes.  If the classes are `M` cyclic intervals this is `2 * dim 𝒳 ≤ n ^ 2 + n * M`.

This file shows that the number of classes alone does not give that bound.  For `n = 6`, the
field `ZMod 2` and the two classes `{0, 1, 3}` and `{2, 4, 5}` of `ZMod 6`, it exhibits a
class-uniform code of dimension `25`, and `6 ^ 2 + 6 * 2 = 48 < 50 = 2 * 25`.  (The class changes
at the four rows `0, 2, 3, 4`, so `two_mul_finrank_le` gives `2 * 25 ≤ 6 ^ 2 + 6 * 4` here.)

The code was found by a SAT solver.  Its data are in `SwapRigidity.AperiodicExampleData`, which
`tools/gen_aperiodic_example.py` writes from the certificate `tools/data/aperiodic_d6_dim25.json`.
Nothing is taken on trust from the certificate or from the generator: the finite facts about the
data (`aperiodicCls_eq_true_iff`, `aperiodicCls_eq_false_iff`, `aperiodicGen_row` and
`aperiodicGen_pivot`) are proved by `decide`.

## Main definitions

* `aperiodicGen`: the 25 generators, as `6 × 6` matrices over `ZMod 2`.
* `aperiodicCode`: their span.
* `aperiodicDec`: the two decoders.  Row `c` of a matrix `X` of the code is
  `aperiodicDec (aperiodicCls c) (rot c X)`; in coordinates,
  `X c r = ∑ (i, j) ∈ aperiodicDecSupport (aperiodicCls c) r, X i (j + c)`.

## Main results

* `aperiodicCls_eq_true_iff`, `aperiodicCls_eq_false_iff`: the classes are `{0, 1, 3}` and
  `{2, 4, 5}`.
* `row_eq_aperiodicDec_of_mem`, `row_apply_of_mem_aperiodicCode`: the rule holds on the code.
* `isClassUniformCode_aperiodicCode`: the code is class-uniform.
* `linearIndependent_aperiodicGen`, `finrank_aperiodicCode`: the code has dimension `25`.
* `exists_classUniformCode_gt`: for two classes, `n ^ 2 + n * 2 < 2 * dim 𝒳` is possible.
-/

namespace SwapRigidity

open Module

/-! ### The classes -/

/-- The class `true` of the example is `{0, 1, 3}`. -/
theorem aperiodicCls_eq_true_iff (c : ZMod 6) :
    aperiodicCls c = true ↔ c = 0 ∨ c = 1 ∨ c = 3 := by
  revert c
  decide

/-- The class `false` of the example is `{2, 4, 5}`. -/
theorem aperiodicCls_eq_false_iff (c : ZMod 6) :
    aperiodicCls c = false ↔ c = 2 ∨ c = 4 ∨ c = 5 := by
  revert c
  decide

/-! ### The code and its decoders -/

/-- The 25 generators of the example code: `aperiodicGen k` is the `6 × 6` matrix over `ZMod 2`
with entry `1` at the positions listed in entry `k` of `aperiodicGenSupports` and `0` elsewhere. -/
def aperiodicGen (k : Fin 25) : Matrix (ZMod 6) (ZMod 6) (ZMod 2) :=
  Matrix.of fun i j => if (i, j) ∈ aperiodicGenSupports.getD k [] then 1 else 0

/-- The example code: the span of the 25 matrices `aperiodicGen k`. -/
def aperiodicCode : Submodule (ZMod 2) (Matrix (ZMod 6) (ZMod 6) (ZMod 2)) :=
  Submodule.span (ZMod 2) (Set.range aperiodicGen)

/-- The generators lie in the example code. -/
theorem aperiodicGen_mem_aperiodicCode (k : Fin 25) : aperiodicGen k ∈ aperiodicCode :=
  Submodule.subset_span (Set.mem_range_self k)

/-- The decoder of the class `k` of the example: output coordinate `r` of `aperiodicDec k Y` is
the sum of the entries `Y i j` over the positions `(i, j)` listed in `aperiodicDecSupport k r`. -/
def aperiodicDec (k : Bool) :
    Matrix (ZMod 6) (ZMod 6) (ZMod 2) →ₗ[ZMod 2] (ZMod 6 → ZMod 2) where
  toFun Y r := ((aperiodicDecSupport k r).map fun p => Y p.1 p.2).sum
  map_add' Y Z := by
    funext r
    simp only [Matrix.add_apply, Pi.add_apply, List.sum_map_add]
  map_smul' a Y := by
    funext r
    simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      List.sum_map_mul_left]

/-- The coordinates of a decoder of the example. -/
theorem aperiodicDec_apply (k : Bool) (Y : Matrix (ZMod 6) (ZMod 6) (ZMod 2)) (r : ZMod 6) :
    aperiodicDec k Y r = ((aperiodicDecSupport k r).map fun p => Y p.1 p.2).sum :=
  rfl

/-! ### The rule -/

/-- Every generator satisfies the rule: row `c` of `aperiodicGen k` is the decoder of the class of
`c` applied to the generator with its columns rotated by `c`.  This is a finite check
(`25 * 6 * 6` equations over `ZMod 2`), done by `decide`. -/
theorem aperiodicGen_row (k : Fin 25) (c : ZMod 6) :
    aperiodicGen k c = aperiodicDec (aperiodicCls c) (rot c (aperiodicGen k)) := by
  have h : (fun k c => aperiodicGen k c) =
      fun k c => aperiodicDec (aperiodicCls c) (rot c (aperiodicGen k)) := by
    decide
  exact congrFun (congrFun h k) c

/-- The rule holds on the example code: row `c` of every `X` in the code is the decoder of the
class of `c` applied to `X` with its columns rotated by `c`. -/
theorem row_eq_aperiodicDec_of_mem {X : Matrix (ZMod 6) (ZMod 6) (ZMod 2)}
    (hX : X ∈ aperiodicCode) (c : ZMod 6) : X c = aperiodicDec (aperiodicCls c) (rot c X) := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨k, rfl⟩ := hX
    exact aperiodicGen_row k c
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | add X Y _ _ hX hY =>
    rw [map_add, map_add, ← hX, ← hY]
    rfl
  | smul a X _ hX =>
    rw [map_smul, map_smul, ← hX]
    rfl

/-- The rule of the example in coordinates: for `X` in the code,
`X c r = ∑ (i, j) ∈ aperiodicDecSupport (aperiodicCls c) r, X i (j + c)`. -/
theorem row_apply_of_mem_aperiodicCode {X : Matrix (ZMod 6) (ZMod 6) (ZMod 2)}
    (hX : X ∈ aperiodicCode) (c r : ZMod 6) :
    X c r = ((aperiodicDecSupport (aperiodicCls c) r).map fun p => X p.1 (p.2 + c)).sum :=
  congrFun (row_eq_aperiodicDec_of_mem hX c) r

/-- The example code is a class-uniform code for the classes `{0, 1, 3}` and `{2, 4, 5}`. -/
theorem isClassUniformCode_aperiodicCode : IsClassUniformCode aperiodicCls aperiodicCode :=
  ⟨aperiodicDec, fun _ hX c => row_eq_aperiodicDec_of_mem hX c⟩

/-! ### The dimension -/

/-- The private position of the generator `k`: entry `k` of `aperiodicPivots`. -/
def aperiodicPivot (k : Fin 25) : ZMod 6 × ZMod 6 :=
  aperiodicPivots.getD k (0, 0)

/-- At the private position of the generator `l`, the generator `l` is `1` and every other
generator is `0`.  This is a finite check (`25 * 25` entries), done by `decide`. -/
theorem aperiodicGen_pivot (k l : Fin 25) :
    aperiodicGen k (aperiodicPivot l).1 (aperiodicPivot l).2 = if k = l then 1 else 0 := by
  have h : (fun k l => aperiodicGen k (aperiodicPivot l).1 (aperiodicPivot l).2) =
      fun k l => if k = l then 1 else 0 := by
    decide
  exact congrFun (congrFun h k) l

/-- The 25 generators of the example code are linearly independent: the projection to the 25
private positions sends them to the standard basis vectors. -/
theorem linearIndependent_aperiodicGen : LinearIndependent (ZMod 2) aperiodicGen := by
  let φ : Matrix (ZMod 6) (ZMod 6) (ZMod 2) →ₗ[ZMod 2] (Fin 25 → ZMod 2) :=
    { toFun := fun X l => X (aperiodicPivot l).1 (aperiodicPivot l).2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : φ ∘ aperiodicGen = fun k => Pi.single k (1 : ZMod 2) := by
    funext k l
    change aperiodicGen k (aperiodicPivot l).1 (aperiodicPivot l).2 = _
    rw [aperiodicGen_pivot, Pi.single_apply]
    simp only [eq_comm]
  refine LinearIndependent.of_comp φ ?_
  rw [hφ]
  exact Pi.linearIndependent_single_one (Fin 25) (ZMod 2)

/-- The example code has dimension `25`. -/
theorem finrank_aperiodicCode : finrank (ZMod 2) aperiodicCode = 25 := by
  rw [aperiodicCode, finrank_span_eq_card linearIndependent_aperiodicGen, Fintype.card_fin]

/-! ### The headline statement -/

/-- **A class-uniform code beyond the interval bound.**  There are a colouring of the rows of
`ZMod 6` with two classes and a class-uniform code `𝒳` over `ZMod 2` for it with
`6 ^ 2 + 6 * 2 < 2 * dim 𝒳`.  So the bound `2 * dim 𝒳 ≤ n ^ 2 + n * M`, which
`IsClassUniformCode.two_mul_finrank_le` gives for `M` cyclic intervals, fails for `M` arbitrary
classes.  The witness is `aperiodicCode` (dimension `25`) with the classes `{0, 1, 3}` and
`{2, 4, 5}`. -/
theorem exists_classUniformCode_gt :
    ∃ (cls : ZMod 6 → Bool) (𝒳 : Submodule (ZMod 2) (Matrix (ZMod 6) (ZMod 6) (ZMod 2))),
      IsClassUniformCode cls 𝒳 ∧ 6 ^ 2 + 6 * 2 < 2 * Module.finrank (ZMod 2) 𝒳 :=
  ⟨aperiodicCls, aperiodicCode, isClassUniformCode_aperiodicCode, by
    rw [finrank_aperiodicCode]
    norm_num⟩

end SwapRigidity
