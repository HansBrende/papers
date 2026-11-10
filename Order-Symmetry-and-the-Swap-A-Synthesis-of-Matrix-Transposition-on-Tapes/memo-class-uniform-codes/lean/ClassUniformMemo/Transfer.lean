import SwapRigidity.ClassUniform
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-!
# Class-uniform codes from certificates over a ring

A *certificate* (`Certificate`) describes a class-uniform code by finite data over a commutative
ring `R`: generators, the coefficients of one decoder per class, a common denominator `scale` of
the decoders, and for every generator a private position where it equals `pivotScale` and every
other generator vanishes.  Two finite facts make a certificate valid: the rule holds for every
generator after multiplying by `scale` (`Certificate.RowsHold`), and the private positions behave as
stated (`Certificate.PivotsHold`).  Both are checked by `decide` for the concrete certificates of
`ClassUniformMemo.RationalData`.

A valid certificate gives a code over every field `F` reached by a ring homomorphism `φ : R →+* F`
in which the two scales do not vanish: the span of the images of the generators is a class-uniform
code (`Certificate.isClassUniformCode`) of dimension the number of generators
(`Certificate.finrank_code`).  With `R = ℤ` this reduces a rational code modulo every prime that
divides neither scale; with `R = ZMod p` it carries a code over `ZMod p` to every field of
characteristic `p`.

## Main definitions

* `Certificate`, `Certificate.RowsHold`, `Certificate.PivotsHold`.
* `Certificate.genMap`, `Certificate.code`, `Certificate.dec`: the generators, the code and the
  decoders over `F`.

## Main results

* `Certificate.genMap_row`, `Certificate.row_eq_dec_of_mem`: the rule holds on the code.
* `Certificate.isClassUniformCode`: the code is class-uniform.
* `Certificate.linearIndependent_genMap`, `Certificate.finrank_code`: its dimension.
-/

namespace ClassUniformMemo

open Module SwapRigidity

/-- Finite data describing a class-uniform code over a commutative ring `R`: `m` generators of
size `n × n`, a class for every row, and the coefficients of one decoder per class. -/
structure Certificate (R : Type*) [CommRing R] (n m : ℕ) (κ : Type*) where
  /-- The class of every row. -/
  cls : ZMod n → κ
  /-- The generators. -/
  gen : Fin m → Matrix (ZMod n) (ZMod n) R
  /-- The decoder of the class `b`, multiplied by `scale`: output coordinate `r` is the sum of
  `a * Y i j` over the entries `((i, j), a)` of `coef b r`. -/
  coef : κ → ZMod n → List ((ZMod n × ZMod n) × R)
  /-- The common denominator of the decoders. -/
  scale : R
  /-- The private position of every generator. -/
  pivot : Fin m → ZMod n × ZMod n
  /-- The value of every generator at its private position. -/
  pivotScale : R

namespace Certificate

variable {R : Type*} [CommRing R] {n m : ℕ} {κ : Type*} (C : Certificate R n m κ)

/-- The rule holds for every generator, multiplied by `scale`: for every row `c` and column `r`,
`scale * gen k c r = ∑ ((i, j), a) ∈ coef (cls c) r, a * gen k i (j + c)`. -/
def RowsHold : Prop :=
  ∀ k c r, C.scale * C.gen k c r =
    ((C.coef (C.cls c) r).map fun p => p.2 * C.gen k p.1.1 (p.1.2 + c)).sum

/-- At the private position of generator `l`, generator `l` equals `pivotScale` and every other
generator vanishes. -/
def PivotsHold : Prop :=
  ∀ k l, C.gen k (C.pivot l).1 (C.pivot l).2 = if k = l then C.pivotScale else 0

variable {F : Type*} [Field F] (φ : R →+* F)

/-- The generators, mapped to `F` by `φ`. -/
def genMap (k : Fin m) : Matrix (ZMod n) (ZMod n) F :=
  (C.gen k).map φ

/-- The code over `F`: the span of the mapped generators. -/
def code : Submodule F (Matrix (ZMod n) (ZMod n) F) :=
  Submodule.span F (Set.range (C.genMap φ))

/-- A sum of a list of products, with a common factor pulled out. -/
theorem sum_map_mul_mul (L : List ((ZMod n × ZMod n) × R)) (a : F)
    (Y : Matrix (ZMod n) (ZMod n) F) :
    (L.map fun p => φ p.2 * (a * Y p.1.1 p.1.2)).sum =
      a * (L.map fun p => φ p.2 * Y p.1.1 p.1.2).sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- The decoder of the class `b` over `F`: output coordinate `r` of `dec φ b Y` is
`(φ scale)⁻¹ * ∑ ((i, j), a) ∈ coef b r, φ a * Y i j`. -/
def dec (b : κ) : Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F) where
  toFun Y r := (φ C.scale)⁻¹ * ((C.coef b r).map fun p => φ p.2 * Y p.1.1 p.1.2).sum
  map_add' Y Z := by
    funext r
    simp only [Matrix.add_apply, Pi.add_apply, mul_add, List.sum_map_add]
  map_smul' a Y := by
    funext r
    simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [sum_map_mul_mul]
    ring

/-- The coordinates of a decoder over `F`. -/
theorem dec_apply (b : κ) (Y : Matrix (ZMod n) (ZMod n) F) (r : ZMod n) :
    C.dec φ b Y r = (φ C.scale)⁻¹ * ((C.coef b r).map fun p => φ p.2 * Y p.1.1 p.1.2).sum :=
  rfl

variable {C φ}

/-- Every mapped generator satisfies the rule, if the rule holds over `R` and `φ scale ≠ 0`. -/
theorem genMap_row (hrow : C.RowsHold) (hscale : φ C.scale ≠ 0) (k : Fin m) (c : ZMod n) :
    C.genMap φ k c = C.dec φ (C.cls c) (rot c (C.genMap φ k)) := by
  funext r
  have h := congrArg φ (hrow k c r)
  rw [map_mul, map_list_sum, List.map_map] at h
  rw [dec_apply, eq_inv_mul_iff_mul_eq₀ hscale]
  simp only [genMap, Matrix.map_apply, rot_apply]
  rw [h]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [map_mul]

/-- The rule holds on the code over `F`. -/
theorem row_eq_dec_of_mem (hrow : C.RowsHold) (hscale : φ C.scale ≠ 0)
    {X : Matrix (ZMod n) (ZMod n) F} (hX : X ∈ C.code φ) (c : ZMod n) :
    X c = C.dec φ (C.cls c) (rot c X) := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨k, rfl⟩ := hX
    exact genMap_row hrow hscale k c
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | add X Y _ _ hX hY =>
    rw [map_add, map_add, ← hX, ← hY]
    rfl
  | smul a X _ hX =>
    rw [map_smul, map_smul, ← hX]
    rfl

/-- **A valid certificate gives a class-uniform code** over every field `F` reached by a ring
homomorphism `φ` with `φ scale ≠ 0`. -/
theorem isClassUniformCode (hrow : C.RowsHold) (hscale : φ C.scale ≠ 0) :
    IsClassUniformCode C.cls (C.code φ) :=
  ⟨C.dec φ, fun _ hX c => row_eq_dec_of_mem hrow hscale hX c⟩

/-- The mapped generators are linearly independent if `φ pivotScale ≠ 0`: the projection to the
private positions, divided by `φ pivotScale`, sends them to the standard basis vectors. -/
theorem linearIndependent_genMap (hpiv : C.PivotsHold) (hps : φ C.pivotScale ≠ 0) :
    LinearIndependent F (C.genMap φ) := by
  let ψ : Matrix (ZMod n) (ZMod n) F →ₗ[F] (Fin m → F) :=
    { toFun := fun X l => (φ C.pivotScale)⁻¹ * X (C.pivot l).1 (C.pivot l).2
      map_add' := fun X Y => by
        funext l
        simp [mul_add]
      map_smul' := fun a X => by
        funext l
        simp [mul_left_comm] }
  have hψ : ψ ∘ C.genMap φ = fun k => Pi.single k (1 : F) := by
    funext k l
    change (φ C.pivotScale)⁻¹ * φ (C.gen k (C.pivot l).1 (C.pivot l).2) = _
    rw [hpiv, Pi.single_apply]
    by_cases hkl : k = l
    · subst hkl
      simp [inv_mul_cancel₀ hps]
    · simp [hkl, Ne.symm hkl]
  refine LinearIndependent.of_comp ψ ?_
  rw [hψ]
  exact Pi.linearIndependent_single_one (Fin m) F

/-- **The dimension of the code** is the number of generators, if `φ pivotScale ≠ 0`. -/
theorem finrank_code (hpiv : C.PivotsHold) (hps : φ C.pivotScale ≠ 0) :
    finrank F (C.code φ) = m := by
  rw [code, finrank_span_eq_card (linearIndependent_genMap hpiv hps), Fintype.card_fin]

end Certificate

end ClassUniformMemo
