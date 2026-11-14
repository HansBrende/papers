import SharedDecoders.Model
import SwapRigidity.ClassUniform
import Mathlib.Algebra.CharP.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Extension Result 1: Linear-Decoder Run-Extension and Multi-Class Ceilings (`Problem 9.1(a)`)

Formal statement specifications for Section 5 of the manuscript (`Theorem 1A` / Theorem 5.2,
sharpness on the alternating coloring in Theorem 5.3, and `Theorem 1B` / Theorems 5.4–5.5 for
`M = 2` and `M ≥ 3` classes):

1. **Multi-Lane Linear Class-Uniform Model & Bridges**:
   * `laneRot`, `IsLinearClassUniformCode`, `linearClassUniformMaxDim`: `b`-lane linear
     class-uniform codes `𝒳 ≤ Matrix (ZMod d) (ZMod d) (Fin b → F)` matching Paper 17
     Definition 6.3 (`def:class-uniform`) and Paper 19 (`SharedDecoders`).
   * `CoprimeToChar` & `Extension_LinearModelAndCharBridgesSpec`: at `b = 1`,
     `IsLinearClassUniformCode` is equivalent (preserving code dimension and single-shift
     intersection dimension) to `SwapRigidity.IsClassUniformCode`; for all `b ≥ 1`, every linear
     class-uniform code determines a `SharedDecoders.IsSharedCode` with single-shift intersection
     in `ShiftLinkCovarianceSpace`; and for `n ≥ 1`, `CoprimeToChar F n` (`gcd(n, char F) = 1`)
     holds iff `((n : ℕ) : F) ≠ 0`.

2. **Exact Single-Shift Bound & Sharpness (`Theorem 1A`)**:
   * `shiftOrbit`, `orbitClassCard`, `orbitRunCount`, `theorem1ASingleShiftBound`: exact orbit
     parameters `g_s = gcd(d, s)`, `n = d / g_s`, `d_{m,a} = |J_m ∩ O_a|`, and
     `T_{m,a} = |{c ∈ J_m ∩ O_a : c + s ∉ J_m}|` along the `g_s` cycles of `c ↦ c + s`.
   * `Extension_Theorem1A_SingleShiftSpec`: exact single-shift intersection bound on
     `dim_F (𝒳 ∩ σ^{-s} 𝒳)` whenever `gcd(d / gcd(d, s), char F) = 1`.
   * `altTwoColoring`, `ShiftLinkCovarianceSpace`, `alternatingSharpDecoder`, &
     `Extension_Theorem1A_AlternatingSharpnessSpec`: on `p(c) = c mod 2` (`d = 2m`, `b = 1`,
     `s = 1`), `Theorem 1A` evaluates to `m^2 + 3m = (1/4) d^2 + (3/2) d` (whereas
     `dim H_{0,1} = (2m)^2 = d^2`), and an explicit decoder attains `dim(𝒳 ∩ σ^{-1} 𝒳) = m^2 + 3m`
     with equality.

3. **Universal Two-Class & Multi-Class Ceilings (`Theorem 1B`)**:
   * `shiftTransitionCount` & `Extension_Theorem1B_TwoClassSpec`: per-shift Cauchy–Schwarz bound
     `dim(𝒳 ∩ σ^{-s} 𝒳) ≤ b ((1/2) Q_s d - (1/4) Q_s^2 + (1/2) g_s Q_s + g_s d)` and universal
     two-class ceiling `D(𝒫) ≤ (19/32) b d^2 + (3/2) b d^(3/2)` when `gcd(d, char F) = 1`, together
     with the barrier comparisons `19/32 = 38/64 < 5/8 = 40/64 < 41/64`.
   * `multiClassLeadingCoeff` & `Extension_Theorem1B_MultiClassPrimeSpec`: simplex maximization of
     `α(1 - α)^2(1 - α/2)` at `α_m = 1/M`, prime-`d` ceiling
     `D(𝒫) ≤ (1 - 5/(4M) + 1/M^2 - 1/(4M^3)) b d^2 + O(b M d)` for `M ≥ 3` and prime
     `d ≠ char F`, and strict improvement over Theorem FL's `1 - 1/(2M)` for every `M ≥ 2`
     (including `37/54 < 5/6` at `M = 3` and `191/256 < 7/8` at `M = 4`).
-/

namespace BoundedArityDecoders

open Module
open scoped BigOperators

section LinearModelDefs

/-- Column rotation by `s : ZMod d` on `d × d` matrices with `b`-lane entries `Fin b → F`:
`(laneRot s X) i j = X i (j + s)`, matching `SwapRigidity.rot` and `SharedDecoders.rot`. -/
def laneRot {F : Type*} [Semiring F] {d b : ℕ} (s : ZMod d) :
    Matrix (ZMod d) (ZMod d) (Fin b → F) →ₗ[F] Matrix (ZMod d) (ZMod d) (Fin b → F) where
  toFun X := Matrix.of fun i j => X i (j + s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem laneRot_apply {F : Type*} [Semiring F] {d b : ℕ} (s : ZMod d)
    (X : Matrix (ZMod d) (ZMod d) (Fin b → F)) (i j : ZMod d) :
    laneRot s X i j = X i (j + s) :=
  rfl

/-- Canonical `F`-linear equivalence between `1`-lane matrices `Matrix (ZMod d) (ZMod d) (Fin 1 → F)`
and scalar matrices `Matrix (ZMod d) (ZMod d) F`. -/
def laneOneMatrixEquiv (F : Type*) [Semiring F] (d : ℕ) :
    Matrix (ZMod d) (ZMod d) (Fin 1 → F) ≃ₗ[F] Matrix (ZMod d) (ZMod d) F where
  toFun X := Matrix.of fun i j => X i j 0
  invFun Y := Matrix.of fun i j _ => Y i j
  left_inv X := by
    ext i j u
    fin_cases u
    rfl
  right_inv Y := by
    ext i j
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical `F`-linear equivalence between `Matrix (ZMod d) (ZMod d) (Fin b → F)` and
`SharedDecoders.State d (Fin b → F)`. -/
def matrixToSharedStateEquiv (F : Type*) [Semiring F] (d b : ℕ) :
    Matrix (ZMod d) (ZMod d) (Fin b → F) ≃ₗ[F] SharedDecoders.State d (Fin b → F) where
  toFun X i j := X i j
  invFun Y := Matrix.of Y
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multi-lane **linear class-uniform code** (Paper 17 Definition 6.3 with lane width `b`):
there exist `F`-linear decoders `dec k : Mat_d(F^b) →ₗ[F] (F^b)^{ZMod d}`, one per class `k : κ`,
such that row `c` of every `X ∈ 𝒳` equals `dec (p c) (laneRot c X)`. -/
def IsLinearClassUniformCode {F : Type*} [Field F] {d b : ℕ} {κ : Type*}
    (p : ZMod d → κ) (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F))) : Prop :=
  ∃ dec : κ → (Matrix (ZMod d) (ZMod d) (Fin b → F) →ₗ[F] (ZMod d → Fin b → F)),
    ∀ X ∈ 𝒳, ∀ c : ZMod d, X c = dec (p c) (laneRot c X)

/-- Maximum `F`-dimension `D(𝒫)` over all `b`-lane linear class-uniform codes for partition `p`. -/
noncomputable def linearClassUniformMaxDim (F : Type*) [Field F] {d : ℕ} (b : ℕ) {κ : Type*}
    (p : ZMod d → κ) : ℕ :=
  sSup {k : ℕ | ∃ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
    IsLinearClassUniformCode p 𝒳 ∧ finrank F 𝒳 = k}

/-- Arithmetic coprimality `gcd(n, char F) = 1`: in characteristic `0` (`ringChar F = 0`) no
positive integer is divisible by `char F`; in prime characteristic `p = ringChar F > 0`,
`Nat.Coprime n p` holds. -/
def CoprimeToChar (F : Type*) [Field F] (n : ℕ) : Prop :=
  ringChar F = 0 ∨ Nat.Coprime n (ringChar F)

/-- Two-shift covariance subspace `H_{0, s}` for partition `p` and shift `s`: matrices `X` such
that whenever rows `c, c'` have the same class `p c = p c'` and `c + δ = c' + δ'` with
`δ, δ' ∈ {0, s}`, row `c'` shifted by `δ'` equals row `c` shifted by `δ`. -/
def ShiftLinkCovarianceSpace (F : Type*) [Field F] (d b : ℕ) {κ : Type*}
    (p : ZMod d → κ) (s : ZMod d) :
    Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)) where
  carrier := {X | ∀ (c c' δ δ' : ZMod d),
    δ ∈ ({0, s} : Finset (ZMod d)) →
    δ' ∈ ({0, s} : Finset (ZMod d)) →
    p c = p c' → c + δ = c' + δ' →
    ∀ j : ZMod d, X c' (j + δ') = X c (j + δ)}
  add_mem' {X Y} hX hY c c' δ δ' hδ hδ' hp hc j := by
    simp [hX c c' δ δ' hδ hδ' hp hc j, hY c c' δ δ' hδ hδ' hp hc j]
  zero_mem' _ _ _ _ _ _ _ _ _ := rfl
  smul_mem' a {X} hX c c' δ δ' hδ hδ' hp hc j := by
    simp [hX c c' δ δ' hδ hδ' hp hc j]

end LinearModelDefs

section OrbitAndSharpnessDefs

/-- Step-size gcd `g_s = gcd(d, s.val)` for `s : ZMod d` (`1 ≤ g_s ≤ d` when `d ≥ 1`). -/
def shiftGcd (d : ℕ) (s : ZMod d) : ℕ :=
  Nat.gcd d s.val

/-- Cycle length `n_s = d / gcd(d, s.val)` of `c ↦ c + s` on `ZMod d`. -/
def shiftOrbitLen (d : ℕ) (s : ZMod d) : ℕ :=
  d / shiftGcd d s

/-- The `a`-th cycle `O_a = {c ∈ ZMod d : c.val % g_s = a}` of `c ↦ c + s` (`0 ≤ a < g_s`). -/
def shiftOrbit {d : ℕ} [NeZero d] (s : ZMod d) (a : Fin (shiftGcd d s)) : Finset (ZMod d) :=
  Finset.univ.filter fun c : ZMod d => c.val % shiftGcd d s = a.val

/-- Class occupancy `d_{m, a} = |J_m ∩ O_a|` in cycle `O_a`. -/
def orbitClassCard {d : ℕ} [NeZero d] {M : ℕ} (p : ZMod d → Fin M) (s : ZMod d)
    (m : Fin M) (a : Fin (shiftGcd d s)) : ℕ :=
  ((shiftOrbit s a).filter fun c => p c = m).card

/-- Run-endpoint count `T_{m, a} = |{c ∈ J_m ∩ O_a : c + s ∉ J_m}|` in cycle `O_a`. -/
def orbitRunCount {d : ℕ} [NeZero d] {M : ℕ} (p : ZMod d → Fin M) (s : ZMod d)
    (m : Fin M) (a : Fin (shiftGcd d s)) : ℕ :=
  ((shiftOrbit s a).filter fun c => p c = m ∧ p (c + s) ≠ m).card

/-- Exact real-valued RHS of `Theorem 1A`:
`b g_s ∑_{a=0}^{g_s - 1} ∑_{m=0}^{M - 1} (T_{m,a}(n - d_{m,a}) - T_{m,a}^2 / 2 + T_{m,a} / 2) + b g_s d`. -/
noncomputable def theorem1ASingleShiftBound {d : ℕ} [NeZero d] {M : ℕ}
    (b : ℕ) (p : ZMod d → Fin M) (s : ZMod d) : ℝ :=
  let g := shiftGcd d s
  let n := shiftOrbitLen d s
  (b * g : ℝ) *
    ∑ a : Fin g, ∑ m : Fin M,
      ((orbitRunCount p s m a : ℝ) * ((n : ℝ) - (orbitClassCard p s m a : ℝ)) -
        (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ)) +
    (b * g * d : ℝ)

/-- Total shift transition count `Q_s = |{c ∈ ZMod d : p(c) ≠ p(c + s)}|`. -/
def shiftTransitionCount {d : ℕ} [NeZero d] {κ : Type*} [DecidableEq κ]
    (p : ZMod d → κ) (s : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : ZMod d => p c ≠ p (c + s)).card

/-- Alternating two-class coloring `p(c) = c mod 2` on `ZMod (2 * m)`. -/
def altTwoColoring (m : ℕ) [NeZero m] (c : ZMod (2 * m)) : Fin 2 :=
  ⟨c.val % 2, Nat.mod_lt _ (by omega)⟩

/-- Explicit `{0, 1}` representation in position coordinates of the symmetric Fourier decoder on
`ZMod (2 * m)` for `altTwoColoring m`, attaining `dim(𝒳 ∩ σ⁻¹ 𝒳) = m^2 + 3m`:
* Class `0` (even rows): coordinate `u` reads `Y (u, 0)` if `u` is even, and `Y (u + 1, -1)` if `u`
  is odd;
* Class `1` (odd rows): coordinate `u` reads `Y (u + 1, -1)` if `u` is even, and `Y (u + 2, -2)` if
  `u` is odd. -/
def alternatingSharpDecoder (F : Type*) [Ring F] (m : ℕ) [NeZero m] (cls : Fin 2) :
    Matrix (ZMod (2 * m)) (ZMod (2 * m)) F →ₗ[F] (ZMod (2 * m) → F) where
  toFun Y u :=
    if cls.val = 0 then
      if u.val % 2 = 0 then Y u 0 else Y (u + 1) (-1)
    else
      if u.val % 2 = 0 then Y (u + 1) (-1) else Y (u + 2) (-2)
  map_add' Y Z := by
    funext u
    by_cases hc : cls.val = 0 <;> by_cases hu : u.val % 2 = 0 <;> simp [hc, hu]
  map_smul' a Y := by
    funext u
    by_cases hc : cls.val = 0 <;> by_cases hu : u.val % 2 = 0 <;> simp [hc, hu]

/-- Explicit linear class-uniform code cut out by `alternatingSharpDecoder F m` on `ZMod (2 * m)`. -/
def alternatingSharpCode (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    Submodule F (Matrix (ZMod (2 * m)) (ZMod (2 * m)) F) where
  carrier := {X | ∀ c : ZMod (2 * m),
    X c = alternatingSharpDecoder F m (altTwoColoring m c) (SwapRigidity.rot c X)}
  add_mem' {X Y} hX hY c := by
    funext u
    have hXc := congrFun (hX c) u
    have hYc := congrFun (hY c) u
    simp only [Matrix.add_apply, map_add, Pi.add_apply] at hXc hYc ⊢
    exact congrArg₂ (· + ·) hXc hYc
  zero_mem' c := by
    funext u
    have h0 : SwapRigidity.rot c (0 : Matrix (ZMod (2 * m)) (ZMod (2 * m)) F) = 0 := map_zero _
    rw [h0, map_zero]
    rfl
  smul_mem' a {X} hX c := by
    funext u
    have hXc := congrFun (hX c) u
    simp only [Matrix.smul_apply, map_smul, Pi.smul_apply] at hXc ⊢
    exact congrArg (a • ·) hXc

/-- Leading quadratic coefficient `1 - 5/(4M) + 1/M^2 - 1/(4M^3)` of `Theorem 1B` for `M` classes. -/
noncomputable def multiClassLeadingCoeff (M : ℕ) : ℝ :=
  1 - 5 / (4 * (M : ℝ)) + 1 / (M : ℝ) ^ 2 - 1 / (4 * (M : ℝ) ^ 3)

end OrbitAndSharpnessDefs

/-! ### Statement Specifications for Result 1 -/

/-- **Model & Characteristic Bridges (`Result 1` Preliminaries).**
1. At `b = 1`, `IsLinearClassUniformCode` corresponds bijectively under `laneOneMatrixEquiv` to
   `SwapRigidity.IsClassUniformCode`, preserving both `finrank F 𝒳` and
   `finrank F (𝒳 ⊓ 𝒳.comap (rot s))`;
2. Every `b`-lane linear class-uniform code `(𝒳 : Set _)` satisfies `SharedDecoders.IsSharedCode`
   and has single-shift intersection `𝒳 ⊓ 𝒳.comap (laneRot s) ≤ ShiftLinkCovarianceSpace F d b p s`;
3. For every `n ≥ 1`, `CoprimeToChar F n` holds if and only if `((n : ℕ) : F) ≠ 0`. -/
def Extension_LinearModelAndCharBridgesSpec : Prop :=
  (∀ (F : Type*) [Field F] (d : ℕ) (κ : Type*) (p : ZMod d → κ)
      (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin 1 → F))) (s : ZMod d),
    let 𝒳₁ := 𝒳.map (laneOneMatrixEquiv F d).toLinearMap
    (IsLinearClassUniformCode p 𝒳 ↔ SwapRigidity.IsClassUniformCode p 𝒳₁) ∧
    finrank F 𝒳₁ = finrank F 𝒳 ∧
    finrank F ↥(𝒳₁ ⊓ 𝒳₁.comap (SwapRigidity.rot s)) =
      finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s))) ∧
  (∀ (F : Type*) [Field F] (d b : ℕ) (κ : Type*) (p : ZMod d → κ)
      (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F))) (s : ZMod d),
    IsLinearClassUniformCode p 𝒳 →
      SharedDecoders.IsSharedCode F p (𝒳.map (matrixToSharedStateEquiv F d b).toLinearMap) ∧
      𝒳 ⊓ 𝒳.comap (laneRot s) ≤ ShiftLinkCovarianceSpace F d b p s) ∧
  (∀ (F : Type*) [Field F] (n : ℕ) [NeZero n],
    CoprimeToChar F n ↔ ((n : ℕ) : F) ≠ 0)

/-- **`Theorem 1A` (Exact Single-Shift Run-Extension Bound for Linear Decoders).**
For every field `F`, `d ≥ 1`, `M ≥ 1`, lane width `b ≥ 1`, partition `p : ZMod d → Fin M`, and
shift `s : ZMod d` with `gcd(d / gcd(d, s), char F) = 1`:
1. In every cycle `O_a` (`0 ≤ a < g_s`) and class `m`, `T_{m, a} ≤ n_s - d_{m, a}`;
2. Every `b`-lane linear class-uniform code `𝒳` for `p` satisfies
   `dim_F (𝒳 ∩ σ^{-s} 𝒳) ≤ theorem1ASingleShiftBound b p s`. -/
def Extension_Theorem1A_SingleShiftSpec : Prop :=
  ∀ (F : Type*) [Field F] (d M b : ℕ) [NeZero d] [NeZero M] [NeZero b]
    (p : ZMod d → Fin M) (s : ZMod d),
    (∀ (a : Fin (shiftGcd d s)) (m : Fin M),
      orbitRunCount p s m a ≤ shiftOrbitLen d s - orbitClassCard p s m a) ∧
    (CoprimeToChar F (shiftOrbitLen d s) →
      ∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
        IsLinearClassUniformCode p 𝒳 →
          (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤ theorem1ASingleShiftBound b p s)

/-- **Sharpness of `Theorem 1A` on the Alternating Coloring (`p(c) = c mod 2`, `d = 2m`, `b = 1`, `s = 1`).**
For every `m ≥ 1`:
1. `theorem1ASingleShiftBound 1 (altTwoColoring m) 1 = (m^2 + 3*m : ℝ) = (1/4) * (2*m)^2 + (3/2) * (2*m)`;
2. Over every field `F`, the nonlinear shift-link covariance space
   `H_{0,1} = ShiftLinkCovarianceSpace F (2 * m) 1 (altTwoColoring m) 1` has full dimension
   `(2 * m) ^ 2`;
3. Over every field `F`, `alternatingSharpCode F m` is a linear class-uniform code for
   `altTwoColoring m` (of code dimension `2 * m * (m + 1)`) attaining
   `finrank F (alternatingSharpCode F m ⊓ (alternatingSharpCode F m).comap (SwapRigidity.rot 1)) = m^2 + 3*m`
   with exact equality (matching `Theorem 1A` whenever `CoprimeToChar F (2 * m)`). -/
def Extension_Theorem1A_AlternatingSharpnessSpec : Prop :=
  ∀ (m : ℕ) [NeZero m],
    haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
    (theorem1ASingleShiftBound 1 (altTwoColoring m) (1 : ZMod (2 * m)) = (m ^ 2 + 3 * m : ℝ) ∧
      ((m ^ 2 + 3 * m : ℝ) =
        (1 / 4 : ℝ) * ((2 * m : ℕ) : ℝ) ^ 2 + (3 / 2 : ℝ) * ((2 * m : ℕ) : ℝ))) ∧
    (∀ (F : Type*) [Field F],
      finrank F (ShiftLinkCovarianceSpace F (2 * m) 1 (altTwoColoring m) 1) = (2 * m) ^ 2 ∧
      SwapRigidity.IsClassUniformCode (altTwoColoring m) (alternatingSharpCode F m) ∧
      finrank F (alternatingSharpCode F m) = 2 * m * (m + 1) ∧
      finrank F ↥(alternatingSharpCode F m ⊓
        (alternatingSharpCode F m).comap (SwapRigidity.rot 1)) = m ^ 2 + 3 * m)

/-- **`Theorem 1B`, Part 1 (Per-Shift Cauchy–Schwarz Bound & Universal `19/32` Two-Class Ceiling).**
1. **Per-shift bound (`M = 2`)**: For every field `F`, `d ≥ 1`, `b ≥ 1`, `p : ZMod d → Fin 2`,
   shift `s : ZMod d` with `CoprimeToChar F (d / gcd(d, s))`, and linear class-uniform code `𝒳`,
   `dim_F (𝒳 ∩ σ^{-s} 𝒳) ≤ b * ((1/2) Q_s d - (1/4) Q_s^2 + (1/2) g_s Q_s + g_s d)`;
2. **Universal `19/32` ceiling**: Whenever `CoprimeToChar F d`, every `b`-lane linear class-uniform
   code `𝒳` for any two-class partition `p : ZMod d → κ` (`Fintype.card κ ≤ 2`, in particular
   `Fin 2`) satisfies `dim_F 𝒳 ≤ (19/32) b d^2 + (3/2) b d^(3/2)`, and hence
   `D(𝒫) = linearClassUniformMaxDim F b p ≤ (19/32) b d^2 + (3/2) b d^(3/2)`;
3. **Barrier comparisons**: `19/32 = 38/64 < 5/8 = 40/64 < 41/64` (strictly below Paper 19's
   `41/64` bound and Paper 19 Theorem C.6's `5/8` nested-component certificate barrier). -/
def Extension_Theorem1B_TwoClassSpec : Prop :=
  (∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d] [NeZero b]
      (p : ZMod d → Fin 2) (s : ZMod d),
    CoprimeToChar F (shiftOrbitLen d s) →
      ∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
        IsLinearClassUniformCode p 𝒳 →
          let Qs : ℝ := (shiftTransitionCount p s : ℝ)
          let gs : ℝ := (shiftGcd d s : ℝ)
          (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤
            (b : ℝ) * ((1 / 2 : ℝ) * Qs * d - (1 / 4 : ℝ) * Qs ^ 2 +
              (1 / 2 : ℝ) * gs * Qs + gs * d)) ∧
  (∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d] [NeZero b]
      (κ : Type*) [Fintype κ] (_hκ : Fintype.card κ ≤ 2) (p : ZMod d → κ),
    CoprimeToChar F d →
      (∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
        IsLinearClassUniformCode p 𝒳 →
          (finrank F 𝒳 : ℝ) ≤
            (19 / 32 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 +
              (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ)) ∧
      (linearClassUniformMaxDim F b p : ℝ) ≤
        (19 / 32 : ℝ) * (b : ℝ) * (d : ℝ) ^ 2 +
          (3 / 2 : ℝ) * (b : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ)) ∧
  ((19 / 32 : ℚ) = 38 / 64 ∧ (5 / 8 : ℚ) = 40 / 64 ∧
    (19 / 32 : ℚ) < 5 / 8 ∧ (5 / 8 : ℚ) < 41 / 64)

/-- **`Theorem 1B`, Part 2 (`M ≥ 3` Classes at Prime `d ≠ char F`, Beating Theorem FL for All `M ≥ 2`).**
1. **Simplex global maximum**: For every `M ≥ 2` and every `α : Fin M → ℝ` with `∀ m, 0 ≤ α m` and
   `∑ m, α m = 1`, letting `f(x) = x * (1 - x)^2 * (1 - x / 2)`,
   `1 / 2 + (1 / 2) * ∑ m, f (α m) ≤ multiClassLeadingCoeff M`, with equality at `α m = 1 / M`
   (and strict inequality whenever `∃ m, α m ≠ 1 / M`);
2. **Prime-`d` multi-class ceiling**: There exists an absolute constant `C > 0` (in fact `C = 1`,
   via `(5 / 4) b d ≤ b M d`) such that for every field `F`, prime `d` with `d ≠ ringChar F`,
   `M ≥ 3`, `b ≥ 1`, `p : ZMod d → Fin M`, and linear class-uniform code `𝒳`,
   `dim_F 𝒳 ≤ multiClassLeadingCoeff M * b * d^2 + C * b * M * d` (and likewise for
   `linearClassUniformMaxDim F b p`);
3. **Strict improvement over Theorem FL for every `M ≥ 2`**:
   * `∀ M ≥ 2`, `multiClassLeadingCoeff M < 1 - 1 / (2 * M)`;
   * At `M = 3`: `multiClassLeadingCoeff 3 = 37 / 54 < 5 / 6`;
   * At `M = 4`: `multiClassLeadingCoeff 4 = 191 / 256 < 7 / 8`. -/
def Extension_Theorem1B_MultiClassPrimeSpec : Prop :=
  (∀ (M : ℕ) (_hM : 2 ≤ M) (α : Fin M → ℝ),
    (∀ m, 0 ≤ α m) → (∑ m, α m = 1) →
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ m : Fin M,
          α m * (1 - α m) ^ 2 * (1 - α m / 2) ≤ multiClassLeadingCoeff M ∧
      ((∃ m, α m ≠ 1 / (M : ℝ)) →
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ m : Fin M,
          α m * (1 - α m) ^ 2 * (1 - α m / 2) < multiClassLeadingCoeff M)) ∧
  (∃ C : ℝ, 0 < C ∧
    ∀ (F : Type*) [Field F] (d M b : ℕ) [NeZero b]
      (_hd : Nat.Prime d) (_hchar : d ≠ ringChar F) (_hM : 3 ≤ M)
      (p : ZMod d → Fin M),
      (∀ 𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)),
        IsLinearClassUniformCode p 𝒳 →
          (finrank F 𝒳 : ℝ) ≤
            multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 2 +
              C * (b : ℝ) * (M : ℝ) * (d : ℝ)) ∧
      (linearClassUniformMaxDim F b p : ℝ) ≤
        multiClassLeadingCoeff M * (b : ℝ) * (d : ℝ) ^ 2 +
          C * (b : ℝ) * (M : ℝ) * (d : ℝ)) ∧
  (∀ M : ℕ, 2 ≤ M → multiClassLeadingCoeff M < 1 - 1 / (2 * (M : ℝ))) ∧
  (multiClassLeadingCoeff 3 = (37 / 54 : ℝ) ∧ (37 / 54 : ℚ) < 5 / 6) ∧
  (multiClassLeadingCoeff 4 = (191 / 256 : ℝ) ∧ (191 / 256 : ℚ) < 7 / 8)

end BoundedArityDecoders
