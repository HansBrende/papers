import SharedDecoders.Model
import SharedDecoders.CompositionProgression
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Formal Specifications — Part II.A: Affine `k`-Cube Growth & Hales–Jewett-Free Two-Stage Cutoff

Statement-only formal specifications of all claims in `README.md` concerning
Breakthrough 2, Theorem 2A:

* `orderedCubeMap`: ordered operator cube vertices `R_{k-1}^{ε_{k-1}} ⋯ R_0^{ε_0}`.
* `Lemma_AffineCubeCommonMessageGrowthSpec`: over every field `F`,
  `(k + 1) * finrank F W ≤ finrank F A + ∑ t, finrank F (ker (R_t - id))`.
* `Control_D13TwoCubeAPFreeSharpnessSpec`: at prime `d = 13`, `q = 2` (`dim A = 26`), the
  2-cube `J = {0, 1, 4, 5}` contains no non-constant 3-term arithmetic progression mod `13`,
  forces `finrank W ≤ 10`, and admits an exact `(W, L)` of dimension `D = 9` (refuting the
  `2^k D ≤ dim A + (2^k - 1) q` strengthening `D ≤ 8`).
* `Control_D4SameIntervalCodedFactorizationSpec`: at `d = 4` with identical interval partitions
  `p₁ = p₂ = [0, 0, 1, 1]`, uncoded entry-copying two-stage rules cannot realize `swap`, whereas
  coded linear `ClassUniform` maps `K₁, K₂` satisfy `K₂ ∘ K₁ = swapLinear`.
* `CauchySchwarzAffineCubeExtractionSpec` & `Theorem2A_TwoStageRamseyFreeCutoffSpec`:
  elementary Cauchy–Schwarz cube extraction and the Hales–Jewett-free cutoff
  `d ≤ max (8 * M₁ * M₂^2) ((2 * M₁)^(2^M₂))` over every field `F` and lane width `b ≥ 1`.
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

section Definitions

variable {F A : Type*} [Semiring F] [AddCommMonoid A] [Module F A]

/-- Ordered operator cube evaluation `R_{k-1}^{ε_{k-1}} ⋯ R_0^{ε_0} : A →ₗ[F] A`. -/
def orderedCubeMap : {k : ℕ} → (Fin k → (A →ₗ[F] A)) → (Fin k → Bool) → (A →ₗ[F] A)
  | 0, _, _ => LinearMap.id
  | k + 1, R, ε =>
      let tail := orderedCubeMap (fun i : Fin k => R i.castSucc) (fun i : Fin k => ε i.castSucc)
      if ε (Fin.last k) then (R (Fin.last k)).comp tail else tail

/-- Linear cyclic shift `(T_s w) u = w (u + s)` on `ZMod d → (Fin q → R)` constructed purely
from `LinearMap` combinators. -/
def cyclicChannelShift (R : Type*) [Semiring R] (d q : ℕ) (s : ZMod d) :
    (ZMod d → Fin q → R) →ₗ[R] (ZMod d → Fin q → R) :=
  LinearMap.pi fun u => LinearMap.pi fun ch =>
    (LinearMap.proj (R := R) (φ := fun _ : Fin q => R) ch).comp
      (LinearMap.proj (R := R) (φ := fun _ : ZMod d => Fin q → R) (u + s))

/-- Entry-copying (uncoded coordinate-routing) class-uniform map on `State d Sigma`: each class
`m` selects fixed rotated coordinates `(srcRow m i, srcOff m i)` for output row `i`. -/
def IsEntryCopyClassRule {d : ℕ} {κ Sigma : Type*}
    (p : ZMod d → κ) (K : State d Sigma → State d Sigma) : Prop :=
  ∃ (srcRow srcOff : κ → ZMod d → ZMod d),
    ∀ (X : State d Sigma) (c i : ZMod d),
      K X i c = (rot c X) (srcRow (p c) i) (srcOff (p c) i)

/-- The half-cycle interval partition `[0, 0, 1, 1]` on `ZMod 4`. -/
def halfIntervalPartition4 (c : ZMod 4) : Fin 2 :=
  if c.val < 2 then 0 else 1

/-- Subset `J ⊆ ZMod d` contains no non-constant 3-term arithmetic progression modulo `d`. -/
def ThreeAPFreeMod {d : ℕ} (J : Finset (ZMod d)) : Prop :=
  ∀ a s : ZMod d, s ≠ 0 → ¬ (a ∈ J ∧ a + s ∈ J ∧ a + (s + s) ∈ J)

end Definitions

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Lemma (`README.md` §II.2 Theorem 2A — Affine `k`-Cube Common-Message Growth).**
Over any field `F`, for any finite-dimensional `F`-vector space `A`, any `k` linear endomorphisms
`R : Fin k → (A →ₗ[F] A)`, any subspace `W ≤ A`, and any `L : A →ₗ[F] Z` injective on `W`, if
`L (R_{k-1}^{ε_{k-1}} ⋯ R_0^{ε_0} x) = L x` for all `x ∈ W` and `ε ∈ {0, 1}^k`, then
`(k + 1) * finrank F W ≤ finrank F A + ∑ t, finrank F (ker (R t - id))`. -/
def Lemma_AffineCubeCommonMessageGrowthSpec : Prop :=
  ∀ (F A Z : Type*) [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    [AddCommGroup Z] [Module F Z]
    (k : ℕ) (R : Fin k → (A →ₗ[F] A)) (W : Submodule F A) (L : A →ₗ[F] Z),
    (∀ x ∈ W, L x = 0 → x = 0) →
    (∀ x ∈ W, ∀ ε : Fin k → Bool, L (orderedCubeMap R ε x) = L x) →
    (k + 1) * finrank F W ≤
      finrank F A + ∑ t : Fin k, finrank F (LinearMap.ker (R t - LinearMap.id))

/-- **Sharpness & AP-Free Control (`README.md` §II.2 Theorem 2A Bullet 1 — `d = 13, J = {0,1,4,5}`).**
1. `J = {0, 1, 4, 5} ⊆ ZMod 13` is an affine 2-cube `{0, 1} + {0, 4}` with no non-constant
   3-term arithmetic progression modulo `13`.
2. Over every field `F`, for `A = ZMod 13 → Fin 2 → F` (`dim A = 26`), any subspace `W ≤ A` and
   linear `L : A →ₗ[F] Z` injective on `W` with `L (T_c x) = L x` for all `c ∈ {0, 1, 4, 5}`
   satisfies `finrank F W ≤ 10` (`< 13`).
3. Conversely, over `ℝ`, there exists such a pair `(W, L)` of exact dimension `finrank ℝ W = 9`
   (`> 8`), refuting the naive `2^k D ≤ dim A + (2^k - 1) q` strengthening. -/
def Control_D13TwoCubeAPFreeSharpnessSpec : Prop :=
  let J13 : Finset (ZMod 13) := {0, 1, 4, 5}
  ThreeAPFreeMod J13 ∧
  (∀ (F Z : Type*) [Field F] [AddCommGroup Z] [Module F Z]
    (W : Submodule F (ZMod 13 → Fin 2 → F))
    (L : (ZMod 13 → Fin 2 → F) →ₗ[F] Z),
    (∀ x ∈ W, L x = 0 → x = 0) →
    (∀ x ∈ W, ∀ c ∈ J13, L (cyclicChannelShift F 13 2 c x) = L x) →
    finrank F W ≤ 10) ∧
  (∃ (W : Submodule ℝ (ZMod 13 → Fin 2 → ℝ))
      (L : (ZMod 13 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)),
    finrank ℝ W = 9 ∧
    (∀ x ∈ W, L x = 0 → x = 0) ∧
    (∀ x ∈ W, ∀ c ∈ J13, L (cyclicChannelShift ℝ 13 2 c x) = L x))

/-- **Same-Interval Coded Factorization Control (`README.md` §II.2 Theorem 2A Bullet 2 — `d = 4`).**
At `d = 4 = M₁ M₂` with identical two-interval partitions `p₁ = p₂ = [0, 0, 1, 1]`:
1. No pair of entry-copying two-stage rules `K₁, K₂` with `p₁ = p₂ = [0, 0, 1, 1]` satisfies
   `K₂ ∘ K₁ = swap` on `State 4 Bool`;
2. Yet over `ℝ`, there exist linear class-uniform maps `K₁, K₂ : State 4 ℝ →ₗ[ℝ] State 4 ℝ`
   for `p₁ = p₂ = [0, 0, 1, 1]` satisfying `K₂.comp K₁ = swapLinear ℝ`. -/
def Control_D4SameIntervalCodedFactorizationSpec : Prop :=
  (¬ ∃ K₁ K₂ : State 4 Bool → State 4 Bool,
      IsEntryCopyClassRule halfIntervalPartition4 K₁ ∧
      IsEntryCopyClassRule halfIntervalPartition4 K₂ ∧
      K₂ ∘ K₁ = swap) ∧
  (∃ K₁ K₂ : State 4 ℝ →ₗ[ℝ] State 4 ℝ,
      ClassUniform halfIntervalPartition4 K₁ ∧
      ClassUniform halfIntervalPartition4 K₂ ∧
      K₂.comp K₁ = swapLinear ℝ)

/-- **Claim (Elementary Cauchy–Schwarz Cube Extraction, `README.md` §II.2 Theorem 2A Bullet 3).**
Whenever `d > max (8 * M₁ * M₂^2) ((2 * M₁)^(2^M₂))` (`M₁, M₂ ≥ 1`), every `M₁`-coloring
`p₁ : ZMod d → Fin M₁` admits a base point `c₀ : ZMod d` and steps `s : Fin M₂ → ℕ` with
`1 ≤ s t` and `M₂^2 * s t < d` for all `t`, such that all `2^M₂` affine cube vertices
`c₀ + ∑_{t : ε t = true} s t` lie in the same `p₁`-class. -/
def CauchySchwarzAffineCubeExtractionSpec : Prop :=
  ∀ (d M₁ M₂ : ℕ) [NeZero d] (p₁ : ZMod d → Fin M₁),
    1 ≤ M₁ →
    1 ≤ M₂ →
    max (8 * M₁ * M₂ ^ 2) ((2 * M₁) ^ (2 ^ M₂)) < d →
    ∃ (c₀ : ZMod d) (s : Fin M₂ → ℕ),
      (∀ t : Fin M₂, 1 ≤ s t ∧ M₂ ^ 2 * s t < d) ∧
      ∀ ε : Fin M₂ → Bool,
        p₁ (c₀ + ∑ t : Fin M₂, if ε t then (s t : ZMod d) else 0) = p₁ c₀

/-- **Theorem 2A (`README.md` §II.2 — Hales–Jewett-Free Two-Stage Exact Factorization Cutoff).**
Over any field `F` and positive lane width `b ≥ 1`, if two linear class-uniform maps `K₁, K₂`
with `M₁ ≥ 1` and `M₂ ≥ 1` classes satisfy `K₂.comp K₁ = swapLinear F` on
`State d (Fin b → F)`, then
`d ≤ max (8 * M₁ * M₂^2) ((2 * M₁)^(2^M₂))`. -/
def Theorem2A_TwoStageRamseyFreeCutoffSpec : Prop :=
  ∀ (F : Type*) [Field F] (d b M₁ M₂ : ℕ) [NeZero d]
    (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
    (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
    1 ≤ b →
    1 ≤ M₁ →
    1 ≤ M₂ →
    ClassUniform p₁ K₁ →
    ClassUniform p₂ K₂ →
    K₂.comp K₁ = swapLinear F →
    d ≤ max (8 * M₁ * M₂ ^ 2) ((2 * M₁) ^ (2 ^ M₂))

end BoundedArityDecoders
