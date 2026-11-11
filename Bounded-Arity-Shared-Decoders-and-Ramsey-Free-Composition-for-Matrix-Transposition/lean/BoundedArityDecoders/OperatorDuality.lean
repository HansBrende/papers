import SharedDecoders.Model
import SwapRigidity.ClassUniform
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Formal Specifications — Part III.A: Anti-Diagonal Untwisting & Operator Entanglement Duality

Statement-only formal specifications of all claims in `README.md` concerning
Breakthrough 3 (`Problem 9.1` & `Problem 9.5`) and Blueprint Part III:

1. **Exact Collision Characterization & Anti-Diagonal Tensor Separation (`Problem 9.1`)**:
   * `PairwiseShiftCollisionCharacterizationSpec`: a linear source `C ≤ State d A` admits
     deterministic (possibly nonlinear) `p`-shared decoders iff for every shift `s : ZMod d`,
     every `Y ∈ C` with `rot s Y ∈ C` satisfies pairwise shift covariance `H_{\{0, s\}}(p)`.
   * `antiDiagLinear` / `fromAntiDiagLinear` (`Z_{c, a} = X_{c, a - c}`) and
     `AntiDiagonalTensorSeparationSpec`: `antiDiagLinear` is a linear isomorphism that
     intertwines every column rotation `rotLinear F t` with the pure right-factor shift
     `I_d ⊗ σ^t` (`(Z c) (a + t)`, under `(σ v)_a = v_{a + 1}` so `(σ^t v)_a = v_{a + t}`)
     and maps general shift-set covariance `H_E(p)` onto matrices whose column profile at each
     anti-diagonal `a` is constant on the connected components of `SwapRigidity.Link p E`.

2. **First-Quantized Operator Schmidt Rank (`Problem 9.5`)**:
   * `HasOperatorSchmidtRankLe` & `HasExactOperatorSchmidtRank` across
     `End_F(F^d_row) ⊗ End_F(F^d_col ⊗ F^b)`.
   * `OperatorSchmidtRankSubmultiplicativeSpec`: submultiplicativity under composition and
     `rk_⊗ ≤ 1` for row-uniform column operators and column-uniform row operators.
   * `OperatorSchmidtRankSwapSpec`: `rk_⊗(swap) = d^2` (`d ≥ 1, b ≥ 1`).
   * `OperatorSchmidtRankStoneShuffleSpec`: `S` and `S⁻¹` are mutual inverses on `d = 2^m`, with
     `rk_⊗ ≤ 4` for all `m ≥ 0` and exact `rk_⊗(S) = rk_⊗(S⁻¹) = 4` for all `m ≥ 1` (`d ≥ 2`, `b ≥ 1`).
   * `StoneShufflePipelinePassLowerBoundSpec`: any pipeline with `t` Stone shuffle/unshuffle
     passes and unlimited row-uniform column / column-uniform row passes realizing `swap` on
     `d = 2^m` (`m ≥ 0`) satisfies `d^2 ≤ 4^t` and `m ≤ t`.
   * Adversarial controls:
     - `Control_RowShearAndRowDiagonalAlternationSpec` (`rk_⊗(K_shear) = d` inside `D_row ⊗ End`,
       every alternating product `D_s U_s D_{s-1} ⋯ U_1 D_0` sends at most `2^s` source rows to
       each output row, and `D_s U_s D_{s-1} ⋯ U_1 D_0 = swap` forces `2^m ≤ 2^s` and `m ≤ s`),
     - `Control_SkewOneTimePadInformationTrapSpec` (`W = Xᵀ ⊕ X` satisfies `W ⊕ X = Xᵀ` while
       every single cell `W_{r, c}` is statistically independent of every target column `X_{:, c'}`).
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

section AntiDiagonalDefs

/-- Pairwise shift-covariance predicate `H_{\{0, s\}}(p)` on `State d A`: whenever `p c = p (c + s)`,
row `c + s` equals row `c` shifted by `s`. -/
def InPairwiseShiftCovariance {d : ℕ} {κ A : Type*}
    (p : ZMod d → κ) (s : ZMod d) (X : State d A) : Prop :=
  ∀ c : ZMod d, p c = p (c + s) → ∀ j : ZMod d, X (c + s) j = X c (j + s)

/-- General shift-set covariance predicate `H_E(p)` on `State d A` induced by `SwapRigidity.Link p E`:
whenever `c, c'` satisfy `p c = p c'` and `c + δ = c' + δ'` for `δ, δ' ∈ E`,
`X c' (j + δ') = X c (j + δ)` for all `j`. -/
def InShiftSetCovariance {d : ℕ} {κ A : Type*}
    (p : ZMod d → κ) (E : Finset (ZMod d)) (X : State d A) : Prop :=
  ∀ (c c' δ δ' : ZMod d),
    δ ∈ E → δ' ∈ E → p c = p c' → c + δ = c' + δ' →
    ∀ j : ZMod d, X c' (j + δ') = X c (j + δ)

/-- Anti-diagonal coordinate transform `Z_{c, a} := X_{c, a - c}` as a linear map built purely
from `LinearMap` combinators. -/
def antiDiagLinear (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] : State d A →ₗ[F] State d A :=
  LinearMap.pi fun c => LinearMap.pi fun a =>
    (LinearMap.proj (R := F) (φ := fun _ : ZMod d => A) (a - c)).comp
      (LinearMap.proj (R := F) (φ := fun _ : ZMod d => ZMod d → A) c)

/-- Inverse anti-diagonal coordinate transform `X_{c, j} := Z_{c, j + c}`. -/
def fromAntiDiagLinear (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] : State d A →ₗ[F] State d A :=
  LinearMap.pi fun c => LinearMap.pi fun j =>
    (LinearMap.proj (R := F) (φ := fun _ : ZMod d => A) (j + c)).comp
      (LinearMap.proj (R := F) (φ := fun _ : ZMod d => ZMod d → A) c)

/-- Pure right-factor shift `(I_d ⊗ σ^t) Z c a = Z c (a + t)` in anti-diagonal coordinates
(with standard left-shift convention `(σ v)_a = v_{a + 1}`, so `(σ^t v)_a = v_{a + t}`, matching
`(antiDiagLinear (rot t X)) c a = X c (a - c + t) = Z c (a + t)`). -/
def antiDiagRightShiftLinear (F : Type*) [Semiring F] (d : ℕ) (A : Type*)
    [AddCommMonoid A] [Module F A] (t : ZMod d) : State d A →ₗ[F] State d A :=
  LinearMap.pi fun c => LinearMap.pi fun a =>
    (LinearMap.proj (R := F) (φ := fun _ : ZMod d => A) (a + t)).comp
      (LinearMap.proj (R := F) (φ := fun _ : ZMod d => ZMod d → A) c)

end AntiDiagonalDefs

section OperatorSchmidtDefs

/-- Matrix space `F^d_row ⊗ (F^d_col ⊗ F^b)` indexed by `(row, col, lane) : Fin d × Fin d × Fin b`. -/
abbrev GridState (F : Type*) (d b : ℕ) := Fin d → Fin d → Fin b → F

/-- A linear operator `K` on `GridState F d b` has **Operator Schmidt (Kronecker) Rank `≤ R`**
across `End_F(F^d_row) ⊗ End_F(F^d_col ⊗ F^b)` if `K = ∑_{i < R} A_i ⊗ B_i` for `R` row matrices
`A_i ∈ Mat_{d × d}(F)` and `R` column-register maps `B_i ∈ End_F(F^d_col ⊗ F^b)`. -/
def HasOperatorSchmidtRankLe {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) (R : ℕ) : Prop :=
  ∃ (A : Fin R → Matrix (Fin d) (Fin d) F)
    (B : Fin R → ((Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F))),
    ∀ (X : GridState F d b) (r c : Fin d) (ℓ : Fin b),
      K X r c ℓ = ∑ i : Fin R, ∑ r' : Fin d, A i r r' * (B i (X r') c ℓ)

/-- Exact Operator Schmidt Rank `rk_⊗(K) = R`: achievable with `R` terms and no fewer. -/
def HasExactOperatorSchmidtRank {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) (R : ℕ) : Prop :=
  HasOperatorSchmidtRankLe K R ∧ ∀ R' : ℕ, R' < R → ¬ HasOperatorSchmidtRankLe K R'

/-- Row-uniform column operator `I_d ⊗ B` (`(K X) r = B (X r)`). -/
def IsRowUniformColOp {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) : Prop :=
  ∃ B : (Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F),
    ∀ X r, K X r = B (X r)

/-- Column-uniform row operator `A ⊗ I_{d b}` (`(K X) r c ℓ = ∑_{r'} A r r' * X r' c ℓ`). -/
def IsColUniformRowOp {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) : Prop :=
  ∃ A : Matrix (Fin d) (Fin d) F,
    ∀ X r c ℓ, K X r c ℓ = ∑ r' : Fin d, A r r' * X r' c ℓ

/-- Row-diagonal (zero-inter-row-communication) subalgebra `D_row ⊗ End_F(F^d_col ⊗ F^b)`:
each output row `r` applies its own arbitrary linear operator `B_r` to input row `X r` alone. -/
def IsRowDiagonalOp {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) : Prop :=
  ∃ B : Fin d → ((Fin d → Fin b → F) →ₗ[F] (Fin d → Fin b → F)),
    ∀ X r, K X r = B r (X r)

/-- Output row `r` of `K : GridState F d b →ₗ[F] GridState F d b` depends on at most `R` source
rows of `X`. -/
def HasOutputRowSourceArityLe {F : Type*} [Semiring F] {d b : ℕ}
    (K : GridState F d b →ₗ[F] GridState F d b) (R : ℕ) : Prop :=
  ∃ srcRows : Fin d → Finset (Fin d),
    (∀ r : Fin d, (srcRows r).card ≤ R) ∧
    ∀ (r : Fin d) (X₁ X₂ : GridState F d b),
      (∀ r' ∈ srcRows r, X₁ r' = X₂ r') → K X₁ r = K X₂ r

/-- Matrix transpose `τ` on `GridState F d b`: `(gridSwapLinear X) r c ℓ = X c r ℓ`. -/
def gridSwapLinear (F : Type*) [Semiring F] (d b : ℕ) :
    GridState F d b →ₗ[F] GridState F d b :=
  LinearMap.pi fun r => LinearMap.pi fun c => LinearMap.pi fun ℓ =>
    (LinearMap.proj (R := F) (φ := fun _ : Fin b => F) ℓ).comp
      ((LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin b → F) r).comp
        (LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin d → Fin b → F) c))

/-- Within-row shear `K_shear` on `GridState F d b` (`d ≥ 1`):
`(rowShearLinear X) r c ℓ = X r ((c + r) mod d) ℓ`. -/
def rowShearLinear (F : Type*) [Semiring F] (d b : ℕ) [NeZero d] :
    GridState F d b →ₗ[F] GridState F d b :=
  LinearMap.pi fun r => LinearMap.pi fun c => LinearMap.pi fun ℓ =>
    let cShift : Fin d := ⟨(c.val + r.val) % d, Nat.mod_lt _ (NeZero.pos d)⟩
    (LinearMap.proj (R := F) (φ := fun _ : Fin b => F) ℓ).comp
      ((LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin b → F) cShift).comp
        (LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin d → Fin b → F) r))

/-- Stone's 1-bit cyclic shuffle pass `S` on `d = 2^m` (`m : ℕ`):
for `m = 0` (`d = 1`), the `0`-bit address rotation is `id`; for `m ≥ 1` (`d = 2^m ≥ 2`), rotates
the `2 m`-bit cell address `p = r * d + c` left by 1 bit, so output `(r', c')` receives cell
`(r, c)` with `r = (c' % 2) * 2^(m - 1) + r' / 2` and `c = (r' % 2) * 2^(m - 1) + c' / 2`. -/
def stoneShuffleGridLinear (F : Type*) [Semiring F] :
    (m b : ℕ) → GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b
  | 0, _ => LinearMap.id
  | m + 1, b =>
      let d := 2 ^ (m + 1)
      let hd := Nat.two_pow_pos (m + 1)
      LinearMap.pi fun r' => LinearMap.pi fun c' => LinearMap.pi fun ℓ =>
        let srcR : Fin d := ⟨((c'.val % 2) * (2 ^ m) + r'.val / 2) % d, Nat.mod_lt _ hd⟩
        let srcC : Fin d := ⟨((r'.val % 2) * (2 ^ m) + c'.val / 2) % d, Nat.mod_lt _ hd⟩
        (LinearMap.proj (R := F) (φ := fun _ : Fin b => F) ℓ).comp
          ((LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin b → F) srcC).comp
            (LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin d → Fin b → F) srcR))

/-- Stone's inverse 1-bit cyclic unshuffle pass `S⁻¹` on `d = 2^m` (`m : ℕ`):
for `m = 0` (`d = 1`), `id`; for `m ≥ 1` (`d = 2^m ≥ 2`), output `(r, c)` receives cell `(r', c')`
with `r' = (2 * r + c / 2^(m - 1)) % d` and `c' = (2 * c + r / 2^(m - 1)) % d`. -/
def stoneUnshuffleGridLinear (F : Type*) [Semiring F] :
    (m b : ℕ) → GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b
  | 0, _ => LinearMap.id
  | m + 1, b =>
      let d := 2 ^ (m + 1)
      let hd := Nat.two_pow_pos (m + 1)
      LinearMap.pi fun r => LinearMap.pi fun c => LinearMap.pi fun ℓ =>
        let srcR : Fin d := ⟨(2 * r.val + c.val / (2 ^ m)) % d, Nat.mod_lt _ hd⟩
        let srcC : Fin d := ⟨(2 * c.val + r.val / (2 ^ m)) % d, Nat.mod_lt _ hd⟩
        (LinearMap.proj (R := F) (φ := fun _ : Fin b => F) ℓ).comp
          ((LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin b → F) srcC).comp
            (LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin d → Fin b → F) srcR))

/-- Ordered composition of a list of linear operators on `GridState F d b`:
`composeGridOps [K_1, …, K_n] = K_n ∘ ⋯ ∘ K_1`. -/
def composeGridOps {F : Type*} [Semiring F] {d b : ℕ} :
    List (GridState F d b →ₗ[F] GridState F d b) → (GridState F d b →ₗ[F] GridState F d b)
  | [] => LinearMap.id
  | K :: Ks => (composeGridOps Ks).comp K

/-- Alternating product `D_s U_s D_{s-1} ⋯ U_1 D_0` of `(s + 1)` row-diagonal operators `D`
with `s` shuffle/unshuffle operators `U`. -/
def alternatingRowDiagProduct {F : Type*} [Semiring F] {d b : ℕ} :
    {s : ℕ} →
    (Fin (s + 1) → (GridState F d b →ₗ[F] GridState F d b)) →
    (Fin s → (GridState F d b →ₗ[F] GridState F d b)) →
    (GridState F d b →ₗ[F] GridState F d b)
  | 0, D, _ => D 0
  | s + 1, D, U =>
      let prefixOp := alternatingRowDiagProduct
        (fun i : Fin (s + 1) => D i.castSucc)
        (fun i : Fin s => U i.castSucc)
      (D (Fin.last (s + 1))).comp ((U (Fin.last s)).comp prefixOp)

/-- Skew-symmetric one-time-pad state `W = Xᵀ ⊕ X` on `State d (Fin b → Bool)`. -/
def skewXorPad {d b : ℕ} (X : State d (Fin b → Bool)) : State d (Fin b → Bool) :=
  fun r c ℓ => xor (X c r ℓ) (X r c ℓ)

end OperatorSchmidtDefs

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Claim (`README.md` §II.3.1 Bullet 1 — Exact Pairwise Shift-Collision Characterization).**
For any linear source `C ≤ State d A` and receiver partition `p : ZMod d → κ`, `C` admits
deterministic (possibly nonlinear) shared decoders (`SharedDecoders.IsSharedCode F p C`) if and
only if for every single shift `s : ZMod d`, every `Y ∈ C` with `rot s Y ∈ C` satisfies
`InPairwiseShiftCovariance p s Y`. -/
def PairwiseShiftCollisionCharacterizationSpec : Prop :=
  ∀ (F : Type*) [Field F] (d : ℕ) (κ A : Type*) [AddCommGroup A] [Module F A]
    (p : ZMod d → κ) (C : Submodule F (State d A)),
    IsSharedCode F p C ↔
      ∀ s : ZMod d, ∀ Y ∈ C, rot s Y ∈ C → InPairwiseShiftCovariance p s Y

/-- **Claim (`README.md` §II.3.1 Bullet 2 — Anti-Diagonal Tensor Separation).**
1. `antiDiagLinear` and `fromAntiDiagLinear` are mutually inverse linear maps on `State d A`.
2. Every column rotation untwists onto the right factor alone:
   `antiDiagLinear ∘ rotLinear t = antiDiagRightShiftLinear t ∘ antiDiagLinear`.
3. Every shift-set covariance space `H_E(p)` untwists onto the left factor alone: `X` satisfies
   `InShiftSetCovariance p E X` iff for every anti-diagonal index `a : ZMod d`,
   `fun c => antiDiagLinear F d A X c a` is constant on the connected components
   `Relation.EqvGen (SwapRigidity.Link p E)`. -/
def AntiDiagonalTensorSeparationSpec : Prop :=
  ∀ (F : Type*) [Field F] (d : ℕ) (κ A : Type*) [AddCommGroup A] [Module F A],
    (antiDiagLinear F d A).comp (fromAntiDiagLinear F d A) = LinearMap.id ∧
    (fromAntiDiagLinear F d A).comp (antiDiagLinear F d A) = LinearMap.id ∧
    (∀ t : ZMod d,
      (antiDiagLinear F d A).comp (rotLinear F t) =
        (antiDiagRightShiftLinear F d A t).comp (antiDiagLinear F d A)) ∧
    (∀ (p : ZMod d → κ) (E : Finset (ZMod d)) (X : State d A),
      InShiftSetCovariance p E X ↔
        ∀ (c c' a : ZMod d),
          Relation.EqvGen (SwapRigidity.Link p E) c c' →
          antiDiagLinear F d A X c a = antiDiagLinear F d A X c' a)

/-- **Claim (`README.md` §II.3.2 — Operator Schmidt Rank Submultiplicativity & Unit-Rank Primitives).**
1. Row-uniform column operators (`I_d ⊗ B`) and column-uniform row operators (`A ⊗ I_{d b}`)
   have Operator Schmidt Rank at most `1`.
2. If `rk_⊗(K₁) ≤ R₁` and `rk_⊗(K₂) ≤ R₂`, then `rk_⊗(K₂ ∘ K₁) ≤ R₂ * R₁`. -/
def OperatorSchmidtRankSubmultiplicativeSpec : Prop :=
  ∀ (F : Type*) [Field F] (d b : ℕ),
    (∀ K : GridState F d b →ₗ[F] GridState F d b,
      IsRowUniformColOp K → HasOperatorSchmidtRankLe K 1) ∧
    (∀ K : GridState F d b →ₗ[F] GridState F d b,
      IsColUniformRowOp K → HasOperatorSchmidtRankLe K 1) ∧
    (∀ (K₁ K₂ : GridState F d b →ₗ[F] GridState F d b) (R₁ R₂ : ℕ),
      HasOperatorSchmidtRankLe K₁ R₁ →
      HasOperatorSchmidtRankLe K₂ R₂ →
      HasOperatorSchmidtRankLe (K₂.comp K₁) (R₂ * R₁))

/-- **Claim (`README.md` §II.3.2 Bullet 1 — Exact Operator Schmidt Rank of Transpose `τ`).**
Over any field `F`, for all `d ≥ 1` and `b ≥ 1`, `gridSwapLinear F d b` has exact Operator
Schmidt Rank `d^2`. -/
def OperatorSchmidtRankSwapSpec : Prop :=
  ∀ (F : Type*) [Field F] (d b : ℕ),
    1 ≤ d → 1 ≤ b →
    HasExactOperatorSchmidtRank (gridSwapLinear F d b) (d ^ 2)

/-- **Claim (`README.md` §II.3.2 Bullet 2 — Exact Operator Schmidt Rank of Stone's Shuffle `S`).**
Over any field `F` and `b ≥ 1`:
1. For all `m : ℕ` (`d = 2^m`), `stoneShuffleGridLinear F m b` and `stoneUnshuffleGridLinear F m b`
   are mutual inverses and have Operator Schmidt Rank at most `4`;
2. For all `m ≥ 1` (`d = 2^m ≥ 2`), both have **exact** Operator Schmidt Rank `4` (independent of
   `m` and `b`). -/
def OperatorSchmidtRankStoneShuffleSpec : Prop :=
  ∀ (F : Type*) [Field F] (m b : ℕ), 1 ≤ b →
    (stoneShuffleGridLinear F m b).comp (stoneUnshuffleGridLinear F m b) = LinearMap.id ∧
    (stoneUnshuffleGridLinear F m b).comp (stoneShuffleGridLinear F m b) = LinearMap.id ∧
    HasOperatorSchmidtRankLe (stoneShuffleGridLinear F m b) 4 ∧
    HasOperatorSchmidtRankLe (stoneUnshuffleGridLinear F m b) 4 ∧
    (1 ≤ m →
      HasExactOperatorSchmidtRank (stoneShuffleGridLinear F m b) 4 ∧
      HasExactOperatorSchmidtRank (stoneUnshuffleGridLinear F m b) 4)

/-- **Claim (`README.md` §II.3.2 Bullet 3 — Tight `log₂ d` Pass Lower Bound for Shuffle Pipelines).**
Over any field `F`, for **all** `m : ℕ` (`d = 2^m ≥ 1`) and `b ≥ 1`, if a pipeline `Ks` consisting
of `t` shuffle/unshuffle passes interleaved with any number of row-uniform column operators and
column-uniform row operators realizes `gridSwapLinear F (2^m) b`, then `(2^m)^2 ≤ 4^t` and `m ≤ t`. -/
def StoneShufflePipelinePassLowerBoundSpec : Prop :=
  ∀ (F : Type*) [Field F] (m b : ℕ)
    (Ks : List (GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b))
    (shuffleIndices : Finset (Fin Ks.length)),
    1 ≤ b →
    (∀ i : Fin Ks.length,
      if i ∈ shuffleIndices then
        Ks.get i = stoneShuffleGridLinear F m b ∨ Ks.get i = stoneUnshuffleGridLinear F m b
      else
        IsRowUniformColOp (Ks.get i) ∨ IsColUniformRowOp (Ks.get i)) →
    composeGridOps Ks = gridSwapLinear F (2 ^ m) b →
    (2 ^ m) ^ 2 ≤ 4 ^ shuffleIndices.card ∧ m ≤ shuffleIndices.card

/-- **Adversarial Control 1 (`README.md` §II.3.2 Bullet 4a — Row Shear & Row-Diagonal Alternation).**
1. Over any field `F`, for `d ≥ 1` and `b ≥ 1`, `rowShearLinear F d b` lies inside the
   zero-inter-row-communication subalgebra `IsRowDiagonalOp` yet has exact Operator Schmidt
   Rank `d`.
2. For all `m, s : ℕ` (`d = 2^m ≥ 1`) and `b ≥ 1`, any alternating product
   `D_s U_s D_{s-1} ⋯ U_1 D_0` of `(s + 1)` arbitrary row-diagonal operators `D_i` with `s` Stone
   shuffles/unshuffles `U_j` sends at most `2^s` source rows to each output row
   (`HasOutputRowSourceArityLe ... (2 ^ s)`), and therefore cannot equal `gridSwapLinear F (2^m) b`
   unless `2^m ≤ 2^s` and `m ≤ s`. -/
def Control_RowShearAndRowDiagonalAlternationSpec : Prop :=
  (∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d], 1 ≤ b →
    IsRowDiagonalOp (rowShearLinear F d b) ∧
    HasExactOperatorSchmidtRank (rowShearLinear F d b) d) ∧
  (∀ (F : Type*) [Field F] (m b s : ℕ)
    (D : Fin (s + 1) → (GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b))
    (U : Fin s → (GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b)),
    1 ≤ b →
    (∀ i : Fin (s + 1), IsRowDiagonalOp (D i)) →
    (∀ j : Fin s,
      U j = stoneShuffleGridLinear F m b ∨ U j = stoneUnshuffleGridLinear F m b) →
    HasOutputRowSourceArityLe (alternatingRowDiagProduct D U) (2 ^ s) ∧
    (alternatingRowDiagProduct D U = gridSwapLinear F (2 ^ m) b →
      2 ^ m ≤ 2 ^ s ∧ m ≤ s))

/-- **Adversarial Control 2 (`README.md` §II.3.2 Bullet 4b — Skew One-Time-Pad Information Trap).**
For every `d ≥ 1` and `b ≥ 1`, `W = skewXorPad X` (`W = Xᵀ ⊕ X`) satisfies:
1. One pass of `X` unmasks `swap X`: `xor (W_{r, c, ℓ}) (X_{r, c, ℓ}) = (swap X)_{r, c, ℓ}`;
2. Under uniform `X ∈ State d (Fin b → Bool)`, for **every** cell `(r, c)` and **every** target
   column `c'`, the cell `W_{r, c}` and the entire target column `X_{:, c'}` are statistically
   independent (`|State| * #{X | W_{r, c} = v ∧ X_{:, c'} = u} = #{X | W_{r, c} = v} * #{X | X_{:, c'} = u}`,
   so marginal mutual information `I(W_{r, c}; X_{:, c'}) = 0`). -/
def Control_SkewOneTimePadInformationTrapSpec : Prop :=
  ∀ (d b : ℕ) [NeZero d], 1 ≤ b →
    (∀ (X : State d (Fin b → Bool)) (r c : ZMod d) (ℓ : Fin b),
      xor (skewXorPad X r c ℓ) (X r c ℓ) = swap X r c ℓ) ∧
    (∀ (r c c' : ZMod d) (v : Fin b → Bool) (u : ZMod d → Fin b → Bool),
      Fintype.card (State d (Fin b → Bool)) *
        (Finset.univ.filter fun X : State d (Fin b → Bool) =>
          skewXorPad X r c = v ∧ (fun i => X i c') = u).card =
      (Finset.univ.filter fun X : State d (Fin b → Bool) => skewXorPad X r c = v).card *
        (Finset.univ.filter fun X : State d (Fin b → Bool) => (fun i => X i c') = u).card)

end BoundedArityDecoders
