import SharedDecoders.Model
import SharedDecoders.CompositionRankField
import BoundedArityDecoders.AffineCubeComposition
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Formal Specifications — Part II.B: Sumset Polynomial Recurrence & Log-Power Rank Deficit

Statement-only formal specifications of all claims in `README.md` concerning
Breakthrough 2, Theorem 2B, and Blueprint Part II:

* `HasShiftedMonochromaticSumset`: shifted `(2 M₂)`-fold sumset
  `J₀ + ∑_{t ∈ S} B_t ⊆ {c | p₁ c = m₁}` with `0 ∈ B_t`, `|J₀| = k`, `|B_t| = k + 1`, and
  bounded diameters `diamB t`.
* Proof-spine specifications:
  - `VandermondeArbitrarySubsetInjectiveSpec` (Vandermonde evaluation injectivity on arbitrary `J₀`),
  - `SumsetAnnihilatingPolynomialSpec` (nonzero polynomial supported on `B_t` annihilating
    frequencies `0, …, k - 1` with `dim ker P_t(T) ≤ q * diamB t`),
  - `SumsetTwoHopRankBoundSpec` (`b k (d - ∑ t, diamB t) ≤ 2 * rank(τ - K₂ K₁)`),
  - `IteratedKovariSosTuranSumsetSpec` (iterated Kővári–Sós–Turán extraction at scale
    `k = Θ_{M₁, M₂}((log d)^(1 / (2 M₂ - 1)))`).
* `Theorem2B_TwoStageLogPowerRankDeficitSpec`:
  `rank(τ - K₂ K₁) ≥ c(M₁, M₂) * b * d * (log d)^(1 / (2 M₂ - 1))`.
* `Control_D12SingleClassAbstractBandSpec` (`d = 12, M₂ = 2, k = 2, J = {0, 1, 3, 4, 7, 9}`
  attaining full single-class band dimension `D = 24 = k d`) and
  `OpenTarget_MacroscopicTwoStageRankDeficitSpec` (`rank(τ - K₂ K₁) ≥ ε(M₁, M₂) b d^2`).
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

section Definitions

/-- A partition `p₁ : ZMod d → Fin M₁` admits a shifted `(nSteps + 1)`-fold monochromatic sumset
in class `m₁` of width parameter `k` and step diameters `diamB : Fin nSteps → ℕ`:
`|J₀| = k`, and for each `t`, `0 ∈ B t`, `|B t| = k + 1`, `∀ x ∈ B t, x ≤ diamB t`, and every
sum `c₀ + ∑_t b_t` (`c₀ ∈ J₀`, `b_t ∈ B t`) lies in class `m₁`.
Because `0 ∈ B t` for all `t`, every partial subset sum `J₀ + ∑_{t ∈ S} B t` is automatically
contained in `{c | p₁ c = m₁}`. -/
def HasShiftedMonochromaticSumset {d M₁ nSteps : ℕ}
    (p₁ : ZMod d → Fin M₁) (m₁ : Fin M₁) (k : ℕ)
    (J₀ : Finset (ZMod d))
    (B : Fin nSteps → Finset ℕ)
    (diamB : Fin nSteps → ℕ) : Prop :=
  J₀.card = k ∧
  (∀ t : Fin nSteps, 0 ∈ B t ∧ (B t).card = k + 1 ∧ ∀ x ∈ B t, x ≤ diamB t) ∧
  ∀ c₀ ∈ J₀, ∀ b : Fin nSteps → ℕ, (∀ t, b t ∈ B t) →
    p₁ (c₀ + ∑ t : Fin nSteps, (b t : ZMod d)) = m₁

/-- Vector-valued character polynomial evaluation on an arbitrary subset `J₀ ⊆ ZMod d`:
`(a_0, …, a_{k-1}) ↦ (∑_{ν < k} χ(ν · c) • a_ν)_{c ∈ J₀}`. -/
def charBandEval {d k : ℕ} {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (χ : AddChar (ZMod d) E) (J₀ : Finset (ZMod d))
    (a : Fin k → V) (c : J₀) : V :=
  ∑ ν : Fin k, (χ ((ν.val : ZMod d) * c.1)) • a ν

end Definitions

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Claim (`README.md` §II.2 Theorem 2B Step 2 — Arbitrary-Subset Vandermonde Injectivity).**
Over any field `E` with an injective additive character `χ : AddChar (ZMod d) E`, for any
subset `J₀ : Finset (ZMod d)` of cardinality `k`, evaluation of degree-`< k` character
polynomials `∑_{ν < k} χ(ν c) • a_ν` on `c ∈ J₀` is injective. -/
def VandermondeArbitrarySubsetInjectiveSpec : Prop :=
  ∀ (d k : ℕ) [NeZero d] (E V : Type*) [Field E] [AddCommGroup V] [Module E V]
    (χ : AddChar (ZMod d) E) (J₀ : Finset (ZMod d)),
    Function.Injective χ →
    J₀.card = k →
    Function.Injective (charBandEval (k := k) (V := V) χ J₀)

/-- **Claim (`README.md` §II.2 Theorem 2B Step 3 — Sparse Sumset Annihilating Polynomial).**
For any injective character `χ : AddChar (ZMod d) E` and any `B_t : Finset ℕ` with `0 ∈ B_t`,
`|B_t| = k + 1`, and `∀ x ∈ B_t, x ≤ L₀`, there exists a nonzero polynomial `P : Polynomial E`
supported in `B_t` of degree `≤ L₀` annihilating `{χ(ν · -) : 0 ≤ ν < k}`, and on the `q`-channel
cyclic module `ZMod d → Fin q → E`, `finrank E (ker P(T_1)) ≤ q * L₀`. -/
def SumsetAnnihilatingPolynomialSpec : Prop :=
  ∀ (d k q L₀ : ℕ) [NeZero d] (E : Type*) [Field E]
    (χ : AddChar (ZMod d) E) (B_t : Finset ℕ),
    Function.Injective χ →
    0 ∈ B_t →
    B_t.card = k + 1 →
    (∀ x ∈ B_t, x ≤ L₀) →
    ∃ P : Polynomial E,
      P ≠ 0 ∧
      P.natDegree ≤ L₀ ∧
      (∀ n ∈ P.support, n ∈ B_t) ∧
      (∀ ν : Fin k, ∑ x ∈ B_t, P.coeff x * χ (((ν.val * x : ℕ) : ZMod d)) = 0) ∧
      finrank E (LinearMap.ker (Polynomial.aeval (cyclicChannelShift E d q 1) P)) ≤ q * L₀

/-- **Claim (`README.md` §II.2 Theorem 2B Step 4 — Two-Stage Sumset Recurrence Rank Bound).**
Over any field `F` with `(d : F) ≠ 0`, if `p₁` admits a shifted `(2 M₂)`-fold monochromatic
sumset `(J₀, B, diamB)` of width `k ≥ 1` with `∑ t, diamB t ≤ d`, then any two linear
class-uniform stages `K₁, K₂` on `State d (Fin b → F)` satisfy
`b * k * (d - ∑ t, diamB t) ≤ 2 * finrank F (range (swapLinear F - K₂ ∘ K₁))`. -/
def SumsetTwoHopRankBoundSpec : Prop :=
  ∀ (F : Type*) [Field F] (d b M₁ M₂ k : ℕ) [NeZero d]
    (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
    (m₁ : Fin M₁) (J₀ : Finset (ZMod d))
    (B : Fin (2 * M₂ - 1) → Finset ℕ)
    (diamB : Fin (2 * M₂ - 1) → ℕ)
    (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
    (d : F) ≠ 0 →
    1 ≤ M₁ →
    1 ≤ M₂ →
    1 ≤ k →
    ∑ t : Fin (2 * M₂ - 1), diamB t ≤ d →
    HasShiftedMonochromaticSumset p₁ m₁ k J₀ B diamB →
    ClassUniform p₁ K₁ →
    ClassUniform p₂ K₂ →
    b * k * (d - ∑ t : Fin (2 * M₂ - 1), diamB t) ≤
      2 * finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁))

/-- **Claim (`README.md` §II.2 Theorem 2B Step 5 — Iterated Kővári–Sós–Turán Sumset Extraction).**
For every `M₁ ≥ 1` and `M₂ ≥ 1`, there exist `c_kst > 0` and `D₀` such that for all `d ≥ D₀`,
every `M₁`-coloring `p₁ : ZMod d → Fin M₁` contains a shifted `(2 M₂)`-fold monochromatic
sumset with step diameters `≤ d / (4 M₂)` and `k ≥ c_kst * (log d)^(1 / (2 M₂ - 1))`. -/
def IteratedKovariSosTuranSumsetSpec : Prop :=
  ∀ (M₁ M₂ : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
    ∃ (c_kst : ℝ) (D₀ : ℕ), 0 < c_kst ∧
      ∀ (d : ℕ) [NeZero d] (p₁ : ZMod d → Fin M₁), D₀ ≤ d →
        ∃ (m₁ : Fin M₁) (k : ℕ) (J₀ : Finset (ZMod d))
          (B : Fin (2 * M₂ - 1) → Finset ℕ),
          1 ≤ k ∧
          c_kst * (Real.log (d : ℝ)) ^ ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)) ≤ (k : ℝ) ∧
          HasShiftedMonochromaticSumset p₁ m₁ k J₀ B (fun _ => d / (4 * M₂))

/-- **Theorem 2B (`README.md` §II.2 — Log-Power Two-Stage Rank Deficit Over Admissible Fields).**
For every `M₁ ≥ 1` and `M₂ ≥ 1`, there exist `c > 0` and `D₀` such that for every field `F`,
every `d ≥ D₀` with `(d : F) ≠ 0`, every lane width `b ≥ 1`, and every pair of `M₁, M₂`-class
linear shared maps `K₁, K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)`,
`finrank F (range (swapLinear F - K₂ ∘ K₁)) ≥ c * b * d * (log d)^(1 / (2 M₂ - 1))`. -/
def Theorem2B_TwoStageLogPowerRankDeficitSpec : Prop :=
  ∀ (M₁ M₂ : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
    ∃ (c : ℝ) (D₀ : ℕ), 0 < c ∧
      ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d]
        (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
        (d : F) ≠ 0 →
        D₀ ≤ d →
        1 ≤ b →
        ClassUniform p₁ K₁ →
        ClassUniform p₂ K₂ →
        c * (b : ℝ) * (d : ℝ) * (Real.log (d : ℝ)) ^ ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)) ≤
          (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ)

/-- **Single-Class Abstract Band Control (`README.md` §II.2 Theorem 2B Note — `d = 12, k = 2`).**
At `d = 12, M₂ = 2, k = 2` (`q = M₂ k = 4`), on the half-density subset
`J = {0, 1, 3, 4, 7, 9} ⊆ ZMod 12`, for every primitive `12`-th root `ζ ∈ ℂ`, there exist a
linear readout `L : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ)` and a `24`-dimensional subspace
(`D = k d = 24`) realizing every pair of band coefficient vectors `(a_0, a_1) ∈ (ℂ^12)^2` as
`L (T_c w) = a_0 + ζ^c • a_1` for all `c ∈ J` — showing that pushing two-stage rank deficits to
`ε b d^2` must couple multiple classes or multiple frequency bands simultaneously. -/
def Control_D12SingleClassAbstractBandSpec : Prop :=
  let J12 : Finset (ZMod 12) := {0, 1, 3, 4, 7, 9}
  ∀ ζ : ℂ, ζ ^ 12 = 1 → (∀ m : ℕ, 1 ≤ m → m < 12 → ζ ^ m ≠ 1) →
    ∃ L : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ),
      ∀ a₀ a₁ : Fin 12 → ℂ,
        ∃ w : ZMod 12 → Fin 4 → ℂ,
          ∀ c ∈ J12, L (cyclicChannelShift ℂ 12 4 c w) = a₀ + (ζ ^ c.val) • a₁

/-- **Open Blueprint Target (`README.md` §II.2 Theorem 2B Note & §III.2 Bullet 2).**
Multi-class / multi-band coupling target: whether two linear class-uniform stages `K₁, K₂` with
constant class counts `M₁, M₂` suffer a macroscopic rank error `rank(τ - K₂ K₁) ≥ ε(M₁, M₂) b d^2`. -/
def OpenTarget_MacroscopicTwoStageRankDeficitSpec : Prop :=
  ∀ (M₁ M₂ : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
    ∃ (ε : ℝ) (D₀ : ℕ), 0 < ε ∧
      ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d]
        (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
        (d : F) ≠ 0 →
        D₀ ≤ d →
        1 ≤ b →
        ClassUniform p₁ K₁ →
        ClassUniform p₂ K₂ →
        ε * (b : ℝ) * ((d : ℝ) ^ 2) ≤
          (finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) : ℝ)

end BoundedArityDecoders
