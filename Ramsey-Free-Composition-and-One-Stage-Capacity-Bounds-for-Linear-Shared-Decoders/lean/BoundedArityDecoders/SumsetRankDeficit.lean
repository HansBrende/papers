import SharedDecoders.Model
import SharedDecoders.CompositionLinear
import SharedDecoders.CompositionRankField
import BoundedArityDecoders.AffineCubeComposition
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sumset Polynomial Recurrence & Log-Power Rank Deficit

Definitions and proposition types for Theorem 2B, its five-step proof spine, and its `d = 12`
abstract band control (proved in `BoundedArityDecoders.SumsetRankDeficitProofs`):

* `HasUnshiftedMonochromaticSumset` & `HasShiftedMonochromaticSumset`: unshifted and shifted
  `(2 M₂)`-fold monochromatic sumsets with `|J₀| = k`, `|B_t| = k + 1`, and bounded diameters.
* Proof-spine specifications (Steps 1–5):
  - `UnshiftedToShiftedSumsetSpec` (Step 1: shifting `B_t` to `B̃_t = B_t - b_{t, 0}` with
    `0 ∈ B̃_t`, `diam(B̃_t) ≤ L₀`, and all subset sums `J̃₀ + ∑_{t ∈ S} B̃_t` in class `m₁`),
  - `VandermondeArbitrarySubsetInjectiveSpec` & `StackedBandPullbackInjectiveSpec`
    (Step 2: Vandermonde evaluation injectivity on arbitrary `J̃₀` and pullback subspace `W`
    inside `ColumnAmbient (bandRowSpace χ p₂ k)` with `dim W ≥ b k d - r`),
  - `SumsetAnnihilatingPolynomialSpec` (Step 3: nonzero polynomial supported on `B̃_t`
    annihilating frequencies `0, …, k - 1` with `dim ker P_t(T) ≤ b M₂ k L₀`),
  - `SumsetTwoHopRankBoundSpec` (Step 4: both `r ≥ (b k / 2)(d - ∑ diam(B̃_t))` and
    `r ≥ b k d / 4` when `diam(B̃_t) ≤ d / (4 M₂)`),
  - `IteratedKovariSosTuranSumsetSpec` (Step 5: iterated Kővári–Sós–Turán extraction at scale
    `k = Θ_{M₁, M₂}((log d)^(1 / (2 M₂ - 1)))`).
* `Theorem2B_TwoStageLogPowerRankDeficitSpec`:
  `rank(τ - K₂ K₁) ≥ c(M₁, M₂) * b * d * (log d)^(1 / (2 M₂ - 1))`.
* `Control_D12SingleClassAbstractBandSpec`: `24`-dimensional `4`-channel (`q = 4`) band subspace
  on `J = {0, 1, 3, 4, 7, 9} ⊆ ZMod 12` with `12`-coordinate readout (`b = 1, M₂ = 2, k = 2`
  where `24 = b k d`, or one readout lane of `bandRowSpace (b := 2) χ (fun _ => 0) 2` where
  `b = 2, M₂ = 1, k = 2` and `q = b M₂ k = 4`).
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

section Definitions

/-- Unshifted `(nSteps + 1)`-fold monochromatic sumset `J₀ + B₁ + ⋯ + B_{nSteps} ⊆ {c | p₁ c = m₁}`
with `|J₀| = k`, `|B_t| = k + 1`, and `B_t ⊆ [0, L₀]`. -/
def HasUnshiftedMonochromaticSumset {d M₁ nSteps : ℕ}
    (p₁ : ZMod d → Fin M₁) (m₁ : Fin M₁) (k L₀ : ℕ)
    (J₀ : Finset (ZMod d))
    (B : Fin nSteps → Finset ℕ) : Prop :=
  J₀.card = k ∧
  (∀ t : Fin nSteps, (B t).card = k + 1 ∧ ∀ x ∈ B t, x ≤ L₀) ∧
  ∀ c₀ ∈ J₀, ∀ b : Fin nSteps → ℕ, (∀ t, b t ∈ B t) →
    p₁ (c₀ + ∑ t : Fin nSteps, (b t : ZMod d)) = m₁

/-- Shifted `(nSteps + 1)`-fold monochromatic sumset:
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

/-! ### Theorem Statement Specifications -/

/-- **Claim (Shifting `B_t` so `0 ∈ B̃_t` for All `t`).**
Given any unshifted monochromatic sumset `J₀ + B₁ + ⋯ + B_{nSteps} ⊆ {c | p₁ c = m₁}` with
`|J₀| = k`, `|B_t| = k + 1`, and `B_t ⊆ [0, L₀]`, shifting `B_t` by its minimum `b_{t, 0} ∈ B_t`
produces `B̃_t` with `0 ∈ B̃_t`, `|B̃_t| = k + 1`, `B̃_t ⊆ [0, L₀]`, and shifted base
`J̃₀ = J₀ + ∑_t b_{t, 0}` (`|J̃₀| = k`) such that for **every** subset `S ⊆ Fin nSteps`,
`J̃₀ + ∑_{t ∈ S} B̃_t ⊆ {c | p₁ c = m₁}`. -/
def UnshiftedToShiftedSumsetSpec : Prop :=
  ∀ (d M₁ nSteps k L₀ : ℕ) [NeZero d]
    (p₁ : ZMod d → Fin M₁) (m₁ : Fin M₁)
    (J₀ : Finset (ZMod d)) (B : Fin nSteps → Finset ℕ),
    HasUnshiftedMonochromaticSumset p₁ m₁ k L₀ J₀ B →
    ∃ (J₀_tilde : Finset (ZMod d)) (B_tilde : Fin nSteps → Finset ℕ),
      HasShiftedMonochromaticSumset p₁ m₁ k J₀_tilde B_tilde (fun _ => L₀) ∧
      ∀ (S : Finset (Fin nSteps)) (c₀ : ZMod d), c₀ ∈ J₀_tilde →
        ∀ b : Fin nSteps → ℕ, (∀ t ∈ S, b t ∈ B_tilde t) →
          p₁ (c₀ + ∑ t ∈ S, (b t : ZMod d)) = m₁

/-- **Claim (Arbitrary-Subset Vandermonde Injectivity).**
Over any field `E` with an injective additive character `χ : AddChar (ZMod d) E`, for any
subset `J₀ : Finset (ZMod d)` of cardinality `k`, evaluation of degree-`< k` character
polynomials `∑_{ν < k} χ(ν c) • a_ν` on `c ∈ J₀` is injective. -/
def VandermondeArbitrarySubsetInjectiveSpec : Prop :=
  ∀ (d k : ℕ) [NeZero d] (E V : Type*) [Field E] [AddCommGroup V] [Module E V]
    (χ : AddChar (ZMod d) E) (J₀ : Finset (ZMod d)),
    Function.Injective χ →
    J₀.card = k →
    Function.Injective (charBandEval (k := k) (V := V) χ J₀)

/-- **Claim (Pullback Subspace `W` with `dim W ≥ b k d - r`).**
Over any field `E` with an injective additive character `χ : AddChar (ZMod d) E`, for any
two linear class-uniform maps `K₁, K₂` on `State d (Fin b → E)` (`k ≤ d`) and any subset
`J₀ ⊆ {c | p₁ c = m₁}` with `|J₀| = k` and class-`m₁` linear decoder `f₁_m₁`, there exists a
subspace `W ≤ ColumnAmbient (bandRowSpace (b := b) χ p₂ k)` such that:
1. `b * k * d ≤ finrank E W + finrank E (range (swapLinear E - K₂ ∘ K₁))` (`dim W ≥ b k d - r`);
2. Stacked evaluation `x ↦ (c ↦ f₁_m₁ (rot c (columnAmbientEmbed H x)))_{c ∈ J₀}` is injective on `W`. -/
def StackedBandPullbackInjectiveSpec : Prop :=
  ∀ (E : Type*) [Field E] (d b M₁ M₂ k : ℕ) [NeZero d]
    (χ : AddChar (ZMod d) E)
    (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂) (m₁ : Fin M₁)
    (J₀ : Finset (ZMod d))
    (K₁ K₂ : State d (Fin b → E) →ₗ[E] State d (Fin b → E))
    (f₁ : Fin M₁ → State d (Fin b → E) →ₗ[E] (ZMod d → Fin b → E)),
    Function.Injective χ →
    k ≤ d →
    J₀.card = k →
    (∀ c ∈ J₀, p₁ c = m₁) →
    (∀ X c i, K₁ X i c = f₁ (p₁ c) (rot c X) i) →
    ClassUniform p₂ K₂ →
    ∃ W : Submodule E (ColumnAmbient (bandRowSpace (b := b) χ p₂ k)),
      b * k * d ≤
        finrank E W +
          finrank E (LinearMap.range (swapLinear E (d := d) (A := Fin b → E) - K₂.comp K₁)) ∧
      ∀ x ∈ W,
        (∀ c ∈ J₀, f₁ m₁ (rot c (columnAmbientEmbed (bandRowSpace (b := b) χ p₂ k) x)) = 0) →
          x = 0

/-- **Claim (Sparse Sumset Annihilating Polynomial).**
For any injective character `χ : AddChar (ZMod d) E` and any `B_t : Finset ℕ` with `0 ∈ B_t`,
`|B_t| = k + 1`, and `∀ x ∈ B_t, x ≤ L₀`, there exists a nonzero polynomial `P : Polynomial E`
supported in `B_t` of degree `≤ L₀` annihilating `{χ(ν · -) : 0 ≤ ν < k}`, and on any
`q`-channel cyclic module `ZMod d → Fin q → E` (hence on `ColumnAmbient (bandRowSpace χ p₂ k)`
where `q = dim H ≤ b * M₂ * k`), `finrank E (ker P(T))` is bounded by `q * L₀`
(hence `≤ b * M₂ * k * L₀`). -/
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

/-- **Claim (Two-Stage Sumset Recurrence Rank Bound).**
Over any field `F` with `(d : F) ≠ 0`, if `p₁` admits a shifted `(2 M₂)`-fold monochromatic
sumset `(J₀, B, diamB)` of width `k ≥ 1` (`k ≤ d`) with `∑ t, diamB t ≤ d`, then any two linear
class-uniform stages `K₁, K₂` on `State d (Fin b → F)` satisfy:
1. `b * k * (d - ∑ t, diamB t) ≤ 2 * rank(τ - K₂ K₁)`, and
2. when `∀ t, diamB t ≤ d / (4 * M₂)`, `b * k * d ≤ 4 * rank(τ - K₂ K₁)` (`r ≥ b k d / 4`). -/
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
    k ≤ d →
    ∑ t : Fin (2 * M₂ - 1), diamB t ≤ d →
    HasShiftedMonochromaticSumset p₁ m₁ k J₀ B diamB →
    ClassUniform p₁ K₁ →
    ClassUniform p₂ K₂ →
    let r := finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁))
    b * k * (d - ∑ t : Fin (2 * M₂ - 1), diamB t) ≤ 2 * r ∧
    ((∀ t : Fin (2 * M₂ - 1), diamB t ≤ d / (4 * M₂)) → b * k * d ≤ 4 * r)

/-- **Claim (Iterated Kővári–Sós–Turán Sumset Extraction).**
For every `M₁ ≥ 1` and `M₂ ≥ 1`, there exist `0 < c_lo ≤ C_hi` and `D₀` such that for all
`d ≥ D₀`, every `M₁`-coloring `p₁ : ZMod d → Fin M₁` contains an unshifted (hence also shifted)
`(2 M₂)`-fold monochromatic sumset in `[0, d / (4 M₂)]` at width scale
`k = Θ_{M₁, M₂}((log d)^(1 / (2 M₂ - 1)))` (`c_lo * (log d)^α ≤ k ≤ C_hi * (log d)^α` and `k ≤ d`). -/
def IteratedKovariSosTuranSumsetSpec : Prop :=
  ∀ (M₁ M₂ : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
    ∃ (c_lo C_hi : ℝ) (D₀ : ℕ), 0 < c_lo ∧ c_lo ≤ C_hi ∧
      ∀ (d : ℕ) [NeZero d] (p₁ : ZMod d → Fin M₁), D₀ ≤ d →
        ∃ (m₁ : Fin M₁) (k : ℕ) (J₀ : Finset (ZMod d))
          (B : Fin (2 * M₂ - 1) → Finset ℕ),
          1 ≤ k ∧
          k ≤ d ∧
          c_lo * (Real.log (d : ℝ)) ^ ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)) ≤ (k : ℝ) ∧
          (k : ℝ) ≤ C_hi * (Real.log (d : ℝ)) ^ ((1 : ℝ) / (2 * (M₂ : ℝ) - 1)) ∧
          HasUnshiftedMonochromaticSumset p₁ m₁ k (d / (4 * M₂)) J₀ B ∧
          ∃ (J₀' : Finset (ZMod d)) (B' : Fin (2 * M₂ - 1) → Finset ℕ),
            HasShiftedMonochromaticSumset p₁ m₁ k J₀' B' (fun _ => d / (4 * M₂))

/-- **Theorem 2B (Log-Power Two-Stage Rank Deficit Over Admissible Fields).**
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

/-- **Abstract `4`-Channel Band Control at `d = 12, k = 2` (`J = {0, 1, 3, 4, 7, 9}`).**
On the `4`-channel cyclic module `ZMod 12 → Fin 4 → ℂ` (`q = 4`, corresponding to `b = 1, M₂ = 2, k = 2`
where `24 = b k d`, or via `d12BandRowSpaceEquiv` to `bandRowSpace (b := 2) χ (fun _ => 0) 2`
where `b = 2, M₂ = 1, k = 2` and `12` of the `24` readout coordinates are read), on the
half-density subset `J = {0, 1, 3, 4, 7, 9} ⊆ ZMod 12` (`|J| = 6`), for every primitive `12`-th
root `ζ ∈ ℂ`, there exist a linear readout `L : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ)` and a
`24`-dimensional subspace `W ≤ (ZMod 12 → Fin 4 → ℂ)` (`finrank ℂ W = 24 = k * d`) on which
stacked evaluation over `J` is injective and realizes every pair of band coefficient vectors
`(a_0, a_1) ∈ (ℂ^12)^2` as `L (T_c w) = a_0 + ζ^c • a_1` for all `c ∈ J`. -/
def Control_D12SingleClassAbstractBandSpec : Prop :=
  let J12 : Finset (ZMod 12) := {0, 1, 3, 4, 7, 9}
  ∀ ζ : ℂ, ζ ^ 12 = 1 → (∀ m : ℕ, 1 ≤ m → m < 12 → ζ ^ m ≠ 1) →
    ∃ (W : Submodule ℂ (ZMod 12 → Fin 4 → ℂ))
      (L : (ZMod 12 → Fin 4 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ)),
      finrank ℂ W = 24 ∧
      (∀ w ∈ W, (∀ c ∈ J12, L (cyclicChannelShift ℂ 12 4 c w) = 0) → w = 0) ∧
      ∀ a₀ a₁ : Fin 12 → ℂ,
        ∃ w ∈ W, ∀ c ∈ J12, L (cyclicChannelShift ℂ 12 4 c w) = a₀ + (ζ ^ c.val) • a₁

end BoundedArityDecoders
