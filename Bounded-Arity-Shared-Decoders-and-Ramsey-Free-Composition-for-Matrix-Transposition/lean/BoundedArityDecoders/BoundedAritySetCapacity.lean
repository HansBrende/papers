import Transpose.Statement
import SharedDecoders.Model
import SharedDecoders.CapacitySetCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Formal Specifications — Part I: Bounded-Arity Arbitrary-Set Shared-Decoder Capacity

Statement-only formal specifications of all claims in `README.md` concerning
Breakthrough 1 (Overturning the Nonlinear Fibre Barrier via Bounded-Arity Shared Decoders)
and Blueprint Part I:

* `CanonicalWordAlphabet`, `SyntacticCellSupport`, `SyntacticColumnSupport`, and
  `IsBoundedAritySetCode`: arbitrary (possibly nonlinear) codes `C ⊆ Σ^{d × d}` with an
  arbitrary `M`-class partition `p`, broken output set `E`, and deterministic class rules `f_m`
  whose `r`-th output coordinate depends syntactically on a footprint `Q m r` of at most `Δ`
  cells.
* Proof-spine specifications:
  - `SelfReferentialAndCleanCountSpec` (shifted-footprint self-reference equivalence and clean
    entry count),
  - `OneHopRecoverableInjectiveSpec` (acyclic 1-hop unique determination outside `Rec(Ω)`),
  - `ExistsRecoverableSubsetBoundSpec` (Bernoulli(`θ = Δ/(Δ + 1)`) per-cell recovery probability,
    first-moment expectation lower bound, and deterministic witness `Ω_*`).
* `Theorem1_BoundedAritySetCapacitySpec`: the unconditional arbitrary-set bound
  `log_{|Σ|} |C| ≤ d^2 - (d^2 - |E| - d M Δ) * Δ^Δ / (Δ + 1)^(Δ + 1)`.
* Boundary controls & corollaries:
  - `BoundaryControl_DeficitVanishesAtDeltaEqDSpec` (`Δ = d` algebraic boundary, explicit
    `d`-column / `(2 d - 1)`-cell row-0 phase-beacon multiplexing witness, and Paper 19
    `Theorem A.1` / `Corollary A.2` unrestricted `d`-column / `d^2`-cell set capacity),
  - `GrowingClassesPositiveDeficitSpec` (`|E| ≤ δ d^2`, `M ≤ η d / Δ`, rate deficit
    `≥ (1 - δ - η) / (e (Δ + 1))`),
  - `OneClassArityTwoHalfBarrierQuestion`, `OneClassBoundedArityHalfBarrierQuestion`,
    `OneClassBoundedArityCodingGainAboveHalfQuestion`, and
    `OneClassBoundedArityInverseArityScalingQuestion` (the finite `Δ = 2` and asymptotic
    `M = 1, Δ = O(1)` questions over canonical word width `|Σ| = 2^⌈log₂ d⌉`).
-/

namespace BoundedArityDecoders

open SharedDecoders
open scoped BigOperators

section Definitions

variable {d M : ℕ} {Sigma : Type*}

/-- Canonical word alphabet `{0, 1}^{b(d)}` with `b(d) = Transpose.entryBits d = max(1, ⌈log₂ d⌉)`,
matching `|Σ| = 2^⌈log₂ d⌉` for `d ≥ 2` (`README.md` §I, §II.1, §III.1). -/
abbrev CanonicalWordAlphabet (d : ℕ) := Fin (Transpose.entryBits d) → Bool

/-- Coordinate `(f m Y) r` depends syntactically on at most `Delta` cells `Q m r` of `Y`. -/
def SyntacticCellSupport (Delta : ℕ)
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d)) : Prop :=
  (∀ m r, (Q m r).card ≤ Delta) ∧
    ∀ m r (Y₁ Y₂ : State d Sigma),
      (∀ q ∈ Q m r, Y₁ q.1 q.2 = Y₂ q.1 q.2) → f m Y₁ r = f m Y₂ r

/-- Coordinate `(f m Y) r` depends syntactically on at most `ColDelta` columns `Qcol m r` of `Y`. -/
def SyntacticColumnSupport (ColDelta : ℕ)
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Qcol : Fin M → ZMod d → Finset (ZMod d)) : Prop :=
  (∀ m r, (Qcol m r).card ≤ ColDelta) ∧
    ∀ m r (Y₁ Y₂ : State d Sigma),
      (∀ i : ZMod d, ∀ u ∈ Qcol m r, Y₁ i u = Y₂ i u) → f m Y₁ r = f m Y₂ r

/-- An arbitrary (not necessarily linear) subset `C ⊆ Σ^{d × d}` is validated outside broken
output coordinates `(r, c) ∈ E` by an `M`-class family of deterministic rules of cell cone
arity at most `Delta`. Note that `(r, c) ∈ E` is indexed in transposed output coordinates
(`row r, column c` of `K(X) ≈ Xᵀ`), whereas `X c r` denotes input matrix entry `(c, r)`. -/
def IsBoundedAritySetCode (Delta : ℕ)
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)) : Prop :=
  SyntacticCellSupport Delta f Q ∧
    ∀ X ∈ C, ∀ r c : ZMod d, (r, c) ∉ E → f (p c) (rot c X) r = X c r

/-- Shifted read footprint `F_{c, r} = {(r', c + u) : (r', u) ∈ Q_{p(c), r}}` in `(row, col)`
coordinates of `X` read when evaluating `(f (p c) (rot c X)) r`.
Note on self-reference (`(c, r) ∈ F_{c, r}`): `(c, r) ∈ shiftedFootprint p Q c r` holds iff
`(c, r - c) ∈ Q (p c) r`; for each fixed `(m, r)`, `c ↦ (c, r - c)` is injective on `ZMod d`,
so `|Q m r| ≤ Delta` bounds the number of self-referential `c` in class `m` by `Delta`. -/
def shiftedFootprint [DecidableEq (ZMod d)]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (c r : ZMod d) : Finset (ZMod d × ZMod d) :=
  (Q (p c) r).image (fun q => (q.1, c + q.2))

/-- Clean matrix entries `(c, r)` of `X`: output `(r, c)` is unbroken (`(r, c) ∉ E`) and `(c, r)`
does not lie in its own shifted read footprint `F_{c, r}`. -/
def cleanEntries [Fintype (ZMod d)] [DecidableEq (ZMod d)]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d)) : Finset (ZMod d × ZMod d) :=
  Finset.univ.filter (fun cr => (cr.2, cr.1) ∉ E ∧ cr ∉ shiftedFootprint p Q cr.1 cr.2)

/-- Deterministic one-hop recoverable set `Rec(Ω)` of matrix cells `(c, r)` outside `Ω` whose
output `(r, c)` is unbroken and whose entire shifted footprint `F_{c, r}` lies inside `Ω`. -/
def recoverableCells [Fintype (ZMod d)] [DecidableEq (ZMod d)]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E Ω : Finset (ZMod d × ZMod d)) : Finset (ZMod d × ZMod d) :=
  Finset.univ.filter (fun cr =>
    cr ∉ Ω ∧ (cr.2, cr.1) ∉ E ∧ shiftedFootprint p Q cr.1 cr.2 ⊆ Ω)

/-- Product Bernoulli(`θ`) probability mass `θ^|Ω| (1 - θ)^(d^2 - |Ω|)` of a subset
`Ω ⊆ (ZMod d)^2`. -/
def bernoulliSubsetWeight (d : ℕ) (θ : ℝ) (Ω : Finset (ZMod d × ZMod d)) : ℝ :=
  θ ^ Ω.card * (1 - θ) ^ (d ^ 2 - Ω.card)

end Definitions

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Claim (Clean Entry Count, `README.md` §II.1 Proof Paragraph 1).**
1. `(c, r) ∈ F_{c, r}` holds iff `(c, r - c) ∈ Q (p c) r`.
2. For any footprints `Q` with `|Q m r| ≤ Delta`, at most `d * M * Delta` entries `(c, r)` are
   self-referential (`(c, r) ∈ F_{c, r}`), leaving at least `d^2 - |E| - d * M * Delta` clean
   entries `(c, r)` with `(r, c) ∉ E`, `(c, r) ∉ F_{c, r}`, and `|F_{c, r}| ≤ Delta`. -/
def SelfReferentialAndCleanCountSpec : Prop :=
  ∀ (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d)),
    (∀ c r : ZMod d, (c, r) ∈ shiftedFootprint p Q c r ↔ (c, r - c) ∈ Q (p c) r) ∧
    ((∀ m r, (Q m r).card ≤ Delta) →
      d ^ 2 ≤ (cleanEntries p Q E).card + E.card + d * M * Delta ∧
        ∀ cr ∈ cleanEntries p Q E, (shiftedFootprint p Q cr.1 cr.2).card ≤ Delta)

/-- **Claim (One-Hop Acyclic Determination, `README.md` §II.1 Proof Paragraph 2).**
For every fixed subset `Ω ⊆ (Z/d)^2`, every codeword `X ∈ C` is uniquely determined by its
restriction to `(Z/d)^2 \ Rec(Ω)`, yielding `|C| ≤ |Σ|^(d^2 - |Rec(Ω)|)`. -/
def OneHopRecoverableInjectiveSpec : Prop :=
  ∀ (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    IsBoundedAritySetCode Delta p E f Q C →
    ∀ Ω : Finset (ZMod d × ZMod d),
      (∀ X₁ ∈ C, ∀ X₂ ∈ C,
        (∀ cr : ZMod d × ZMod d, cr ∉ recoverableCells p Q E Ω → X₁ cr.1 cr.2 = X₂ cr.1 cr.2) →
        X₁ = X₂) ∧
      Nat.card C ≤ (Fintype.card Sigma) ^ (d ^ 2 - (recoverableCells p Q E Ω).card)

/-- **Claim (Bernoulli First-Moment Recovery Witness, `README.md` §II.1 Proof Paragraph 2).**
Sampling `Ω ⊆ (Z/d)^2` independently with probability `θ = Delta / (Delta + 1)` (`Delta ≥ 1`):
1. For each clean cell `cr ∈ cleanEntries p Q E`, the exact recovery probability equals
   `(1 - θ) * θ ^ |F_{c, r}| ≥ Delta^Delta / (Delta + 1)^(Delta + 1)`;
2. The expected recoverable size `E[|Rec(Ω)|]` is at least
   `|cleanEntries p Q E| * Delta^Delta / (Delta + 1)^(Delta + 1)`;
3. Hence there exists a deterministic subset `Ω_* ⊆ (Z/d)^2` with
   `|Rec(Ω_*)| ≥ (d^2 - |E| - d M Delta) * Delta^Delta / (Delta + 1)^(Delta + 1)`. -/
def ExistsRecoverableSubsetBoundSpec : Prop :=
  ∀ (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d)),
    1 ≤ Delta →
    (∀ m r, (Q m r).card ≤ Delta) →
    let θ : ℝ := (Delta : ℝ) / ((Delta + 1 : ℝ))
    let p_min : ℝ := (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))
    (∀ cr ∈ cleanEntries p Q E,
      (∑ Ω ∈ (Finset.univ : Finset (Finset (ZMod d × ZMod d))).filter
          (fun Ω => cr ∈ recoverableCells p Q E Ω),
        bernoulliSubsetWeight d θ Ω) =
        (1 - θ) * θ ^ (shiftedFootprint p Q cr.1 cr.2).card ∧
      p_min ≤ (1 - θ) * θ ^ (shiftedFootprint p Q cr.1 cr.2).card) ∧
    ((cleanEntries p Q E).card : ℝ) * p_min ≤
      (∑ Ω : Finset (ZMod d × ZMod d),
        bernoulliSubsetWeight d θ Ω * ((recoverableCells p Q E Ω).card : ℝ)) ∧
    ∃ Ω : Finset (ZMod d × ZMod d),
      ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) * p_min ≤
        ((recoverableCells p Q E Ω).card : ℝ)

/-- **Theorem 1 (`README.md` §II.1 — Bounded-Arity Arbitrary-Set Shared-Decoder Deficit).**
For any finite alphabet `Σ` (`|Σ| ≥ 2`, including canonical word width `CanonicalWordAlphabet d`
with `|Σ| = 2^⌈log₂ d⌉`), any nonempty subset `C ⊆ Σ^{d × d}`, any `M`-class partition
`p : Z/d → Fin M`, any broken output set `E ⊆ (Z/d)^2`, and any deterministic rules `f` of
syntactic cell cone arity at most `Delta ≥ 1`,
`log_{|Σ|} |C| ≤ d^2 - (d^2 - |E| - d M Delta) * Delta^Delta / (Delta + 1)^(Delta + 1)`. -/
def Theorem1_BoundedAritySetCapacitySpec : Prop :=
  (∀ d : ℕ, 2 ≤ d → Fintype.card (CanonicalWordAlphabet d) = 2 ^ Transpose.entryBits d) ∧
  ∀ (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    2 ≤ Fintype.card Sigma →
    1 ≤ M →
    1 ≤ Delta →
    C.Nonempty →
    IsBoundedAritySetCode Delta p E f Q C →
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
      (d : ℝ) ^ 2 -
        ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))

/-- **Boundary Control 1 (`README.md` §I.2 Wall 1, §II.1 Paragraph 1 & Bullet 1).**
1. At `Delta = d` (`M ≥ 1`), Theorem 1's deficit coefficient `d^2 - |E| - d M Delta` is `≤ 0`.
2. Right at **exact cell cone arity `Delta = d`** (`IsBoundedAritySetCode d`), a single (`M = 1,
   E = ∅`) anti-diagonal partition decoder (`Q 0 r = {(u, r - u) : u ∈ ZMod d}`) achieves
   `|C| = (|Σ|^d / d)^d` (rate `1 - O((log_{|Σ|} d) / d) → 1`) for all `d ≥ 2` and `|Σ| ≥ 2`.
3. Right at full column inspection (`ColDelta = d` columns of row `0`, cell cone arity
   `2 * d - 1 = Θ(d)`), a single (`M = 1, E = ∅`) phase-beacon multiplexing decoder locates a
   unique marker in row `0` at column `-c` and multiplexes `X c r`, achieving
   `|C| ≥ |Σ|^(d * (d - 1))` (rate `≥ 1 - 1 / d → 1`) for all `d ≥ 2` and `|Σ| ≥ 2`.
4. With full matrix inspection (`ColDelta = d`, `Delta = d^2`), Paper 19 `Theorem A.1` /
   `Corollary A.2` achieves `|C| ≥ |Σ|^(d^2) / d` for prime `d` (rate `≥ 1 - (log_{|Σ|} d) / d^2`)
   and `|C| ≥ |Σ|^(d^2) / (2 d)` for all `d ≥ 2`. -/
def BoundaryControl_DeficitVanishesAtDeltaEqDSpec : Prop :=
  (∀ (d M : ℕ) (E : Finset (ZMod d × ZMod d)),
    1 ≤ M →
    (d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (d : ℝ) ≤ 0) ∧
  (∀ (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma],
    2 ≤ d → 2 ≤ Fintype.card Sigma →
    ∃ (C : Set (State d Sigma))
      (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d)),
      IsBoundedAritySetCode d (fun _ => 0) ∅ f Q C ∧
      Nat.card C = ((Fintype.card Sigma) ^ d / d) ^ d) ∧
  (∀ (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma],
    2 ≤ d → 2 ≤ Fintype.card Sigma →
    ∃ (C : Set (State d Sigma))
      (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
      (Qcol : Fin 1 → ZMod d → Finset (ZMod d)),
      IsBoundedAritySetCode (2 * d - 1) (fun _ => 0) ∅ f Q C ∧
      SyntacticColumnSupport d f Qcol ∧
      (Fintype.card Sigma) ^ (d * (d - 1)) ≤ Nat.card C) ∧
  (∀ (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma],
    d.Prime → 2 ≤ Fintype.card Sigma →
    ∃ (C : Set (State d Sigma))
      (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d)),
      IsBoundedAritySetCode (d ^ 2) (fun _ => 0) ∅ f Q C ∧
      (Fintype.card Sigma) ^ (d ^ 2) ≤ d * Nat.card C) ∧
  (∀ (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma],
    2 ≤ d → 2 ≤ Fintype.card Sigma →
    ∃ (C : Set (State d Sigma))
      (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d)),
      IsBoundedAritySetCode (d ^ 2) (fun _ => 0) ∅ f Q C ∧
      (Fintype.card Sigma) ^ (d ^ 2) ≤ 2 * d * Nat.card C)

/-- **Corollary (`README.md` §II.1 Bullet 2 & §III.1 — Growing Classes & Broken Outputs).**
Whenever broken outputs satisfy `|E| ≤ δ d^2` and class count satisfies `M ≤ η d / Delta` with
`δ + η < 1`, any nonempty `(Delta, p, E)`-bounded-arity nonlinear shared code `C ⊆ Σ^{d × d}` has
normalized rate at most `1 - (1 - δ - η) * Delta^Delta / (Delta + 1)^(Delta + 1)`, with
`Delta^Delta / (Delta + 1)^(Delta + 1) > 1 / (e * (Delta + 1))`. -/
def GrowingClassesPositiveDeficitSpec : Prop :=
  ∀ (d M Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (δ η : ℝ)
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    2 ≤ Fintype.card Sigma →
    1 ≤ M →
    1 ≤ Delta →
    0 ≤ δ →
    0 ≤ η →
    δ + η < 1 →
    (E.card : ℝ) ≤ δ * (d : ℝ) ^ 2 →
    (M : ℝ) ≤ η * (d : ℝ) / (Delta : ℝ) →
    C.Nonempty →
    IsBoundedAritySetCode Delta p E f Q C →
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      1 - (1 - δ - η) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))) ∧
    1 / (Real.exp 1 * (Delta + 1 : ℝ)) <
      (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))

/-- **Open Finite/Asymptotic Question — Arity `Δ = 2` (`README.md` §II.1 Bullet 3).**
Whether `M = 1`, cell-arity-`Δ = 2` nonlinear shared codes on `Σ^{d × d}` (`|Σ| ≥ 2`) obey the
`1/2 + o(1)` rate bound (improving Theorem 1's unconditional `1 - 4/27 = 23/27` upper bound). -/
def OneClassArityTwoHalfBarrierQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, ∀ (d : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    D₀ ≤ d →
    2 ≤ Fintype.card Sigma →
    C.Nonempty →
    IsBoundedAritySetCode 2 (fun _ => 0) ∅ f Q C →
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      (1 : ℝ) / 2 + ε

/-- **Open Asymptotic Dichotomy — Branch A (`README.md` §II.1 Bullet 3 & §III.1).**
Every fixed cell cone arity `Delta = O(1)` (`Delta ≥ 1`) with `M = 1` over canonical word
alphabet `CanonicalWordAlphabet d` (`|Σ| = 2^⌈log₂ d⌉`) obeys the `1/2 + o(1)` rate bound. -/
def OneClassBoundedArityHalfBarrierQuestion : Prop :=
  ∀ (Delta : ℕ), 1 ≤ Delta → ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ,
    ∀ (d : ℕ) [NeZero d]
      (f : Fin 1 → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
      (C : Set (State d (CanonicalWordAlphabet d))),
      max D₀ 2 ≤ d →
      C.Nonempty →
      IsBoundedAritySetCode Delta (fun _ => 0) ∅ f Q C →
      Real.log (Nat.card C : ℝ) /
          (Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) * (d : ℝ) ^ 2) ≤
        (1 : ℝ) / 2 + ε

/-- **Open Asymptotic Dichotomy — Branch B (`README.md` §II.1 Bullet 3 & §III.1).**
Exact logical negation of Branch A: some bounded cell arity `Delta ≥ 1` with `M = 1` over
`CanonicalWordAlphabet d` achieves rate strictly above `1/2 + c` infinitely often. -/
def OneClassBoundedArityCodingGainAboveHalfQuestion : Prop :=
  ∃ (Delta : ℕ), 1 ≤ Delta ∧ ∃ c : ℝ, 0 < c ∧ ∀ D₀ : ℕ,
    ∃ (d : ℕ) (_ : NeZero d)
      (f : Fin 1 → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
      (C : Set (State d (CanonicalWordAlphabet d))),
      max D₀ 2 ≤ d ∧
      C.Nonempty ∧
      IsBoundedAritySetCode Delta (fun _ => 0) ∅ f Q C ∧
      ((1 : ℝ) / 2 + c) *
          (Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) * (d : ℝ) ^ 2) <
        Real.log (Nat.card C : ℝ)

/-- **Open Asymptotic Scaling Question (`README.md` §III.1 Bullet 2 — `1 - Θ(1 / Delta)` Regime).**
Whether `M = 1` bounded-arity nonlinear shared codes over `CanonicalWordAlphabet d` achieve rate
`1 - O(1 / Delta)` matching the `1 - Ω(1 / Delta)` upper bound of Theorem 1. -/
def OneClassBoundedArityInverseArityScalingQuestion : Prop :=
  ∃ C_gain : ℝ, 0 < C_gain ∧ ∀ (Delta : ℕ), 2 ≤ Delta → ∀ D₀ : ℕ,
    ∃ (d : ℕ) (_ : NeZero d)
      (f : Fin 1 → State d (CanonicalWordAlphabet d) → (ZMod d → CanonicalWordAlphabet d))
      (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
      (C : Set (State d (CanonicalWordAlphabet d))),
      max D₀ 2 ≤ d ∧
      C.Nonempty ∧
      IsBoundedAritySetCode Delta (fun _ => 0) ∅ f Q C ∧
      (1 - C_gain / (Delta : ℝ)) *
          (Real.log (Fintype.card (CanonicalWordAlphabet d) : ℝ) * (d : ℝ) ^ 2) ≤
        Real.log (Nat.card C : ℝ)

end BoundedArityDecoders
