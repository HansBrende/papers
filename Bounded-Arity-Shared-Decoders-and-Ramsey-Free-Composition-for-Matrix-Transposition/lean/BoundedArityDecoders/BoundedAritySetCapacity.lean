import SharedDecoders.Model
import SharedDecoders.CapacitySetCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Formal Specifications — Part I: Bounded-Arity Arbitrary-Set Shared-Decoder Capacity

Statement-only formal specifications of all claims in `README.md` concerning
Breakthrough 1 (Overturning the Nonlinear Fibre Barrier via Bounded-Arity Shared Decoders)
and Blueprint Part I:

* `SyntacticCellSupport` and `IsBoundedAritySetCode`: arbitrary (possibly nonlinear) codes
  `C ⊆ Σ^{d × d}` with an arbitrary `M`-class partition `p`, broken output set `E`, and
  deterministic class rules `f_m` whose `r`-th output coordinate depends syntactically on a
  footprint `Q m r` of at most `Δ` cells.
* Proof-spine specifications:
  - `SelfReferentialAndCleanCountSpec` (counting self-referential vs. clean entries),
  - `OneHopRecoverableInjectiveSpec` (acyclic 1-hop unique determination outside `Rec(Ω)`),
  - `ExistsRecoverableSubsetBoundSpec` (probabilistic first-moment witness `Ω_*`).
* `Theorem1_BoundedAritySetCapacitySpec`: the unconditional arbitrary-set bound
  `log_{|Σ|} |C| ≤ d^2 - (d^2 - |E| - d M Δ) * Δ^Δ / (Δ + 1)^(Δ + 1)`.
* Boundary controls & corollaries:
  - `BoundaryControl_DeficitVanishesAtDeltaEqDSpec` (`Δ = d`),
  - `BoundaryControl_UnrestrictedOneClassSetCapacitySpec` (Paper 19 `Theorem A.1` / `Corollary A.2`),
  - `GrowingClassesPositiveDeficitSpec` (`|E| ≤ δ d^2`, `M ≤ η d / Δ`, rate deficit `≥ (1 - δ - η) / (e (Δ + 1))`),
  - `OneClassArityTwoMaxRateAtMostHalfQuestion` & `OneClassBoundedArityCodingGainAboveHalfQuestion`
    (the sharp finite/asymptotic rate question of Section II.1(3) and Section III.1).
-/

namespace BoundedArityDecoders

open SharedDecoders

section Definitions

variable {d M : ℕ} {Sigma : Type*}

/-- Coordinate `(f m Y) r` depends syntactically on at most `Delta` cells `Q m r` of `Y`. -/
def SyntacticCellSupport (Delta : ℕ)
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d)) : Prop :=
  (∀ m r, (Q m r).card ≤ Delta) ∧
    ∀ m r (Y₁ Y₂ : State d Sigma),
      (∀ q ∈ Q m r, Y₁ q.1 q.2 = Y₂ q.1 q.2) → f m Y₁ r = f m Y₂ r

/-- An arbitrary (not necessarily linear) subset `C ⊆ Σ^{d × d}` is validated outside broken
output coordinates `(r, c) ∈ E` by an `M`-class family of deterministic rules of cell cone
arity at most `Delta`. -/
def IsBoundedAritySetCode (Delta : ℕ)
    (p : ZMod d → Fin M)
    (E : Finset (ZMod d × ZMod d))
    (f : Fin M → State d Sigma → (ZMod d → Sigma))
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)) : Prop :=
  SyntacticCellSupport Delta f Q ∧
    ∀ X ∈ C, ∀ r c : ZMod d, (r, c) ∉ E → f (p c) (rot c X) r = X c r

/-- Shifted read footprint `F_{c, r} = {(r', c + u) : (r', u) ∈ Q_{p(c), r}}` in `(row, col)`
coordinates of `X` read when evaluating `(f (p c) (rot c X)) r`. -/
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

end Definitions

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Claim (Clean Entry Count, `README.md` §II.1 Proof Paragraph 1).**
For any footprints `Q` with `|Q m r| ≤ Delta`, at most `d * M * Delta` entries `(c, r)` are
self-referential (`(c, r) ∈ F_{c, r}`), leaving at least `d^2 - |E| - d * M * Delta` clean
entries `(c, r)` with `(r, c) ∉ E`, `(c, r) ∉ F_{c, r}`, and `|F_{c, r}| ≤ Delta`. -/
def SelfReferentialAndCleanCountSpec : Prop :=
  ∀ (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d)),
    (∀ m r, (Q m r).card ≤ Delta) →
    d ^ 2 ≤ (cleanEntries p Q E).card + E.card + d * M * Delta ∧
      ∀ cr ∈ cleanEntries p Q E, (shiftedFootprint p Q cr.1 cr.2).card ≤ Delta

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

/-- **Claim (Probabilistic First-Moment Recovery Witness, `README.md` §II.1 Proof Paragraph 2).**
Sampling `Ω` at density `θ = Delta / (Delta + 1)` guarantees the existence of a deterministic
subset `Ω_* ⊆ (Z/d)^2` with
`|Rec(Ω_*)| ≥ (d^2 - |E| - d M Delta) * Delta^Delta / (Delta + 1)^(Delta + 1)`. -/
def ExistsRecoverableSubsetBoundSpec : Prop :=
  ∀ (d M Delta : ℕ) [NeZero d]
    (p : ZMod d → Fin M)
    (Q : Fin M → ZMod d → Finset (ZMod d × ZMod d))
    (E : Finset (ZMod d × ZMod d)),
    1 ≤ Delta →
    (∀ m r, (Q m r).card ≤ Delta) →
    ∃ Ω : Finset (ZMod d × ZMod d),
      ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))) ≤
        ((recoverableCells p Q E Ω).card : ℝ)

/-- **Theorem 1 (`README.md` §II.1 — Bounded-Arity Arbitrary-Set Shared-Decoder Deficit).**
For any finite alphabet `Σ` (`|Σ| ≥ 2`), any subset `C ⊆ Σ^{d × d}`, any `M`-class partition
`p : Z/d → Fin M`, any broken output set `E ⊆ (Z/d)^2`, and any deterministic rules `f` of
syntactic cell cone arity at most `Delta ≥ 1`,
`log_{|Σ|} |C| ≤ d^2 - (d^2 - |E| - d M Delta) * Delta^Delta / (Delta + 1)^(Delta + 1)`. -/
def Theorem1_BoundedAritySetCapacitySpec : Prop :=
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
    IsBoundedAritySetCode Delta p E f Q C →
    Real.log (Nat.card C : ℝ) / Real.log (Fintype.card Sigma : ℝ) ≤
      (d : ℝ) ^ 2 -
        ((d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (Delta : ℝ)) *
          ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))

/-- **Boundary Control 1 (`README.md` §I.2 Wall 1 & §II.1 Bullet 1).**
At `Delta = d` (`M ≥ 1`), the Theorem 1 deficit lower bound `(d^2 - |E| - d M Delta)` is
nonpositive, matching Paper 19 `Theorem A.1` / `Corollary A.2`, where an unrestricted (`M = 1`)
deterministic shared decoder on nonlinear `C ⊆ Σ^{d × d}` achieves `|C| ≥ |Σ|^(d^2) / d` for
prime `d` (rate `≥ 1 - (log_{|Σ|} d) / d^2`) and `|C| ≥ |Σ|^(d^2) / (2 d)` for all `d ≥ 2`. -/
def BoundaryControl_DeficitVanishesAtDeltaEqDSpec : Prop :=
  (∀ (d M : ℕ) (E : Finset (ZMod d × ZMod d)),
    1 ≤ M →
    (d : ℝ) ^ 2 - (E.card : ℝ) - (d : ℝ) * (M : ℝ) * (d : ℝ) ≤ 0) ∧
  (∀ (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma],
    d.Prime → 2 ≤ Fintype.card Sigma →
    ∃ (C : Set (State d Sigma)) (f : State d Sigma → (ZMod d → Sigma)),
      (∀ X ∈ C, ∀ c : ZMod d, f (rot c X) = X c) ∧
      (Fintype.card Sigma) ^ (d ^ 2) ≤ d * Nat.card C) ∧
  (∀ (d : ℕ) [NeZero d] (Sigma : Type*) [Fintype Sigma],
    2 ≤ d → 2 ≤ Fintype.card Sigma →
    ∃ (C : Set (State d Sigma)) (f : State d Sigma → (ZMod d → Sigma)),
      (∀ X ∈ C, ∀ c : ZMod d, f (rot c X) = X c) ∧
      (Fintype.card Sigma) ^ (d ^ 2) ≤ 2 * d * Nat.card C)

/-- **Corollary (`README.md` §II.1 Bullet 2 & §III.1 — Growing Classes & Broken Outputs).**
Whenever broken outputs satisfy `|E| ≤ δ d^2` and class count satisfies `M ≤ η d / Delta` with
`δ + η < 1`, any `(Delta, p, E)`-bounded-arity nonlinear shared code `C ⊆ Σ^{d × d}` has
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
    IsBoundedAritySetCode Delta p E f Q C →
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      1 - (1 - δ - η) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))) ∧
    1 / (Real.exp 1 * (Delta + 1 : ℝ)) <
      (Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1))

/-- **Open Finite/Asymptotic Question — Branch A (`README.md` §II.1 Bullet 3 & §III.1).**
Whether `M = 1`, bounded-cell-arity (`Delta = O(1)`, starting at `Delta = 2`) nonlinear shared
codes on `Σ^{d × d}` (including canonical word width `|Σ| = 2^⌈log₂ d⌉`) obey the `1/2 + o(1)`
rate barrier. -/
def OneClassBoundedArityHalfBarrierQuestion (Delta : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, ∀ (d : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (f : Fin 1 → State d Sigma → (ZMod d → Sigma))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    D₀ ≤ d →
    2 ≤ Fintype.card Sigma →
    IsBoundedAritySetCode Delta (fun _ => 0) ∅ f Q C →
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      (1 : ℝ) / 2 + ε

/-- **Open Finite/Asymptotic Question — Branch B (`README.md` §II.1 Bullet 3 & §III.1).**
Whether `M = 1`, bounded-cell-arity `Delta = O(1)` nonlinear shared codes over canonical word
alphabets achieve a genuine coding gain `1/2 + c > 1/2` (up toward `1 - Θ(1 / Delta)`). -/
def OneClassBoundedArityCodingGainAboveHalfQuestion (Delta : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ D₀ : ℕ, ∃ (d : ℕ) (_ : NeZero d)
    (b : ℕ)
    (f : Fin 1 → State d (Fin b → Bool) → (ZMod d → (Fin b → Bool)))
    (Q : Fin 1 → ZMod d → Finset (ZMod d × ZMod d))
    (C : Set (State d (Fin b → Bool))),
    D₀ ≤ d ∧ 1 ≤ b ∧
    IsBoundedAritySetCode Delta (fun _ => 0) ∅ f Q C ∧
    ((1 : ℝ) / 2 + c) * (Real.log ((2 : ℝ) ^ b) * (d : ℝ) ^ 2) ≤
      Real.log (Nat.card C : ℝ)

end BoundedArityDecoders
