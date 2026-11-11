import Transpose.Statement
import BoundedArityDecoders.BoundedAritySetCapacity

/-!
# Formal Specifications — Section I & Part III.B: Native Sweep-Cone Interface to `(T)` & `Problem 9.4`

Statement-only formal specifications connecting Theorem 1 (`BoundedAritySetCapacity.lean`) to
the Machine Spine (`Transpose/Statement.lean`, `TCP` depth reduction, and `Problem 9.4`) as
described in `README.md` (§I Diagnosis and §III.3 Bullet 2):

* `TapeCodingConjectureNegationSpec`: the main target `¬ Transpose.LinearTimeTransposable` (`(T)`).
* `PeriodicHeadSweepTransducer`: a finite-state (`q_state`-state) sweep pass along columns
  `c : ZMod d` with `M_sched` periodic head-motion schedule classes, reading a fixed local
  cone stencil `stencil sClass r` of at most `Delta` relative cells on regular columns outside
  irregular steps `irregCols` and broken outputs `brokenOut`.
* `PeriodicSweepInducesBoundedAritySharedCodeSpec`: conditioning any (arbitrary, nonlinear!)
  cut fibre `C ⊆ Σ^{d × d}` on the finite control-state trace at sparse landmarks / schedule
  classes induces an `IsBoundedAritySetCode` directly on the nonlinear subfibre — requiring
  **no fibre linearity or affine-intersection hypothesis**.
* `PeriodicSweepNonlinearFibreDeficitSpec`: combining periodic sweep cone sharing with Theorem 1
  yields an unconditional positive entropy/rate deficit on nonlinear cut fibres whenever
  irregular/broken outputs have density `δ` and effective class count satisfies
  `M ≤ η d / Delta` (`δ + η < 1`).
-/

namespace BoundedArityDecoders

open SharedDecoders

section SweepDefinitions

/-- A finite-state periodic-motion sweep cone system over `State d Sigma` (`Problem 9.4` &
`README.md` §III.3 Bullet 2):
* `M_sched` periodic head-motion classes `schedClass : ZMod d → Fin M_sched`;
* `q_state` finite control states `Fin q_state` (`q_state ≥ 1`) entered at column `c` via
  `entryState : State d Sigma → ZMod d → Fin q_state`;
* local cone footprint `stencil : Fin M_sched → Fin q_state → ZMod d → Finset (ZMod d × ZMod d)`
  of cell arity at most `Delta`, together with transition readout `evalCell` depending only on
  the cells in `stencil`. -/
structure PeriodicHeadSweepSystem (d M_sched q_state Delta : ℕ) (Sigma : Type*) where
  schedClass : ZMod d → Fin M_sched
  entryState : State d Sigma → ZMod d → Fin q_state
  stencil : Fin M_sched → Fin q_state → ZMod d → Finset (ZMod d × ZMod d)
  evalCell : Fin M_sched → Fin q_state → State d Sigma → ZMod d → Sigma
  stencil_card_le : ∀ sc st r, (stencil sc st r).card ≤ Delta
  eval_local : ∀ sc st r (Y₁ Y₂ : State d Sigma),
    (∀ q ∈ stencil sc st r, Y₁ q.1 q.2 = Y₂ q.1 q.2) →
    evalCell sc st Y₁ r = evalCell sc st Y₂ r

/-- A `PeriodicHeadSweepSystem` recovers transposed entries `X c r` outside broken output set
`E` on an arbitrary nonlinear fibre `C ⊆ State d Sigma`. -/
def ValidatesNonlinearFibre {d M_sched q_state Delta : ℕ} {Sigma : Type*}
    (S : PeriodicHeadSweepSystem d M_sched q_state Delta Sigma)
    (E : Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)) : Prop :=
  ∀ X ∈ C, ∀ r c : ZMod d, (r, c) ∉ E →
    S.evalCell (S.schedClass c) (S.entryState X c) (rot c X) r = X c r

end SweepDefinitions

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Main Series Target `(T)` (`README.md` §I Line 3 & `Transpose/Statement.lean`).**
No deterministic multitape Turing machine transposes `d × d` matrices of `⌈log₂ d⌉`-bit words
in time `O(L)` (`L = d^2 ⌈log₂ d⌉`). -/
def TapeCodingConjectureNegationSpec : Prop :=
  ¬ Transpose.LinearTimeTransposable

/-- **Claim (`README.md` §III.3 Bullet 2 — Periodic Sweep Induces Bounded-Arity Shared Cones on
Nonlinear Fibres Without Linearization).**
Given any `PeriodicHeadSweepSystem` validating an arbitrary (nonlinear) cut fibre `C ⊆ Σ^{d × d}`
outside broken outputs `E`, conditioning `C` on the entry control states at `K_land` landmark
columns (`1 ≤ K_land`), where along each landmark interval `entryState X c` is determined by the
landmark's state (`M = M_sched * q_state` effective classes), partitions `C` into at most
`q_state ^ K_land` nonlinear subfibres, **each** of which is an `IsBoundedAritySetCode` with
at most `M_sched * q_state` classes and cell cone arity `Delta` — hence some nonlinear subfibre
`C' ⊆ C` has `|C| ≤ q_state ^ K_land * |C'|` and satisfies `IsBoundedAritySetCode` directly. -/
def PeriodicSweepInducesBoundedAritySharedCodeSpec : Prop :=
  ∀ (d M_sched q_state Delta K_land : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (S : PeriodicHeadSweepSystem d M_sched q_state Delta Sigma)
    (landmarks : Fin K_land → ZMod d)
    (landmarkOf : ZMod d → Fin K_land)
    (propState : Fin K_land → Fin q_state → ZMod d → Fin q_state)
    (E : Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    1 ≤ M_sched →
    1 ≤ q_state →
    1 ≤ Delta →
    C.Nonempty →
    ValidatesNonlinearFibre S E C →
    (∀ X ∈ C, ∀ c : ZMod d,
      S.entryState X c = propState (landmarkOf c) (S.entryState X (landmarks (landmarkOf c))) c) →
    ∃ (C' : Set (State d Sigma))
      (p : ZMod d → Fin (M_sched * q_state))
      (f : Fin (M_sched * q_state) → State d Sigma → (ZMod d → Sigma))
      (Q : Fin (M_sched * q_state) → ZMod d → Finset (ZMod d × ZMod d)),
      C' ⊆ C ∧
      Nat.card C ≤ (q_state ^ K_land) * Nat.card C' ∧
      IsBoundedAritySetCode Delta p E f Q C'

/-- **Claim (`README.md` §I.1–2, §II.1 Bullet 2 & §III.3 Bullet 2 — Nonlinear Cut-Fibre Rate
Deficit on Periodic Head-Motion Sweeps, `Problem 9.4` Bounded-Cone Regime).**
Under the landmark-conditioned periodic sweep hypotheses above, for `|Σ| ≥ 2`, broken outputs
`|E| ≤ δ d^2`, effective class count `M_sched * q_state ≤ η d / Delta`, and landmark advice
`K_land * log q_state ≤ α * d^2 * log |Σ|` with `δ + η < 1`, the nonlinear fibre `C` obeys
`log_{|Σ|} |C| / d^2 ≤ 1 + α - (1 - δ - η) * Delta^Delta / (Delta + 1)^(Delta + 1)`. -/
def PeriodicSweepNonlinearFibreDeficitSpec : Prop :=
  ∀ (d M_sched q_state Delta K_land : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (δ η α : ℝ)
    (S : PeriodicHeadSweepSystem d M_sched q_state Delta Sigma)
    (landmarks : Fin K_land → ZMod d)
    (landmarkOf : ZMod d → Fin K_land)
    (propState : Fin K_land → Fin q_state → ZMod d → Fin q_state)
    (E : Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    2 ≤ Fintype.card Sigma →
    1 ≤ M_sched →
    1 ≤ q_state →
    1 ≤ Delta →
    0 ≤ δ →
    0 ≤ η →
    0 ≤ α →
    δ + η < 1 →
    (E.card : ℝ) ≤ δ * (d : ℝ) ^ 2 →
    ((M_sched * q_state : ℕ) : ℝ) ≤ η * (d : ℝ) / (Delta : ℝ) →
    (K_land : ℝ) * Real.log (q_state : ℝ) ≤
      α * ((d : ℝ) ^ 2) * Real.log (Fintype.card Sigma : ℝ) →
    C.Nonempty →
    ValidatesNonlinearFibre S E C →
    (∀ X ∈ C, ∀ c : ZMod d,
      S.entryState X c = propState (landmarkOf c) (S.entryState X (landmarks (landmarkOf c))) c) →
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      1 + α - (1 - δ - η) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))

end BoundedArityDecoders
