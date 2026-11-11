import Transpose.Statement
import BoundedArityDecoders.BoundedAritySetCapacity

/-!
# Formal Specifications — Section I & Part III.B: Native Sweep-Cone Interface to `(T)` & `Problem 9.4`

Statement-only formal specifications connecting Theorem 1 (`BoundedAritySetCapacity.lean`) directly
to the `Transpose.TM` machine model (`Transpose/Statement.lean`), `TCP` cut-truncated causal cones
(Paper 14), adaptive simulator pullback (Paper 18), and periodic head-motion stretches
(`Problem 9.4`), as described in `README.md` (§I Diagnosis, §II.1, and §III.3 Bullet 2):

* `TapeCodingConjectureNegationSpec`: the main series target `¬ Transpose.LinearTimeTransposable`
  (`(T)`), together with the canonical entry-width agreement `Transpose.entryBits d = ⌈log₂ d⌉` for
  all `d ≥ 2` (`entryBits 1 = 1`).
* `stateToTMMatrix`, `encodeCanonicalState`, `IsFrozenTraceCutFibre`, `TMDepStep`,
  `IsCutFreeCausalPath`, and `cutInputBitCone` / `cutInputEntryCone`: concrete `Transpose.TM`
  execution trace and `Γ`-cut causal dependency DAG on `State d (CanonicalWordAlphabet d)` — with
  **zero** data-independent landmark state assumptions.
* `TMTraceCutConeDeterminationSpec`: on any `Γ`-cut frozen-trace fibre `C` of `M : Transpose.TM`
  with `Γ`-free causal path vertex bound `D` (`1 ≤ M.k`), every step's `Γ`-truncated causal cone
  reads at most `(M.k + 1)^D` input bit steps, and every output bit / entry is uniquely determined
  on `C` by the input cells in its `Γ`-truncated causal cone.
* `PeriodicSweepInducesBoundedAritySharedCodeSpec` & `PeriodicSweepNonlinearFibreDeficitSpec`:
  when, on a periodic head-motion stretch of a `Γ`-cut fibre `C ⊆ Σ^{d × d}` (`Problem 9.4`),
  unbroken columns outside `E` share `M_cls` local cut-cone templates (`p : ZMod d → Fin M_cls`)
  of cell cone arity `≤ Delta`, the nonlinear fibre `C` **itself** satisfies `IsBoundedAritySetCode`
  directly without linearization, forcing a strict positive rate deficit whenever `|E| ≤ δ d^2`
  and `M_cls ≤ η d / Delta` (`δ + η < 1`).
-/

namespace BoundedArityDecoders

open SharedDecoders

section MachineTraceDefs

/-- Convert a matrix `X : State d (CanonicalWordAlphabet d)` into `Transpose.Matrix`
(`Nat → Nat → Nat → Bool`). -/
def stateToTMMatrix {d : ℕ} [NeZero d] (X : State d (CanonicalWordAlphabet d)) :
    Transpose.Matrix :=
  fun i j t =>
    if ht : t < Transpose.entryBits d then
      X (i : ZMod d) (j : ZMod d) ⟨t, ht⟩
    else false

/-- Row-major bit-list encoding of `X : State d (CanonicalWordAlphabet d)` on `Transpose.TM`. -/
def encodeCanonicalState {d : ℕ} [NeZero d] (X : State d (CanonicalWordAlphabet d)) : List Bool :=
  Transpose.encode d (Transpose.entryBits d) (stateToTMMatrix X)

/-- Configuration of `M : Transpose.TM` after `t` steps from `Transpose.init M` on input `w`. -/
def tmCfgAt (M : Transpose.TM) (w : List Bool) (t : ℕ) : Option (Transpose.Config M) :=
  Transpose.stepN M w t (Transpose.init M)

/-- Work-tape head `h` writes cell `workPos u h` at step `u`, and step `v > u` is the next visit
of head `h` to that exact tape cell. -/
def IsLastWorkVisit {k : ℕ} (workPos : ℕ → Fin k → Int) (h : Fin k) (u v : ℕ) : Prop :=
  u < v ∧ workPos u h = workPos v h ∧ ∀ w : ℕ, u < w → w < v → workPos w h ≠ workPos v h

/-- Direct causal dependency edge `u → v` (`u < v < T`) along a frozen head schedule `workPos`:
either `v = u + 1` (control-state spine edge) or `u` is the most recent step visiting one of the
`k` work-tape cells under `workPos v`. -/
def TMDepStep {k : ℕ} (workPos : ℕ → Fin k → Int) (T u v : ℕ) : Prop :=
  v < T ∧ (v = u + 1 ∨ ∃ h : Fin k, IsLastWorkVisit workPos h u v)

/-- Descending causal path `π = [v_0, v_1, …, v_ℓ]` (`v_0 > v_1 > ⋯ > v_ℓ`) in `workPos` avoiding
the cut step set `Γ` at all strict predecessors `v_1, …, v_ℓ` (matching `BoundedStackDepth.genie`). -/
def IsCutFreeCausalPath {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ) (Γ : Finset ℕ) :
    List ℕ → Prop
  | [] => True
  | [v] => v < T
  | v :: u :: rest =>
      TMDepStep workPos T u v ∧ u ∉ Γ ∧ IsCutFreeCausalPath workPos T Γ (u :: rest)

/-- Step `u < T` lies in the `Γ`-truncated causal cone of step `v < T` along `workPos`. -/
def InCutCausalCone {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ) (Γ : Finset ℕ) (v u : ℕ) : Prop :=
  ∃ π : List ℕ, π.head? = some v ∧ π.getLast? = some u ∧ IsCutFreeCausalPath workPos T Γ π

/-- A subset `C ⊆ State d (CanonicalWordAlphabet d)` forms a **frozen-trace `Γ`-cut fibre** of
`M : Transpose.TM` at horizon `T` with common head trajectory `(inPos, workPos)` and output-bit
emission steps `emitStep : Fin (Transpose.inputLength d) → ℕ` if:
1. Every `X ∈ C` halts at step `T` with output `transpose (stateToTMMatrix X)` and follows the
   common head positions `(inPos t, workPos t)` and output-emission step schedule `emitStep`;
2. Every cut step `u ∈ Γ` (`u < T`) has identical post-step control state and written work-tape
   symbols across all `X ∈ C` (the nonlinear fibre obtained by conditioning on the `Γ` cut values). -/
def IsFrozenTraceCutFibre (M : Transpose.TM) (d T : ℕ) [NeZero d]
    (inPos : ℕ → Int)
    (workPos : ℕ → Fin M.k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ)
    (Γ : Finset ℕ)
    (C : Set (State d (CanonicalWordAlphabet d))) : Prop :=
  (∀ u ∈ Γ, u < T) ∧
  (∀ idx : Fin (Transpose.inputLength d), emitStep idx < T) ∧
  (∀ X ∈ C,
    ∃ cEnd : Transpose.Config M,
      tmCfgAt M (encodeCanonicalState X) T = some cEnd ∧
      Transpose.step M (encodeCanonicalState X) cEnd = none ∧
      cEnd.outRev.reverse =
        Transpose.encode d (Transpose.entryBits d) (Transpose.transpose (stateToTMMatrix X))) ∧
  (∀ X ∈ C, ∀ t ≤ T,
    ∃ cfg : Transpose.Config M,
      tmCfgAt M (encodeCanonicalState X) t = some cfg ∧
      cfg.inPos = inPos t ∧
      cfg.workPos = workPos t) ∧
  (∀ X ∈ C, ∀ idx : Fin (Transpose.inputLength d),
    ∃ cfgPre cfgPost : Transpose.Config M,
      tmCfgAt M (encodeCanonicalState X) (emitStep idx) = some cfgPre ∧
      tmCfgAt M (encodeCanonicalState X) (emitStep idx + 1) = some cfgPost ∧
      cfgPre.outRev.length = idx.val ∧
      cfgPost.outRev.length = idx.val + 1) ∧
  (∀ X₁ ∈ C, ∀ X₂ ∈ C, ∀ u ∈ Γ,
    ∀ cfg₁ cfg₂ : Transpose.Config M,
      tmCfgAt M (encodeCanonicalState X₁) (u + 1) = some cfg₁ →
      tmCfgAt M (encodeCanonicalState X₂) (u + 1) = some cfg₂ →
      cfg₁.state = cfg₂.state ∧
      ∀ h : Fin M.k, cfg₁.work h (workPos u h) = cfg₂.work h (workPos u h))

/-- A cell-level `Γ`-cut sweep cone system on `State d Sigma` (`Problem 9.4` & `README.md` L28,
L137): on a nonlinear cut fibre `C ⊆ State d Sigma` where the `Γ`-truncated causal DAG has cell
cone arity `≤ Delta`, unbroken columns `c` (those where `(r, c) ∉ E`) fall into `M_cls` periodic
cone-template classes `p : ZMod d → Fin M_cls` sharing both relative head-offset stencils
`stencil (p c) r` (`|stencil m r| ≤ Delta`) and local `D`-step `M.δ` + frozen-cut transition
composition `evalCone (p c)`. -/
structure PeriodicCutConeSweep (d M_cls Delta : ℕ) (Sigma : Type*) where
  p : ZMod d → Fin M_cls
  stencil : Fin M_cls → ZMod d → Finset (ZMod d × ZMod d)
  evalCone : Fin M_cls → State d Sigma → (ZMod d → Sigma)
  stencil_card_le : ∀ m r, (stencil m r).card ≤ Delta
  eval_local : ∀ m r (Y₁ Y₂ : State d Sigma),
    (∀ q ∈ stencil m r, Y₁ q.1 q.2 = Y₂ q.1 q.2) →
    evalCone m Y₁ r = evalCone m Y₂ r

end MachineTraceDefs

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Main Series Target `(T)` (`README.md` §I Line 3 & `Transpose/Statement.lean`).**
1. For all `d ≥ 2`, `Transpose.entryBits d = Nat.clog 2 d` (`⌈log₂ d⌉`, with `entryBits 1 = 1`).
2. Statement `(T)` asserts `¬ Transpose.LinearTimeTransposable`: no deterministic multitape Turing
   machine (`M.k` read/write work tapes + read-only input tape + one-way write-only output tape)
   transposes `d × d` matrices of `entryBits d`-bit words in `O(L)` steps (`L = d^2 * entryBits d`). -/
def TapeCodingConjectureNegationSpec : Prop :=
  (∀ d : ℕ, 2 ≤ d → Transpose.entryBits d = Nat.clog 2 d) ∧
  ¬ Transpose.LinearTimeTransposable

/-- **Claim (`README.md` §I.1 Line 6 & §II.1 Line 28 — Concrete `Transpose.TM` Cut-Cone
Fan-In `(k + 1)^D` and Nonlinear Fibre Determination).**
On any frozen-trace `Γ`-cut fibre `C ⊆ State d (CanonicalWordAlphabet d)` of `M : Transpose.TM`
(`1 ≤ M.k`) whose `Γ`-avoiding causal paths have at most `D ≥ 1` vertices:
1. Every step `v < T` has a `Γ`-truncated causal cone `cone(v)` of at most `(M.k + 1)^D` steps
   (hence reads at most `(M.k + 1)^D` input matrix cells);
2. For every output bit `idx : Fin (Transpose.inputLength d)` (say bit `ℓ` of transposed entry
   `(r, c)`), there is a fixed footprint `Q_idx ⊆ (ZMod d)^2` of at most `(M.k + 1)^D` matrix
   entries such that on the **nonlinear** fibre `C`, `X₁ c r ℓ = X₂ c r ℓ` holds whenever
   `X₁, X₂ ∈ C` agree on `Q_idx` (requiring **zero** data-independent control-state assumptions,
   because every causal path of length `D` is already terminated by frozen cut values in `Γ`). -/
def TMTraceCutConeDeterminationSpec : Prop :=
  ∀ (M : Transpose.TM) (d T D : ℕ) [NeZero d]
    (inPos : ℕ → Int)
    (workPos : ℕ → Fin M.k → Int)
    (emitStep : Fin (Transpose.inputLength d) → ℕ)
    (Γ : Finset ℕ)
    (C : Set (State d (CanonicalWordAlphabet d))),
    1 ≤ M.k →
    1 ≤ D →
    IsFrozenTraceCutFibre M d T inPos workPos emitStep Γ C →
    (∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D) →
    (∀ v < T, ∃ coneSteps : Finset ℕ,
      coneSteps.card ≤ (M.k + 1) ^ D ∧
      ∀ u < T, InCutCausalCone workPos T Γ v u → u ∈ coneSteps) ∧
    (∀ (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d)),
      ∃ Q_bit : Finset (ZMod d × ZMod d),
        Q_bit.card ≤ (M.k + 1) ^ D ∧
        ∀ X₁ ∈ C, ∀ X₂ ∈ C,
          (∀ ij ∈ Q_bit, X₁ ij.1 ij.2 = X₂ ij.1 ij.2) →
          X₁ c r ℓ = X₂ c r ℓ)

/-- **Claim (`README.md` §III.3 Bullet 2 — Periodic Cut-Cone Sweep Induces `IsBoundedAritySetCode`
Directly on Nonlinear Cut Fibres Without Linearization).**
Whenever a `PeriodicCutConeSweep d M_cls Delta Sigma` validates an arbitrary **nonlinear** cut
fibre `C ⊆ State d Sigma` outside broken/cut-incident output entries `E` (i.e., for all `X ∈ C`
and `(r, c) ∉ E`, `S.evalCone (S.p c) (rot c X) r = X c r`), `C` **directly** satisfies
`IsBoundedAritySetCode Delta S.p E S.evalCone S.stencil C` — with zero fibre linearization and
zero subfibre state-reset assumptions. -/
def PeriodicSweepInducesBoundedAritySharedCodeSpec : Prop :=
  ∀ (d M_cls Delta : ℕ) [NeZero d]
    (Sigma : Type*)
    (S : PeriodicCutConeSweep d M_cls Delta Sigma)
    (E : Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    (∀ X ∈ C, ∀ r c : ZMod d, (r, c) ∉ E →
      S.evalCone (S.p c) (rot c X) r = X c r) →
    IsBoundedAritySetCode Delta S.p E S.evalCone S.stencil C

/-- **Claim (`README.md` §I.1–2, §II.1 Bullet 2 & §III.3 Bullet 2 — Unconditional Nonlinear
Cut-Fibre Rate Deficit on Periodic Head-Motion Sweeps, `Problem 9.4`).**
For any finite alphabet `Σ` (`|Σ| ≥ 2`, including `CanonicalWordAlphabet d`), any nonempty
nonlinear cut fibre `C ⊆ State d Sigma` validated outside `E` (`|E| ≤ δ d^2`) by a
`PeriodicCutConeSweep d M_cls Delta Sigma` (`1 ≤ M_cls`, `1 ≤ Delta`) with
`M_cls ≤ η d / Delta` and `δ + η < 1`, Theorem 1 forces the strict nonlinear rate upper bound
`log_{|Σ|} |C| / d^2 ≤ 1 - (1 - δ - η) * Delta^Delta / (Delta + 1)^(Delta + 1)`. -/
def PeriodicSweepNonlinearFibreDeficitSpec : Prop :=
  ∀ (d M_cls Delta : ℕ) [NeZero d]
    (Sigma : Type*) [Fintype Sigma]
    (δ η : ℝ)
    (S : PeriodicCutConeSweep d M_cls Delta Sigma)
    (E : Finset (ZMod d × ZMod d))
    (C : Set (State d Sigma)),
    2 ≤ Fintype.card Sigma →
    1 ≤ M_cls →
    1 ≤ Delta →
    0 ≤ δ →
    0 ≤ η →
    δ + η < 1 →
    (E.card : ℝ) ≤ δ * (d : ℝ) ^ 2 →
    (M_cls : ℝ) ≤ η * (d : ℝ) / (Delta : ℝ) →
    C.Nonempty →
    (∀ X ∈ C, ∀ r c : ZMod d, (r, c) ∉ E →
      S.evalCone (S.p c) (rot c X) r = X c r) →
    Real.log (Nat.card C : ℝ) / (Real.log (Fintype.card Sigma : ℝ) * (d : ℝ) ^ 2) ≤
      1 - (1 - δ - η) * ((Delta : ℝ) ^ Delta / ((Delta + 1 : ℝ) ^ (Delta + 1)))

end BoundedArityDecoders
