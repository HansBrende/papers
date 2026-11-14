import Transpose.Statement
import BoundedArityDecoders.BoundedAritySetCapacity

/-!
# Frozen-Trace `Γ`-Cut Fibres and Syntactic Causal-Cone Support on `Transpose.TM`

Definitions and exact syntactic causal-cone support specification for `Transpose.TM`
(`Transpose/Statement.lean`) on `State d (CanonicalWordAlphabet d)`:

* `stateToTMMatrix`, `encodeCanonicalState`, `tmCfgAt`, `IsLastWorkVisit`, `TMDepStep`,
  `IsCutFreeCausalPath`, `InCutCausalCone`, and `IsFrozenTraceCutFibre`: concrete `Transpose.TM`
  execution trace and `Γ`-cut causal dependency DAG on `State d (CanonicalWordAlphabet d)`.
* `inputCellOfPos`, `outputBitIdx`, and `cutConeInputCells`: explicit syntactic input-cell support
  of the `Γ`-truncated causal cone of any step `v < T` (eliminating existential singleton-footprint
  loopholes).
* `TMTraceCutConeDeterminationSpec`: proved in `BoundedArityDecoders.NativeSweepInterfaceProofs`.
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

/-- Input matrix cell `(row, col) : ZMod d × ZMod d` under input head position `p : Int` (`none`
when `p` lies outside `[0, L(d))`). -/
def inputCellOfPos (d : ℕ) [NeZero d] (p : Int) : Option (ZMod d × ZMod d) :=
  if 0 ≤ p ∧ p.toNat < Transpose.inputLength d then
    let b := Transpose.entryBits d
    some (((p.toNat / (d * b) : ℕ) : ZMod d),
          (((p.toNat % (d * b)) / b : ℕ) : ZMod d))
  else none

/-- Output tape index of bit `ℓ` of transposed matrix entry `(r, c)`. -/
def outputBitIdx (d : ℕ) [NeZero d] (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d)) :
    Fin (Transpose.inputLength d) :=
  let b := Transpose.entryBits d
  ⟨r.val * (d * b) + c.val * b + ℓ.val, by
    have hr : r.val + 1 ≤ d := r.val_lt
    have hc : c.val + 1 ≤ d := c.val_lt
    have hcb : c.val * b + ℓ.val < d * b :=
      calc c.val * b + ℓ.val < c.val * b + b := Nat.add_lt_add_left ℓ.isLt _
        _ = (c.val + 1) * b := by ring
        _ ≤ d * b := Nat.mul_le_mul_right b hc
    unfold Transpose.inputLength
    calc r.val * (d * b) + c.val * b + ℓ.val < r.val * (d * b) + d * b := by omega
      _ = (r.val + 1) * (d * b) := by ring
      _ ≤ d * (d * b) := Nat.mul_le_mul_right (d * b) hr
      _ = d * d * b := (Nat.mul_assoc d d b).symm⟩

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
the cut step set `Γ` at all strict predecessors `v_1, …, v_ℓ`. -/
def IsCutFreeCausalPath {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ) (Γ : Finset ℕ) :
    List ℕ → Prop
  | [] => True
  | [v] => v < T
  | v :: u :: rest =>
      TMDepStep workPos T u v ∧ u ∉ Γ ∧ IsCutFreeCausalPath workPos T Γ (u :: rest)

/-- Step `u < T` lies in the `Γ`-truncated causal cone of step `v < T` along `workPos`. -/
def InCutCausalCone {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ) (Γ : Finset ℕ) (v u : ℕ) : Prop :=
  ∃ π : List ℕ, π.head? = some v ∧ π.getLast? = some u ∧ IsCutFreeCausalPath workPos T Γ π

/-- Exact set of steps `u < T` in the `Γ`-truncated causal cone of step `v`. -/
noncomputable def trueConeSteps {k : ℕ} (workPos : ℕ → Fin k → Int) (T : ℕ)
    (Γ : Finset ℕ) (v : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun u => InCutCausalCone workPos T Γ v u)
    (fun _ => Classical.propDecidable _) (Finset.range T)

/-- Exact syntactic input-cell support read by `inPos` across `trueConeSteps workPos T Γ v`:
`ij ∈ cutConeInputCells d T inPos workPos Γ v` holds iff some step `w < T` in the `Γ`-truncated
causal cone of `v` places the input head on matrix cell `ij`. -/
noncomputable def cutConeInputCells {k : ℕ} (d T : ℕ) [NeZero d] [DecidableEq (ZMod d)]
    (inPos : ℕ → Int) (workPos : ℕ → Fin k → Int) (Γ : Finset ℕ) (v : ℕ) :
    Finset (ZMod d × ZMod d) :=
  (trueConeSteps workPos T Γ v).biUnion fun w =>
    match inputCellOfPos d (inPos w) with
    | none => ∅
    | some ij => {ij}

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

end MachineTraceDefs

/-- **Syntactic `Γ`-Cut Cone Fan-In `(k + 1)^D` and Fibre Determination.**
On any frozen-trace `Γ`-cut fibre `C ⊆ State d (CanonicalWordAlphabet d)` of `M : Transpose.TM`
(`1 ≤ M.k`) whose `Γ`-avoiding causal paths have at most `D ≥ 1` vertices:
1. Every step `v < T` has `(trueConeSteps workPos T Γ v).card ≤ (M.k + 1)^D`;
2. For every output bit `(r, c, ℓ)`, the explicit syntactic cone footprint
   `Q_bit = cutConeInputCells d T inPos workPos Γ (emitStep (outputBitIdx d r c ℓ))` contains `ij`
   if and only if some step `w < T` in `InCutCausalCone` places `inPos w` inside cell `ij`, has
   cardinality `Q_bit.card ≤ (M.k + 1)^D`, and uniquely determines `X c r ℓ` across `C`. -/
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
    (∀ v < T,
      (trueConeSteps workPos T Γ v).card ≤ (M.k + 1) ^ D ∧
      ∀ u : ℕ, u ∈ trueConeSteps workPos T Γ v ↔ (u < T ∧ InCutCausalCone workPos T Γ v u)) ∧
    (∀ (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d)),
      let v := emitStep (outputBitIdx d r c ℓ)
      let Q_bit := cutConeInputCells d T inPos workPos Γ v
      Q_bit.card ≤ (M.k + 1) ^ D ∧
      (∀ ij : ZMod d × ZMod d,
        ij ∈ Q_bit ↔ ∃ w < T, InCutCausalCone workPos T Γ v w ∧ inputCellOfPos d (inPos w) = some ij) ∧
      (∀ X₁ ∈ C, ∀ X₂ ∈ C,
        (∀ ij ∈ Q_bit, X₁ ij.1 ij.2 = X₂ ij.1 ij.2) →
        X₁ c r ℓ = X₂ c r ℓ))

end BoundedArityDecoders
