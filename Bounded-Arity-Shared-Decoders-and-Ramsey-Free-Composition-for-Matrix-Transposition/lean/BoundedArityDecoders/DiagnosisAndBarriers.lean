import Transpose.Statement
import SharedDecoders.CapacityUniversal
import SharedDecoders.CapacityDifferenceCover
import SharedDecoders.CapacityMaskMethodEndpoints
import SharedDecoders.CapacityMaskStructured
import SharedDecoders.CompositionLinear
import SharedDecoders.CompositionRankField
import BoundedArityDecoders.NativeSweepInterface
import BoundedArityDecoders.OperatorDuality

/-!
# Formal Specifications — Section I Diagnosis, Prior Spine Benchmarks & Machine-Level Controls

Statement-only formal specifications covering all remaining mathematical claims in `README.md`
Section I (Diagnosis: Walls 1–3 and Machine/Shared-Decoder Spines) and Section II motivational
and machine-complexity controls (`[F5]`):

1. `Diagnosis_TCPAndAdaptiveConeReductionSpec` (`README.md` §I.1 Line 6):
   `TCP` depth reduction on frozen `k`-head traces (Paper 14 `BoundedStackDepth.genie`) and
   adaptive simulator cut-cone pullback (Papers 15 & 18) yielding bounded cell fan-in
   `Δ ≤ (k + 1)^{D(k, ε)}`.
2. `Diagnosis_AbstractSeparatedHighRateCodeSpec` (`README.md` §I.1 Line 7a):
   abstract bounded-degree paired-distance-separated binary storage codes achieving rate
   `1 - C Δ^{-α} → 1` (`0 < α < 1/2`, Paper 13 + Paper 15).
3. `Diagnosis_ShiftAndRotationCodingGainBarrierSpec` (`README.md` §I.1 Line 7b):
   shift-circuit / programmable-rotation coding-gain barrier `Ω(n log n / (s + n))` on bounded-degree
   causal networks without shared finite-state sweep rules (Paper 1 `Propositions 11.2–11.3`).
4. `Diagnosis_LinearSharedDecoderBoundsAndMaskFloorsSpec` (`README.md` §I.2 Line 10 & §II.3.1 Line 99):
   Paper 19's `41/64` two-class bound (`Theorem C`), `1 - 1 / (4 ⌈√(2 M)⌉)` `M`-class bound
   (`Theorem M`), and the `9/16` and `5/8` positive-term Grassmann/mask certificate floors.
5. `Diagnosis_RamseyHalesJewettTwoStageSpec` (`README.md` §I.2 Line 13 & §II.2 Line 53):
   Paper 19's van der Waerden / Hales–Jewett two-stage progression cutoff and `r / (b d) ≥ W_{M₁}⁻¹(d) / 4`
   rank lower bound.
6. `Diagnosis_BehrendAndRandomAPBoundSpec` (`README.md` §II.2 Line 55):
   Behrend's `d exp(-C √(log d))` `3`-AP-free subsets and the `O(log d)` longest ordinary arithmetic
   progression in random `M₁`-colorings (`M₁ ≥ 2`).
7. `Diagnosis_StoneShuffleAndRowShearMachineComplexitySpec` (`README.md` §I.2 Line 14, §II.3.2
   Lines 102 & 108):
   `O(L)` `Transpose.TM` computation of one Stone shuffle/unshuffle pass and `2`-work-tape
   within-row shear `K_shear`, paired with the exact simultaneous dyadic commutator rank
   `finrank F (range [S, I_row ⊗ G_j]) = b * (2^m)^2 / 2` across all `m = log₂ d` dyadic address
   scales over every field `F`.
-/

namespace BoundedArityDecoders

open SharedDecoders Module
open scoped BigOperators

section BarrierDefs

/-- An abstract directed recovery relation `N : V → Finset V` on a finite coordinate set `V` has:
* maximum incidence degree at most `Delta` (each `v` reads `|N v| ≤ Delta` coordinates and is read
  by at most `Delta` coordinates), and
* paired-distance separation `≥ G` (no sequence of `≤ G` undirected incidence steps connects the
  left port `(false, v)` of a coordinate `v` to its right port `(true, v)`). -/
def IsBoundedDegreeSeparatedRelation {V : Type*} [Fintype V] [DecidableEq V]
    (Delta G : ℕ) (N : V → Finset V) : Prop :=
  (∀ v : V, (N v).card ≤ Delta) ∧
  (∀ u : V, (Finset.univ.filter (fun v => u ∈ N v)).card ≤ Delta) ∧
  ∀ (v : V) (walk : List (Bool × V)),
    walk.head? = some (false, v) →
    walk.getLast? = some (true, v) →
    (∀ i : ℕ, ∀ h : i + 1 < walk.length,
      let p := walk.get ⟨i, Nat.lt_of_succ_lt h⟩
      let q := walk.get ⟨i + 1, h⟩
      (p.1 = false ∧ q.1 = true ∧ p.2 ∈ N q.2) ∨
      (p.1 = true ∧ q.1 = false ∧ q.2 ∈ N p.2)) →
    G < walk.length

/-- Binary storage code `C ⊆ (V → Bool)` for recovery relation `N`: each coordinate `v` is
uniquely determined on `C` by the coordinates in `N v` (`v ∉ N v` is automatic when `G ≥ 1`). -/
def IsBinaryStorageCodeFor {V : Type*} (N : V → Finset V) (C : Set (V → Bool)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ v : V, (∀ u ∈ N v, x u = y u) → x v = y v

/-- An odd-girth above-half-rate linear storage-code seed over a finite field `K` (matching
`TapeStorageRates.OddGirthLinearSeed` in Paper 15, supplied on paper by Paper 13 `Corollary U(a)` /
`Theorem G` via Goren–Oort Ramanujan Tanner codes on non-abelian `PGL₂` quotients, whose
Hilbert-modular-surface Riemann–Roch input is external to Mathlib):
a growing sequence of simple undirected graphs `(Fin (size j), adj j)` of maximum degree `≤ D_seed`
whose closed walks of odd edge-length eventually exceed every threshold `G₀`, carrying `K`-linear
storage codes `code j` of rate `dim(code j) / size j ≥ ρ`. -/
def HasOddGirthLinearSeed (K : Type*) [Field K] [Fintype K] (D_seed : ℕ) (ρ : ℝ) : Prop :=
  ∃ (size : ℕ → ℕ)
    (adj : ∀ j : ℕ, Fin (size j) → Fin (size j) → Prop)
    (_ : ∀ j : ℕ, DecidableRel (adj j))
    (code : ∀ j : ℕ, Submodule K (Fin (size j) → K)),
    (∀ N₀ : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀, N₀ ≤ size j) ∧
    (∀ (j : ℕ) (u v : Fin (size j)), adj j u v ↔ adj j v u) ∧
    (∀ (j : ℕ) (u : Fin (size j)), ¬ adj j u u) ∧
    (∀ (j : ℕ) (u : Fin (size j)),
      (Finset.univ.filter (fun v => adj j u v)).card ≤ D_seed) ∧
    (∀ G₀ : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (v : Fin (size j)) (w : List (Fin (size j))),
      w.head? = some v →
      w.getLast? = some v →
      (∀ i : ℕ, ∀ h : i + 1 < w.length,
        adj j (w.get ⟨i, Nat.lt_of_succ_lt h⟩) (w.get ⟨i + 1, h⟩)) →
      Odd (w.length - 1) →
      G₀ < w.length - 1) ∧
    (∀ (j : ℕ) (x : Fin (size j) → K), x ∈ code j → ∀ u : Fin (size j),
      (∀ v : Fin (size j), adj j u v → x v = 0) → x u = 0) ∧
    (∀ j : ℕ, ρ * (size j : ℝ) ≤ (finrank K (code j) : ℝ))

/-- A size-`s` fan-in-2 acyclic Boolean circuit computing programmable cyclic shift / rotation
`(x, sh) ↦ (j ↦ x ((j + sh) mod n))` on `n` data bits (`0 .. n - 1`) and `n` binary shift-control
bits (`n .. 2 n - 1`, encoding `sh : Fin n` in binary). -/
def HasBarrelShiftCircuit (n s : ℕ) [NeZero n] : Prop :=
  let W := 2 * n + s
  let hW : 0 < W := Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos 1) (NeZero.pos n)) s
  let wIdx (k : ℕ) : Fin W := ⟨k % W, Nat.mod_lt _ hW⟩
  ∃ (in1 in2 : Fin s → Fin W)
    (gateOp : Fin s → Bool → Bool → Bool)
    (outWire : Fin n → Fin W),
    (∀ g : Fin s, (in1 g).val < 2 * n + g.val ∧ (in2 g).val < 2 * n + g.val) ∧
    ∀ (x : Fin n → Bool) (sh : Fin n),
      ∃ wireVal : Fin W → Bool,
        (∀ i : Fin n, wireVal (wIdx i.val) = x i) ∧
        (∀ b : Fin n, wireVal (wIdx (n + b.val)) = (((sh.val / (2 ^ b.val)) % 2) == 1)) ∧
        (∀ g : Fin s,
          wireVal (wIdx (2 * n + g.val)) =
            gateOp g (wireVal (in1 g)) (wireVal (in2 g))) ∧
        (∀ j : Fin n,
          wireVal (outWire j) = x ⟨(j.val + sh.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩)

/-- An `n`-round causal network code on a simple undirected graph `(Fin V, adj)` with sources
`src` and sinks `sink` realizing the complete bipartite demand `msg : Fin n → Fin n → Bool`
(Paper 1, `Section 11.2` / `Proposition 11.2`):
fixing an acyclic orientation `topo : Fin V → ℕ` (`v ∈ adj u ∧ topo u < topo v`), in each round
`r : Fin n` every oriented edge `(u, v)` sends 1 bit `edgeBit r u v` computed by `edgeFn r u v`
solely from oriented edges `(w, u)` entering `u` (`w ∈ adj u ∧ topo w < topo u`) and (when
`src i = u`) source `i`'s message vector `msg i`; and for every pair `(i, j)` there is a round
`roundOf i j : Fin n` in which `sinkFn j (roundOf i j)` recovers `msg i j` solely from oriented
edges entering `sink j`. -/
def HasCausalCompleteExchangeCode {V n : ℕ}
    (adj : Fin V → Finset (Fin V)) (src sink : Fin n → Fin V) : Prop :=
  Function.Injective src ∧
  Function.Injective sink ∧
  (∀ i j : Fin n, src i ≠ sink j) ∧
  ∃ (topo : Fin V → ℕ)
    (edgeFn : Fin n → Fin V → Fin V → (Fin V → Bool) → (Fin n → Bool) → Bool)
    (roundOf : Fin n → Fin n → Fin n)
    (sinkFn : Fin n → Fin n → (Fin V → Bool) → Bool),
    ∀ msg : Fin n → Fin n → Bool,
      ∃ edgeBit : Fin n → Fin V → Fin V → Bool,
        (∀ (r : Fin n) (u v : Fin V),
          v ∈ adj u → topo u < topo v →
          edgeBit r u v =
            edgeFn r u v
              (fun w => if w ∈ adj u ∧ topo w < topo u then edgeBit r w u else false)
              (fun j => (List.finRange n).any
                (fun i => decide (src i = u) && msg i j))) ∧
        (∀ i j : Fin n,
          let r := roundOf i j
          sinkFn j r
            (fun w => if w ∈ adj (sink j) ∧ topo w < topo (sink j) then
              edgeBit r w (sink j) else false) = msg i j)

/-- Dyadic column-bit flip involution `I_row ⊗ G_j` on `GridState F (2^m) b` (`j : Fin m`):
flips bit `j` (`2^j`-place) of the column index `c` on every row and lane. -/
def colBitFlipGridLinear (F : Type*) [Semiring F] {m : ℕ} (b : ℕ) (j : Fin m) :
    GridState F (2 ^ m) b →ₗ[F] GridState F (2 ^ m) b :=
  let d := 2 ^ m
  let hd := Nat.two_pow_pos m
  LinearMap.pi fun r => LinearMap.pi fun c => LinearMap.pi fun ℓ =>
    let cFlip : Fin d := ⟨(Nat.xor c.val (2 ^ j.val)) % d, Nat.mod_lt _ hd⟩
    (LinearMap.proj (R := F) (φ := fun _ : Fin b => F) ℓ).comp
      ((LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin b → F) cFlip).comp
        (LinearMap.proj (R := F) (φ := fun _ : Fin d => Fin d → Fin b → F) r))

/-- Convert `A : Transpose.Matrix` (`d = 2^m`) to its `1`-bit left-shuffled `Transpose.Matrix`
(matching `stoneShuffleGridLinear` at `d = 2^m, b = entryBits d`). -/
def stoneShuffleTMMatrix (m : ℕ) (A : Transpose.Matrix) : Transpose.Matrix :=
  match m with
  | 0 => A
  | m' + 1 =>
      let d := 2 ^ (m' + 1)
      fun r' c' t =>
        let srcR := ((c' % 2) * (2 ^ m') + r' / 2) % d
        let srcC := ((r' % 2) * (2 ^ m') + c' / 2) % d
        A srcR srcC t

/-- Within-row shear `(rowShearTMMatrix d A) r c t = A r ((c + r) % d) t` on `Transpose.Matrix`. -/
def rowShearTMMatrix (d : ℕ) (A : Transpose.Matrix) : Transpose.Matrix :=
  fun r c t => A r ((c + r) % d) t

end BarrierDefs

/-! ### Formal Claim Specifications (No Proofs Yet) -/

/-- **Diagnosis 1 (`README.md` §I.1 Line 6 — `TCP` Frozen-Trace Cut & Adaptive Cone Pullback).**
1. (*Paper 14 `BoundedStackDepth.genie`*) For every `k ≥ 1` and `ε > 0`, there exists a constant
   depth `D ≥ 1` such that every `T`-step `k`-head unit-speed walk `workPos` admits a cut step set
   `Γ ⊆ {0, …, T - 1}` with `|Γ| ≤ ε T` reducing all `Γ`-free causal paths to `≤ D` vertices and
   all `Γ`-truncated causal cones to `≤ (k + 1)^D` steps.
2. (*Papers 14, 15 & 18 aligned-simulator cut-cone pullback*) For every `c₀ L`-step transposer
   `M : Transpose.TM` (`1 ≤ M.k`) and `0 < ε < 1`, there exist a constant depth `D ≥ 1` and `D₀`
   such that for every `d ≥ D₀`, there exist a nonlinear fibre `C ⊆ State d (CanonicalWordAlphabet d)`
   of size `|C| ≥ 2^((1 - ε) L)` (`L = inputLength d`) and a set `E_bits` of at most `ε L` broken
   output bits outside which every output bit `(r, c, ℓ)` (in the bit-step `Transpose.TM` model,
   where each step emits at most one bit) is determined on `C` by a fixed cone `Q_bit` of at most
   `(M.k + 1)^D` input matrix cells. -/
def Diagnosis_TCPAndAdaptiveConeReductionSpec : Prop :=
  (∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε →
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ (T : ℕ) (workPos : ℕ → Fin k → Int),
        (∀ (t : ℕ) (h : Fin k), |workPos (t + 1) h - workPos t h| ≤ 1) →
        ∃ Γ : Finset ℕ,
          (∀ u ∈ Γ, u < T) ∧
          (Γ.card : ℝ) ≤ ε * (T : ℝ) ∧
          (∀ π : List ℕ, IsCutFreeCausalPath workPos T Γ π → π.length ≤ D) ∧
          (∀ v < T, ∃ coneSteps : Finset ℕ,
            coneSteps.card ≤ (k + 1) ^ D ∧
            ∀ u < T, InCutCausalCone workPos T Γ v u → u ∈ coneSteps)) ∧
  (∀ (M : Transpose.TM) (c₀ : ℕ) (ε : ℝ),
    1 ≤ M.k → 0 < ε → ε < 1 →
    Transpose.TransposesWithin M (fun L => c₀ * L) →
    ∃ (D D₀ : ℕ), 1 ≤ D ∧
      ∀ (d : ℕ) [NeZero d], max D₀ 2 ≤ d →
        ∃ (C : Set (State d (CanonicalWordAlphabet d)))
          (E_bits : Finset (ZMod d × ZMod d × Fin (Transpose.entryBits d))),
          (2 : ℝ) ^ ((1 - ε) * (Transpose.inputLength d : ℝ)) ≤ (Nat.card C : ℝ) ∧
          (E_bits.card : ℝ) ≤ ε * (Transpose.inputLength d : ℝ) ∧
          ∀ (r c : ZMod d) (ℓ : Fin (Transpose.entryBits d)),
            (r, c, ℓ) ∉ E_bits →
            ∃ Q_bit : Finset (ZMod d × ZMod d),
              Q_bit.card ≤ (M.k + 1) ^ D ∧
              ∀ X₁ ∈ C, ∀ X₂ ∈ C,
                (∀ ij ∈ Q_bit, X₁ ij.1 ij.2 = X₂ ij.1 ij.2) →
                X₁ c r ℓ = X₂ c r ℓ)

/-- **Diagnosis 2 (`README.md` §I.1 Line 7a — High-Rate Binary Codes on Separated Bounded-Degree
Relations, Paper 13 + Paper 15).**
1. (*Paper 13 `Numbers.lean` Goren–Oort Ramanujan Tanner numerical threshold at `p = 127, k = 91`*)
   At inert prime `p = 127` and weight `k = 91` (`δ = 127^2 + 1 = 16130`), the lift-degeneracy
   budget `⌈(2 - √3) * 16130 + 317⌉₊ = 4640 ≤ 4663 = 127^2 - 91 * 126` holds simultaneously with
   above-half field rate `(91 - 1)^2 / (127^2 + 1) = 8100 / 16130 > 1/2` and `14`-bit binary
   blow-up rate `(8100 / 16130) * log₂(127^2) / 14 > 5013 / 10000 > 1/2`.
2. (*Paper 15 `TapeStorageRates` odd-majority tensor amplification from Paper 13's odd-girth seed*)
   Given any odd-characteristic finite-field linear storage seed `HasOddGirthLinearSeed K D_seed ρ`
   with `1/2 < ρ < 1` (supplied on paper by Paper 13 `Corollary U(a)` / `Theorem G`), there exist
   constants `C_code > 0`, `0 < α < 1/2`, and `Δ₀` such that for every degree cap `Delta ≥ Δ₀` and
   every paired-distance girth threshold `G`, there exists a finite nonempty coordinate set `Fin n`,
   a relation `N : Fin n → Finset (Fin n)` satisfying `IsBoundedDegreeSeparatedRelation Delta G N`,
   and a nonempty binary storage code `C ⊆ (Fin n → Bool)` for `N` of rate
   `log₂ |C| / n ≥ 1 - C_code * Delta ^ (-α)`. -/
def Diagnosis_AbstractSeparatedHighRateCodeSpec : Prop :=
  (Nat.Prime 127 ∧
    ⌈(2 - Real.sqrt 3) * 16130 + 317⌉₊ = 4640 ∧
    4640 ≤ 127 ^ 2 - 91 * 126 ∧
    (1 : ℝ) / 2 < (8100 : ℝ) / 16130 ∧
    (5013 : ℝ) / 10000 < ((8100 : ℝ) / 16130) * (Real.log (127 ^ 2 : ℝ) / Real.log 2) / 14) ∧
  (∀ (K : Type) [Field K] [Fintype K] (D_seed : ℕ) (ρ : ℝ),
    (2 : K) ≠ 0 → 1 / 2 < ρ → ρ < 1 →
    HasOddGirthLinearSeed K D_seed ρ →
    ∃ (C_code α : ℝ) (Δ₀ : ℕ),
      0 < C_code ∧ 0 < α ∧ α < (1 : ℝ) / 2 ∧
      ∀ (Delta G : ℕ), Δ₀ ≤ Delta →
        ∃ (n : ℕ) (_ : NeZero n)
          (N : Fin n → Finset (Fin n))
          (C : Set (Fin n → Bool)),
          C.Nonempty ∧
          IsBoundedDegreeSeparatedRelation Delta G N ∧
          IsBinaryStorageCodeFor N C ∧
          (1 - C_code * ((Delta : ℝ) ^ (-α))) * (n : ℝ) ≤
            Real.log (Nat.card C : ℝ) / Real.log 2)

/-- **Diagnosis 3 (`README.md` §I.1 Line 7b — Shift-Circuit / Rotation Coding-Gain Barrier on
Bounded-Degree Networks Without Shared Finite-State Sweep Rules, Paper 1 `Propositions 11.2–11.3`).**
1. (*Coding gain `Ω(n log n / (s + n))` from size-`s` shift/rotation circuits*) Whenever cyclic
   shift / rotation on `n` bits (`n ≥ N₀`) is computable by a size-`s` fan-in-2 Boolean circuit
   (`HasBarrelShiftCircuit n s`, where distinct vertices apply distinct local gate functions rather
   than a shared finite-state sweep rule), it embeds into a max-degree-`4` graph on
   `V ≤ C_net * (s + n)` vertices (`m_edges = (∑_u deg u) / 2 ≤ 2 V`) with `n` sources `src` and
   `n` injective sinks `sink` realizing `n`-round complete-exchange shift coding at rate `1 / n`
   per round, whereas a pairwise walk-step lower bound `distBound` satisfies
   `∑_{i, j} distBound i j ≥ c_dist * n^2 * log₂ n` — forcing every positive multicommodity
   routing rate `λ_route > 0` obeying weak duality `λ_route * ∑ distBound ≤ m_edges` to have
   coding-to-routing gain `(1 / n) / λ_route ≥ c_gain * n * log₂ n / (s + n)`.
2. (*Explicit `s = O(n log n)` barrel shifter*) For every `n ≥ 2`, `HasBarrelShiftCircuit n s` holds
   for some `s ≤ C_sh * n * log₂ n`. -/
def Diagnosis_ShiftAndRotationCodingGainBarrierSpec : Prop :=
  (∃ (c_dist c_gain : ℝ) (C_net N₀ : ℕ),
    0 < c_dist ∧ 0 < c_gain ∧ 1 ≤ C_net ∧ 2 ≤ N₀ ∧
    ∀ (n s : ℕ) [NeZero n],
      N₀ ≤ n →
      HasBarrelShiftCircuit n s →
      ∃ (V : ℕ) (adj : Fin V → Finset (Fin V))
        (src sink : Fin n → Fin V)
        (distBound : Fin n → Fin n → ℕ),
        1 ≤ V ∧ V ≤ C_net * (s + n) ∧
        (∀ u : Fin V, u ∉ adj u) ∧
        (∀ u v : Fin V, v ∈ adj u ↔ u ∈ adj v) ∧
        (∀ u : Fin V, (adj u).card ≤ 4) ∧
        HasCausalCompleteExchangeCode adj src sink ∧
        (∀ (i j : Fin n) (walk : List (Fin V)),
          walk.head? = some (src i) →
          walk.getLast? = some (sink j) →
          (∀ t : ℕ, ∀ h : t + 1 < walk.length,
            walk.get ⟨t + 1, h⟩ ∈ adj (walk.get ⟨t, Nat.lt_of_succ_lt h⟩)) →
          distBound i j + 1 ≤ walk.length) ∧
        c_dist * ((n : ℝ) ^ 2) * (Real.log (n : ℝ) / Real.log 2) ≤
          (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) ∧
        (∀ rateRoute : ℝ, 0 < rateRoute →
          rateRoute * (∑ i : Fin n, ∑ j : Fin n, (distBound i j : ℝ)) ≤
            ((∑ u : Fin V, (adj u).card : ℕ) : ℝ) / 2 →
          c_gain * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) / ((s : ℝ) + (n : ℝ)) ≤
            (1 / (n : ℝ)) / rateRoute)) ∧
  (∃ C_sh : ℝ, 0 < C_sh ∧
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∃ s : ℕ, (s : ℝ) ≤ C_sh * (n : ℝ) * (Real.log (n : ℝ) / Real.log 2) ∧
        HasBarrelShiftCircuit n s)

/-- **Diagnosis 4 (`README.md` §I.2 Line 10 & §II.3.1 Line 99 — Paper 19 Linear-Source Shared
Capacity Bounds `Theorem C`, `Theorem M`, and `9/16` & `5/8` Certificate Floors).**
Over any field `F` and finite-dimensional entry space `A` (`b = finrank F A`):
1. (*`Theorem C`, `CapacityUniversal.lean`*) Every 2-class linear shared code `C` satisfies
   `finrank F C ≤ (41 / 64) b d^2 + (5 / 3) b d √d`.
2. (*`Theorem M`, `CapacityDifferenceCover.lean`*) Every `M`-class linear shared code `C` with
   `2 M ≤ d` and `2 M ≤ t^2` (`t ≥ 1`, e.g. `t = ⌈√(2 M)⌉`) satisfies
   `4 t * finrank F C + b d^2 ≤ 4 t * b d^2` (`rate ≤ 1 - 1 / (4 t)`).
3. (*`appendix-mask-methods.tex`*) On random binary masks (`η ≥ 0`), full-ambient isolation
   certificates are bounded below by `(9/16 - η/4 + 1/(2 d)) b d^2` outside probability
   `(d - 1) exp(-2 η^2 d / 9)`, and nested component certificates are bounded below by
   `(5/8 - η/4) b d^2` outside probability `(d - 1) exp(-η^2 d / 2)`. -/
def Diagnosis_LinearSharedDecoderBoundsAndMaskFloorsSpec : Prop :=
  (∀ (F A : Type*) [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (d : ℕ) [NeZero d] (p : ZMod d → Bool) (C : Submodule F (State d A)),
    IsSharedCode F p C →
    (finrank F C : ℝ) ≤
      41 / 64 * (finrank F A : ℝ) * (d : ℝ) ^ 2 +
        5 / 3 * (finrank F A : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ)) ∧
  (∀ (F A : Type*) [Field F] [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (d M t : ℕ) [NeZero d] (p : ZMod d → Fin M) (C : Submodule F (State d A)),
    IsSharedCode F p C →
    0 < t → 2 * M ≤ d → 2 * M ≤ t * t →
    4 * t * finrank F C + d * d * finrank F A ≤ 4 * t * (d * d * finrank F A)) ∧
  (∀ (d : ℕ) [NeZero d] (η : ℝ), 0 ≤ η →
    CapacityMaskProbability.prob (fun p : ZMod d → Bool =>
      ¬ ∀ (b : ℕ), 0 < b → ∀ (R : Finset (ZMod d)), R.card = 2 →
        ∀ (t : ℕ → ZMod d) (k : ℕ),
          9 / 16 - η / 4 + 1 / (2 * (d : ℝ)) ≤
            CapacityMaskProbability.isolationCertificate p b R t k / ((b : ℝ) * (d : ℝ) ^ 2)) ≤
      ((d : ℝ) - 1) * Real.exp (-2 * η ^ 2 * (d : ℝ) / 9)) ∧
  (∀ (d : ℕ) [NeZero d] (η : ℝ), 0 ≤ η →
    CapacityMaskProbability.prob (fun p : ZMod d → Bool =>
      ¬ ∀ (b : ℕ) (t : ℕ → ZMod d) (k : ℕ),
        (5 / 8 - η / 4) * (b : ℝ) * (d : ℝ) ^ 2 ≤
          CapacityMask.certificate (fun j =>
            (b : ℝ) * (d : ℝ) *
              (componentCount p (translateSets t j) : ℝ)) k) ≤
      ((d : ℝ) - 1) * Real.exp (-η ^ 2 * (d : ℝ) / 2))

/-- **Diagnosis 5 (`README.md` §I.2 Line 13 & §II.2 Line 53 — Paper 19 Hales–Jewett / van der
Waerden Two-Stage Progression Cutoff & Rank Threshold).**
1. (*Paper 19 `Theorem 6.3`, `CompositionLinear.exists_twoHop_cutoff`*) For every `M₁, M₂ ≥ 1`,
   there exists a Hales–Jewett / van der Waerden cutoff `N > 0` above which no two linear
   class-uniform stages `K₁, K₂` over **any** field `F` (`b ≥ 1`) satisfy `K₂ ∘ K₁ = swapLinear F`.
2. (*Paper 19 `Theorem 6.6`, `CompositionRankField.exists_twoHop_rank_threshold`*) Given any
   van der Waerden threshold `N` forcing a monochromatic `((2 M₂ + 1) k - 1)`-term progression in
   `[0, N)`, any two linear class-uniform maps `K₁, K₂` over a field `F` with `(d : F) ≠ 0` satisfy
   `b k (d - N + 1) ≤ 2 * rank(τ - K₂ K₁)` (yielding `r / (b d) ≥ k / 4` once `d ≥ 2 N`, i.e., `k`
   at the inverse van der Waerden scale `W_{M₁}⁻¹(d)`). -/
def Diagnosis_RamseyHalesJewettTwoStageSpec : Prop :=
  (∀ (M₁ M₂ : ℕ), 1 ≤ M₁ → 1 ≤ M₂ →
    ∃ N : ℕ, 0 < N ∧
      ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d]
        (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
        1 ≤ b →
        N ≤ d →
        ClassUniform p₁ K₁ →
        ClassUniform p₂ K₂ →
        K₂.comp K₁ ≠ swapLinear F (d := d) (A := Fin b → F)) ∧
  (∀ (M₁ M₂ k : ℕ), 1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ k →
    ∃ N : ℕ, 0 < N ∧
      ∀ (F : Type*) [Field F] (d b : ℕ) [NeZero d]
        (p₁ : ZMod d → Fin M₁) (p₂ : ZMod d → Fin M₂)
        (K₁ K₂ : State d (Fin b → F) →ₗ[F] State d (Fin b → F)),
        (d : F) ≠ 0 →
        2 * N ≤ d →
        ClassUniform p₁ K₁ →
        ClassUniform p₂ K₂ →
        b * k * (d - N + 1) ≤
          2 * finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)) ∧
        b * k * d ≤
          4 * finrank F (LinearMap.range (swapLinear F (d := d) (A := Fin b → F) - K₂.comp K₁)))

/-- **Diagnosis 6 (`README.md` §II.2 Line 55 — Behrend `3`-AP-Free Density & `O(log d)` Random
Progression Limit).**
1. (*Behrend*) There exists `C_beh > 0` such that for every `d ≥ 2`, `{0, …, d - 1}` contains an
   ordinary `3`-AP-free subset `S` of size `|S| ≥ d * exp(-C_beh * √(log d))`.
2. (*Random `M₁`-colorings, `M₁ ≥ 2`*) For every `M₁ ≥ 2`, there exist `C_ap > 0` and `D₀ ≥ 1` such
   that for every `d ≥ D₀`, more than half of all `M₁`-colorings `p₁ : Fin d → Fin M₁` have every
   monochromatic ordinary progression `a, a + s, …, a + (ℓ - 1) s < d` (`1 ≤ s`) bounded in length
   by `ℓ ≤ C_ap * log d`. -/
def Diagnosis_BehrendAndRandomAPBoundSpec : Prop :=
  (∃ C_beh : ℝ, 0 < C_beh ∧
    ∀ d : ℕ, 2 ≤ d →
      ∃ S : Finset ℕ,
        (∀ x ∈ S, x < d) ∧
        (∀ a s : ℕ, 1 ≤ s → ¬ (a ∈ S ∧ a + s ∈ S ∧ a + 2 * s ∈ S)) ∧
        (d : ℝ) * Real.exp (-C_beh * Real.sqrt (Real.log (d : ℝ))) ≤ (S.card : ℝ)) ∧
  (∀ M₁ : ℕ, 2 ≤ M₁ →
    ∃ (C_ap : ℝ) (D₀ : ℕ), 0 < C_ap ∧ 1 ≤ D₀ ∧
      ∀ (d : ℕ) [NeZero d], D₀ ≤ d →
        let hd : 0 < d := NeZero.pos d
        Fintype.card (Fin d → Fin M₁) <
          2 * Nat.card { p₁ : Fin d → Fin M₁ |
            ∀ (a s ℓ : ℕ), 1 ≤ s → 1 ≤ ℓ → a + (ℓ - 1) * s < d →
              (∀ j < ℓ,
                p₁ ⟨(a + j * s) % d, Nat.mod_lt _ hd⟩ = p₁ ⟨a % d, Nat.mod_lt _ hd⟩) →
              (ℓ : ℝ) ≤ C_ap * Real.log (d : ℝ) })

/-- **Diagnosis 7 (`README.md` §I.2 Line 14 & §II.3.2 Lines 102, 108 — `O(L)` `Transpose.TM`
Complexity of Stone Shuffle and `2`-Tape Row Shear, Plus Simultaneous Dyadic Commutator Rank).**
1. There exists a deterministic multitape Turing machine `M_shuf : Transpose.TM` and `C_shuf : ℕ`
   computing one Stone shuffle pass `stoneShuffleTMMatrix m A` on `d = 2^m` (`m ≥ 1`) in
   `≤ C_shuf * inputLength (2^m)` steps.
2. There exists a **`2`-work-tape** machine `M_shear : Transpose.TM` (`M_shear.k = 2`) and
   `C_shear : ℕ` computing the within-row shear `rowShearTMMatrix d A` for all `d ≥ 1` in
   `≤ C_shear * inputLength d` steps.
3. Over **every** field `F`, for all `m ≥ 1` (`d = 2^m`), all `b ≥ 1`, and **every** dyadic column
   bit scale `j : Fin m`, the commutator `[S, I_row ⊗ G_j]` of Stone's shuffle `S` with the `j`-th
   dyadic column-digit involution `colBitFlipGridLinear F b j` has exact macroscopic rank
   `b * (2^m)^2 / 2` simultaneously across all `m = log₂ d` scales! -/
def Diagnosis_StoneShuffleAndRowShearMachineComplexitySpec : Prop :=
  (∃ (M_shuf : Transpose.TM) (C_shuf : ℕ),
    ∀ (m : ℕ) (A : Transpose.Matrix), 1 ≤ m →
      let d := 2 ^ m
      Transpose.ComputesWithin M_shuf
        (Transpose.encode d (Transpose.entryBits d) A)
        (Transpose.encode d (Transpose.entryBits d) (stoneShuffleTMMatrix m A))
        (C_shuf * Transpose.inputLength d)) ∧
  (∃ (M_shear : Transpose.TM) (C_shear : ℕ),
    M_shear.k = 2 ∧
    ∀ (d : ℕ) (A : Transpose.Matrix), 1 ≤ d →
      Transpose.ComputesWithin M_shear
        (Transpose.encode d (Transpose.entryBits d) A)
        (Transpose.encode d (Transpose.entryBits d) (rowShearTMMatrix d A))
        (C_shear * Transpose.inputLength d)) ∧
  (∀ (F : Type*) [Field F] (m b : ℕ) (j : Fin m),
    1 ≤ m → 1 ≤ b →
    let S := stoneShuffleGridLinear F m b
    let G := colBitFlipGridLinear F b j
    finrank F (LinearMap.range (S.comp G - G.comp S)) = b * ((2 ^ m) ^ 2) / 2)

end BoundedArityDecoders
