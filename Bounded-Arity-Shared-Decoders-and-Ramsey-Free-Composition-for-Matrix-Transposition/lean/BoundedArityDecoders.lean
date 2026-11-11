import BoundedArityDecoders.BoundedAritySetCapacity
import BoundedArityDecoders.BoundedAritySetCapacityProofs
import BoundedArityDecoders.SetCapacityConsequences
import BoundedArityDecoders.AffineCubeComposition
import BoundedArityDecoders.AffineCubeCompositionProofs
import BoundedArityDecoders.AffineCubeConsequences
import BoundedArityDecoders.SumsetRankDeficit
import BoundedArityDecoders.SumsetRankDeficitProofs
import BoundedArityDecoders.SumsetRankConsequences
import BoundedArityDecoders.OperatorDuality
import BoundedArityDecoders.OperatorDualityProofs
import BoundedArityDecoders.SwapCodeAnswers
import BoundedArityDecoders.SwapCodeAnswersProofs
import BoundedArityDecoders.DualityAndSwapConsequences
import BoundedArityDecoders.NativeSweepInterface
import BoundedArityDecoders.NativeSweepInterfaceProofs
import BoundedArityDecoders.MachineSweepConsequences
import BoundedArityDecoders.DiagnosisAndBarriers
import BoundedArityDecoders.DiagnosisAndBarriersProofs
import BoundedArityDecoders.DiagnosisAndBridgesConsequences

/-!
# Bounded-Arity Shared Decoders and Ramsey-Free Composition for Matrix Transposition

Root module importing all formal claim specifications, kernel-verified proofs, and structural /
asymptotic consequence modules for Paper 20 (`README.md`):

* `BoundedArityDecoders.BoundedAritySetCapacity` / `Proofs` / `SetCapacityConsequences` —
  Breakthrough 1 & Blueprint Part I: bounded-arity nonlinear shared-decoder capacity (`Theorem 1`),
  two-sided `Θ(1 / Δ)` `pMin` scaling (`> 1 / (e (Δ + 1))`), explicit `Δ = 1` (`3/4`) and `Δ = 2`
  (`23/27`) corollaries, Wall 1 exact all-dimension logarithmic asymptotic (`d^2 - log_q d + o(1)`),
  sublinear-class `M = o(d / Δ)` broken-cell rate-<1 corollary, and `M = 1, Δ = O(1)` dichotomy.
* `BoundedArityDecoders.AffineCubeComposition` / `Proofs` / `AffineCubeConsequences` —
  Breakthrough 2A & Blueprint Part II: affine `k`-cube common-message growth, single-subset
  Cauchy–Schwarz extraction (including `3`-AP-free / Behrend subsets), `d = 13` arbitrary-field
  2-cube and Paper 19 progression sharpness controls, `d = 4` all-width / `GF(2)` coded
  factorization vs. uncoded bit-lane impossibility, and polynomial-class two-stage cutoffs.
* `BoundedArityDecoders.SumsetRankDeficit` / `Proofs` / `SumsetRankConsequences` —
  Breakthrough 2B & Blueprint Part II: intrinsic diameter `finsetNatDiam`, `bandRowSpace`
  annihilating polynomial rank bound, iterated Kővári–Sós–Turán extraction, explicit-constant
  `Ω(b d (log d)^(1 / (2 M₂ - 1)))` and `M₂ = 1` `Ω(b d log d)` two-stage rank deficits,
  unconditional `ℂ` `d = 12` character-band witness + `bandRowSpace` equivalence, and open target.
* `BoundedArityDecoders.OperatorDuality` / `SwapCodeAnswers` / `DualityAndSwapConsequences` —
  Breakthrough 3, Blueprint Part III & Two Bonus Answers to Paper 17: explicit `TensorProduct`
  anti-diagonal untwisting and mask-floor realization, general `(d, R)` OSR pass lower bound,
  `IsRowDiagonalOp` source-arity gauge invariance, discrete Shannon mutual information `= 0` for
  the skew one-time pad, unified `d ∈ {3, 4, 6, 7, 9, 12}` 3-Kronecker-term disproof of the
  pairing bound, and literal `Problem 9.3` `1/2 d^2 + o(d^2)` resolution + Walsh boundary dichotomy.
* `BoundedArityDecoders.NativeSweepInterface` / `Proofs` / `MachineSweepConsequences` —
  Diagnosis & Blueprint Part III: Statement `(T)` (`¬ Transpose.LinearTimeTransposable`), `TM`
  cut-cone determination, genuine `M.δ` causal-cone tree evaluation (`tmPeriodicSweepExtraction_cutAbsorbed`
  and `tmPeriodicSweepExtraction_cutLabelRefined`), and conditional implication chains to `(T)`.
* `BoundedArityDecoders.DiagnosisAndBarriers` / `Proofs` / `DiagnosisAndBridgesConsequences` —
  Section I Diagnosis, Section II Benchmarks & Machine-to-Operator Bridges: word-step `TCP`
  cell-cone reduction, Paper 18 `AdaptiveTransfer` interior `(b - 6s)_+` cone pullback, separated
  high-rate limit, multi-bit block-edge shift barrier, `⌈√(2 M)⌉` & `5/8` certificate bridge,
  `invVdW → ∞`, modular Behrend & random `ZMod d` progression bounds, `O(L)` `Transpose.TM`
  Stone shuffle / unshuffle / row shear, and definitional `encodeTMMatrixToGrid` bridges.
-/
