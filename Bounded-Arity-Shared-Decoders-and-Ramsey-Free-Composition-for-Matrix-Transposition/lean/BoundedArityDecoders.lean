import BoundedArityDecoders.BoundedAritySetCapacity
import BoundedArityDecoders.AffineCubeComposition
import BoundedArityDecoders.SumsetRankDeficit
import BoundedArityDecoders.OperatorDuality
import BoundedArityDecoders.SwapCodeAnswers
import BoundedArityDecoders.NativeSweepInterface

/-!
# Bounded-Arity Shared Decoders and Ramsey-Free Composition for Matrix Transposition

Root module importing all formal claim specifications for Paper 20 (`README.md`):

* `BoundedArityDecoders.BoundedAritySetCapacity` — Breakthrough 1 & Blueprint Part I:
  bounded-arity nonlinear shared-decoder capacity (`Theorem 1`), boundary controls, growing
  classes, and the finite/asymptotic `M = 1, Δ = O(1)` dichotomy.
* `BoundedArityDecoders.AffineCubeComposition` — Breakthrough 2A & Blueprint Part II:
  affine `k`-cube common-message growth, `d = 13` AP-free 2-cube sharpness control, `d = 4`
  same-interval coded factorization control, and Hales–Jewett-free two-stage cutoffs.
* `BoundedArityDecoders.SumsetRankDeficit` — Breakthrough 2B & Blueprint Part II:
  shifted `(2 M₂)`-fold sumset polynomial recurrence, iterated Kővári–Sós–Turán extraction,
  `Ω(b d (log d)^(1 / (2 M₂ - 1)))` two-stage rank deficit, `d = 12` single-class band control,
  and the macroscopic two-stage rank target.
* `BoundedArityDecoders.OperatorDuality` — Breakthrough 3 & Blueprint Part III:
  exact pairwise shift-collision characterization, anti-diagonal tensor untwisting, Operator
  Schmidt Rank separation (`rk_⊗(S) = 4` vs. `rk_⊗(τ) = d^2`), `t ≥ log₂ d` pass lower bound,
  row-shear / row-diagonal alternation control, and skew one-time-pad marginal trap.
* `BoundedArityDecoders.SwapCodeAnswers` — Two Bonus Answers to Paper 17:
  explicit 3-Kronecker-term family beating `d(d + 1)/2` for `d = 6, 7, 9, 12` (`Remark 4.6`)
  and exact resolution of literal `Problem 9.3` (*Both sides, all scales*).
* `BoundedArityDecoders.NativeSweepInterface` — Diagnosis & Blueprint Part III:
  Statement `(T)` (`¬ Transpose.LinearTimeTransposable`) and periodic head-motion sweep-cone
  pullback directly onto nonlinear cut fibres without fibre linearization (`Problem 9.4`).
-/
