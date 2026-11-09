# Cascade obstruction: Lean formalization

This standalone package uses Lean and mathlib v4.34.1 and the sibling Paper 2
package through the relative dependency in `lakefile.toml`.

```sh
lake build
lake env lean PaperAxioms.lean
```

The new declarations check the following reusable steps:

| Declaration | Statement |
| --- | --- |
| `DyadicClock.total_time_le` | An actual unary, two-stage clock with half-volume contraction has total time at most `2 * a * P`. |
| `DyadicClock.deep_time_le` | Its ticks at depths at least `h` total at most `2 * a * P * (1/2)^h`. |
| `exists_uniform_positive_gap` | For nonnegative costs on arbitrary size-dependent objects, exclusion of every vanishing-cost sequence at diverging sizes implies one eventual uniform positive gap. |
| `no_vanishing_native_dyadic_cost` | Paper 2's native regular-recursion theorem excludes vanishing normalized controller bits plus a certified integer correctness deficit. |
| `uniform_native_dyadic_gap` | The two preceding results give a uniform positive gap for any supplied native class whose every diverging sequence has regular dyadic clocks. |
| `Compiler.run_denote`, `Compiler.state_count` | Exact native simulation of arbitrary time-indexed simultaneous local rules, with `(T+1)(q+1)` states and unchanged alphabet/tape count. |
| `StageClockAssembly.toClock` | Construct an actual complete clock from uniquely labelled finite execution chunks and proved volume budgets. |
| `Raster.regular_of_ramp_approximation` | Bounded finite ramp approximations with vanishing normalized error imply actual fixed-stage regularity. |
| `uniform_native_real_deficit_gap` | Round the exact correctness deficit internally and remove uniformly sublinear compiler overhead. |
| `C5.uniform_c5_gap` | The concrete canonical-width C5 schedule has an eventual uniform positive source-controller-plus-real-deficit gap. All clock, simulation and regularity obligations are discharged. |

All names are in namespace `CascadeObstruction`. The generic native interfaces
retain their clock and regularity hypotheses; `C5.uniform_c5_gap` supplies them
from the actual specified schedule. `C5.CorrectCompletion` contains only a legal
dyadic dimension, arbitrary local rules/controller, and a nonempty correctness set.

The C5 pipeline is `C5Trace` → `C5Stages` → `C5Schedule` → `C5Clock` →
`C5ClockPaths` → `C5Regularity` → `C5Exclusion`, with the general compiler and
deficit transfer supplying the machine and counting interfaces. Geometry is
proved for every positive width; the native exclusion here is canonical-width only.

Still unformalized: C1–C4's concrete source applications, the bit-lane simulator,
the remaining finite case assembly, and public initialization/joint entry information.
The exact Rust-to-Lean C5 correspondence is source-audited and finitely compared;
this package does not contain a formal semantics of Rust.

`PaperAxioms.lean` is generated from every declaration cited in the manuscript.
All are proved using only
Lean's standard axioms (`propext`, `Classical.choice`, and `Quot.sound`).
