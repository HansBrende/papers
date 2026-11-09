# Regular-Recursion Obstructions for the Five Cascade Schedules

**Hans Brende and GPT-6 Astra (OpenAI)**, November 2026.

A memo to *Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings*
(Paper 16), applying *Local Coding Barriers and the Limits of Tape Geometry for
Matrix Transposition* (Paper 2), **Theorem 7.5**.

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean library](lean/README.md), licensed under [Apache 2.0](lean/LICENSE).
- [Reproduction instructions](tools/README.md), [source pins](verification/source-pins.json)
  and [finite-check receipts](verification/).

## The question

Can any choice of finite-state local computations on one of the five exact
published cascade schedules transpose every input in linear time? The schedules
pass the finite tests reported in Paper 16, but also satisfy an earlier obstruction.

## What is proved

For every fixed finite work alphabet, there are `δ > 0` and `d₀` such that each
of C1–C5, at every dyadic `d ≥ d₀`, satisfies

\[
q + L - \log_2 |S| \ge \delta L,\qquad L=d^2b.
\]

Here `q = ceil(log₂ |Q|)` counts controller bits and `S` is any nonempty set on
which the program outputs the correct transpose. The result holds both for
`b = 1` and `b = max(1, ceil(log₂ d))`. Head moves and append times are fixed,
but arbitrary nonlinear, time-dependent local rules may rewrite **every** scanned
work cell, including transit visits. No routing or preservation assumption is used.
Fixed states are a special case; even `q = o(L)` gives exponentially small ambient
success. Public initial work words are allowed, and a complete deterministic
entry record `Z` gives the extension `q + L − log₂|S| + H(Z) ≥ δL` under the
memo's stated entry conditions.

The imported obstruction is **Paper 2, Theorem 7.5**, with Definitions 7.2/7.4
and Lemma 7.3. It excludes complete contracting clocks whose every fixed actual
stage has a finite-affine limiting head profile. The count of pieces may grow
with depth. The memo pays every positioning, wrap, preparation and output tick.
It gives a reusable criterion for future variants, not just five isolated tests.

| Exact constructor | Work tapes | Legal dyadic dimension | Own-stage constant `a` |
| --- | ---: | --- | ---: |
| `c1_torus_cascade` | 2 | `d ≥ 16` | 128 |
| `c2_bfly_cascade` | 2 | `d ≥ 4` | 128 |
| `c3_ten_entry_cascade` | 3 | `d ≥ 4` | 80 |
| `c4_no_overwrite_cascade` | 3 | `d ≥ 4` | 128 |
| `c5_comb_fanout` | 2 | `d ≥ 4` | 18 |

These are constructor domains, **not exclusion thresholds**. The clock gives
`T ≤ 2aL` and depth-at-least-`h` time at most `2aL·2⁻ʰ`. Geometry is proved for
all integer `b ≥ 1`; the transposition conclusion is limited to the two stated
width regimes. C1's eventual parameter formulas stabilize at `d ≥ 256`, which
also is not the unknown exclusion threshold.

The five exact-integer schedule families are those of the original Rust source at
[`9ffa8f2e5494988731a37c0bed8b0be6a046e5e8`](https://github.com/HansBrende/papers/tree/9ffa8f2e5494988731a37c0bed8b0be6a046e5e8).
The executable's finite integer ranges are distinguished from the mathematical
families. The proof uses the published sources, not a replacement generator.

## Formal verification status

The imported obstruction is Lean-verified. **C5 at canonical logarithmic width
is now formalized for its specified Lean tick word**, through the final real-deficit
bound. The proof constructs the actual clock, proves stage regularity, compiles
arbitrary local data rules, and pays the clock's controller cost. Its final theorem
has no assumed clock, simulation, or regularity certificate.

The library also supplies reusable clock accounting, a general native compiler,
finite-block regularity and real-deficit transfer. All cited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. The Lean statements are authoritative
for these results; the English outlines are explanatory.

The **combined five-schedule, two-width theorem remains partially formalized**.
The remaining written steps are:

- C1–C4's concrete clocks, endpoint budgets and limiting profiles.
- All-instance correspondence of the Rust C5 constructor with the declarative
  Lean word. This is source-audited and finitely compared, not a formal Rust proof.
- The `3b` bit-lane simulator, product correctness, motion preservation and transfer.
- The remaining case applications and finite minimum across constructors/widths.
  Real-deficit rounding and compiler-overhead removal are already formalized.
- Public initialization and the complete joint-entry-information extension.

These steps have written proofs in the PDF. Numerical checks are implementation
controls and are not premises of the asymptotic theorem.

## What is open

The constants `δ` and `d₀` have no numerical values here. No isolated experimental
size is certified impossible by the asymptotic argument. Unlisted variants,
the historical comparator, growing alphabets, other widths, and unrestricted
adaptive schedules are not classified. The general linear-time transposition
question (T) remains open. A new schedule can be screened by the memo's complete
clock/regularity criterion; merely resembling a cascade is insufficient.

## Building and verifying

Use a complete repository clone with sibling directories in place. The memo reuses
Paper 2 through a relative Lean dependency. Follow its
[dependency setup](../../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/README.md)
and retain its pinned Lean/Mathlib versions. In `lean/`:

```sh
lake build
lake env lean PaperAxioms.lean
```

From this memo directory:

```sh
python3 tools/lean_index.py --check
python3 tools/check_source_pins.py
python3 tools/lane_lift_control.py
python3 -B tools/check_geometry.py
python3 tools/check_c5_lean_trace.py
```

Regenerate the index with `python3 tools/lean_index.py`. The geometry check builds
and exports the unchanged original Rust crate. The saved controls cover 4,928 lane
inputs, 569,088 physical lane transitions, and ten original cascade exports with
273,065 steps. A further eight exact Lean–Rust C5 comparisons check 38,504 ticks,
including every positioning and append event. These finite comparisons do not
establish all-instance source equivalence. Details and receipt commands are in
[tools/README.md](tools/README.md).

Build the PDF in `paper/` with `latexmk -pdf -interaction=nonstopmode main.tex`.
