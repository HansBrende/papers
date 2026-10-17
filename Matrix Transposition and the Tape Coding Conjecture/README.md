# Matrix Transposition and the Tape Coding Conjecture

Hans Brende and Claude Opus 5.5 (Anthropic), October 2026.

- [`paper/`](paper/): the paper ([`main.pdf`](paper/main.pdf)) and its LaTeX sources. License: CC BY 4.0
  ([`paper/LICENSE`](paper/LICENSE)).
- [`lean/`](lean/): the Lean 4 formalization (Lean and Mathlib v4.34.1). License: Apache 2.0
  ([`lean/LICENSE`](lean/LICENSE)).

## The question

Can a deterministic multitape Turing machine transpose a d × d matrix with ⌈log₂ d⌉-bit entries, written
row by row, in time linear in the input length L = d²⌈log₂ d⌉? This statement, (T), is fixed in the frozen
Lean file [`lean/Transpose/Statement.lean`](lean/Transpose/Statement.lean) as `Transpose.LinearTimeTransposable` (the Lean files call the side length n). By a reduction of Harvey and van der Hoeven, a linear-time multiplication
machine would give a linear-time transposer (their Corollary 6.9, which has no overhead at this entry width). (T) is open, and this work does not decide it.

## What is proved

Everything in the following list is proved in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The
paper states each result with its Lean declarations and file.

- **Locality and counting.** A cut lemma for every set of time steps, and a discrete isoperimetric inequality
  on the block network of a run (paper §§3–4).
- **Theorem P and Theorem P′.** Every transposer with at least one work tape needs Ω(log d) passes in which all heads move monotonically,
  whatever it does with its data: oblivious machines (P) and every machine running in time poly(L) (P′), also
  when correct only on a 2^(−O(d log d)) fraction of the inputs (§5).
- **Adaptive machines.** Block-level traces, the popular trace, and the cut lemmas on trace classes (§6).
- **Theorem M\*.** Along its most popular block-level trace, the rescaled work-head trajectories of every
  linear-time transposer converge, along subsequences, to 1-Lipschitz paths that satisfy an isoperimetric
  inequality: the heads must fold back. Also for non-uniform machines and for machines correct on a 2^(−o(L))
  fraction of the inputs (§7).
- **The Tape Coding Conjecture as a formal target.** Codes on time–space diagrams and their block networks; the
  conjecture (`Transpose.Tape.RobustNoCode_TM`) in no-code, flow and distance forms, proved equivalent; a proof of
  the conjecture refutes (T) (`not_linearTimeTransposable_of_robustNoCode`); weaker sufficient conditions
  (co-entropy O(d), infinitely many sizes, output at the end); consequences for non-uniform and average-case
  machines; every counterexample obeys Theorem M\* (§§8–9).
- **Plain versus robust.** The robust conjecture is the plain one plus an oracle hint of O(d log d) bits; the
  plain conjecture implies the robust one for linear and nearly linear codes, affine and low-degree sets, codes
  with few error patterns, constant hints and several covering families (§10).
- **XOR-frame recursions.** In the run model of an abstract XOR-frame recursion (the recursion behind the only
  claimed sub-(L log d) construction, an unrefereed preprint), every run realizing a gadget makes at least as many
  frame changes as the gadget has wires; with integer frames the runs' total jump rank is larger still (§12).

Four results are not formalized; the paper proves them in full. One (§11) shows that (T) is equivalent, up
to linear time, to the linear-time formulation of Harvey and van der Hoeven (their Theorem 6.11 with l = 1,
which takes entries of ⌈log₂ m⌉ bits for matrices of m bits). Two are barrier results (§11): a shift circuit on n bits with s gates, and an oblivious machine rotating in T steps, yield coding gains over routing of order at
least n log n/(s+n) and L log L/T (for T ≤ L log₂ L) respectively, that is, of order at least log n for
linear-size circuits and log L for linear-time machines. The fourth is the translation from gadgets to runs (§12), which gives every gadget cost at least W and
so, within the XOR-frame template, excludes linear time.

## What is open

- (T) itself.
- The Tape Coding Conjecture (a proof would decide (T); a refutation would give codes, not a machine).
- Whether the plain form of the conjecture implies the robust form.
- See §14 of the paper for more.

## Building and verifying

Install [elan](https://github.com/leanprover/elan), then in `lean/`:

```bash
lake exe cache get
lake build
```

Check the frozen files (the statement and its checker):

```bash
shasum -a 256 -c FROZEN.sha256
```

Check the axioms of every declaration cited in the paper (generated from the paper's LaTeX sources):

```bash
lake env lean PaperAxioms.lean
```

`Verify.lean` is the frozen checker for a future `Transpose/Answer.lean`, a proof of (T) or of its negation. That
file does not exist, so `lake env lean Verify.lean` currently fails with a missing-module error.

To build the paper, run `latexmk -pdf main.tex` in `paper/`.
