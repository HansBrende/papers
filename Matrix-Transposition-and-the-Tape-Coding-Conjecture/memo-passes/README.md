# Adaptive Pass Bounds without a Runtime Assumption

Hans Brende and GPT-6 Astra (OpenAI), October 2026.

Extension memo to the first paper by Hans Brende and Claude Opus 5.5.
[PDF](https://hansbrende.github.io/papers/Matrix-Transposition-and-the-Tape-Coding-Conjecture/memo-passes/paper/main.pdf) · [LaTeX](paper/) (CC BY 4.0) · [Lean](lean/) (Apache 2.0).

## The question

Does the adaptive logarithmic-pass lower bound still hold without a
polynomial runtime assumption? For halting machines in the original model,
yes. The underlying reversal/run-length principle is classical.

## What is proved

All new numbered results are Lean verified in the first paper's native model:

- A halting run with `r` passes satisfies `L + T + 1 ≤ (L + 1) C_M^r`,
  with `C_M = (2k + 3)(3(q + 1)(g + 1)^k + 1)`.
- Substituting that bound into the existing adaptive information theorem gives
  a grouped inequality without a runtime premise, also for a specified set
  of correct halting inputs with its co-entropy cost.
- For positive widths with `d ≤ 2^b`, `kd ≤ A_M(k + 1)^r`; the paper gives
  `A_M` explicitly. In particular, canonical-width transposition needs
  `r ≥ log_(k+1)(d) − O_M(1)` for `k ≥ 1`.
- The old runtime-restricted consequence is derived by discarding its extra
  premise. The original finite-time inequality is reused, not superseded.

The cited declarations use only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## What is open

This does not decide linear-time transposition. Many short passes can fit
inside linear time. The run-length lemma also does not cover arbitrary
nonhalting prefixes, for which the original finite-time theorem remains useful.

## Building and verifying

Clone the whole repository. The Lean package imports `../../lean`; do not
copy this memo out of its parent paper. In `lean/`:

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

From this directory, regenerate the declaration index and axiom check with
`python3 tools/lean_index.py`. In `paper/`, run `latexmk -pdf main.tex`.
