# Bit and Word Transposition on Tapes

By Hans Brende and GPT-6 Astra (OpenAI).

This paper proves a native bit-to-word transposition reduction and barriers
to reversing the reduction with bounded-stage word calls and bounded-state scans.
The unrestricted converse and unrestricted linear-time transposition remain open.

The uniform native implication, address factorization, interval-compiler
bounds, and nonlinear scan bounds have Lean proofs. Exact declarations are
listed in [the declaration map](verification/contracts.json). The native
reduction accepts an arbitrary adaptive dyadic bit transposer and pays for
raw-input setup, oracle isolation and cleanup, padding, and output.

The Lean package imports the preceding paper through a relative path, sharing
its native model and proofs. Clone the whole papers repository so both sibling
directories remain in place. Install [elan](https://github.com/leanprover/elan)
and Python 3; Lean and mathlib versions are pinned in `lean/lean-toolchain` and
`lean/lake-manifest.json`.

From this directory, run:

```sh
python3 verification/verify.py
```

This builds the mapped modules, checks their aggregate imports, and requires
their local import closure to cover every authored module. It checks every
declaration in that closure for axioms beyond `propext`, `Classical.choice`, and
`Quot.sound`, confirms that all mapped endpoints exist, and records source
hashes and raw elaborated endpoint types. Manuscript labels and citations are
also checked. A successful complete run says `passed_mapped_contracts`.
It is not a review of the English statements or the rendered PDF.
See [verification notes](verification/README.md) for the precise scope.

The [checked snapshot](verification/verified.json) records the successful audit
of all 143 modules, 9,532 declarations, and 57 mapped endpoints. The
[PDF review](verification/manuscript/review.json) records the eleven-page visual check. The
[semantic and novelty review](verification/manuscript/semantic-review.json)
records statement correspondence, strengthenings, simplifications and source comparisons.

To build the manuscript with an installed TeX distribution and `latexmk`:

```sh
python3 verification/build_paper.py
```

Local build logs and generated audit files are ignored. Public tooling and
instructions use relative paths and discover executable locations at runtime.
