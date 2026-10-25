# Bit and Word Transposition on Tapes

By Hans Brende and GPT-6 Astra (OpenAI).

This paper proves a native bit-to-word transposition reduction and barriers
to reversing the reduction with bounded-stage word calls and bounded-state scans.
Its constructive extension computes column phases and periods in linear time,
and shows that full normalization by this particular phase is equivalent to
canonical linear-time word transposition.
The unrestricted converse and unrestricted linear-time transposition remain open.

The uniform native implication, address factorization, interval-compiler
bounds, and nonlinear scan bounds have Lean proofs. Exact declarations are
listed in [the declaration map](verification/contracts.json). The native
reduction accepts an arbitrary adaptive dyadic bit transposer and pays for
raw-input setup, oracle isolation and cleanup, padding, and output.

The phase extractor, exact marker lemma, and full-normalizer equivalence have
complete written proofs, including native tape costs, in the manuscript's
constructive section. **These three results are not formalized in Lean.** They
are recorded in [a separate proof-status map](verification/written-results.json).
The extractor returns indices, not normalized payload; producing that full
payload remains as hard as the canonical transposition question. Independently
normalizing the two recursive children does not suffice.

## Formalization todos

- Formalize the vector-polynomial phase recurrence, period formula, and
  two-coefficient selector, including zero and short-period columns.
- Realize the selector and phase extractor in the shared native model, with
  raw size discovery, fixed tape pools, and the nested metadata cost bound.
- Prove the exact marker lemma and both full-normalizer reductions in that
  model, reusing the existing raw-input wrappers and transpose interfaces.

## Building and verifying

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
It checks the distinction between Lean-mapped and written-only results, but
does not certify the written proofs, English statements, or rendered PDF.
See [verification notes](verification/README.md) for the precise scope.

The [historical checked snapshot](verification/verified.json) records the successful audit
of all 143 modules, 9,532 declarations, and 57 mapped endpoints. The
[original PDF review](verification/manuscript/review.json) covers the earlier
eleven-page version; the [original semantic and novelty review](verification/manuscript/semantic-review.json)
records statement correspondence, strengthenings, simplifications and source
comparisons for that version. The Lean sources and declaration map are
unchanged by the constructive extension. Its current proof-status and PDF
checks are recorded in the [extension review](verification/manuscript/phase-review.json).

To build the manuscript with an installed TeX distribution and `latexmk`:

```sh
python3 verification/build_paper.py
```

Local build logs and generated audit files are ignored. Public tooling and
instructions use relative paths and discover executable locations at runtime.
