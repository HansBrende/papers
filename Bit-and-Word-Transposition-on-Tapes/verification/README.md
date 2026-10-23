# Verification

`contracts.json` maps manuscript results and supporting interfaces to exact
Lean declarations, including the complete native bit-to-word implication.
The current map is complete and has no pending entries. Its mapped modules
are imported by `lean/BitWord.lean`; their closure must cover every authored
module under `lean/BitWord/`.

Run `python3 verification/verify.py` from the paper directory. The script:

1. Validates the declaration map and aggregate imports.
2. Follows all local imports from the mapped modules, rejects proof escapes in
   those sources, and records their hashes together with the package pins.
3. Checks manuscript labels, references, citations, and an exact map of every
   numbered definition or result (including any explicitly pending result).
4. Runs an ordinary `lake build` with the mapped modules as explicit targets,
   then checks their combined imports with `lake env lean BitWord.lean`.
5. Runs a Lean audit of every declaration owned by that local module closure,
   including uncited helper declarations. Lean's `collectAxioms` must return
   only `propext`, `Classical.choice`, or `Quot.sound`. Every mapped declaration
   must be present, and its elaborated type and universe parameters are logged.
6. Confirms that the audited local sources did not change during the run.

The generated audit, logs, and JSON receipt are in ignored `verification/build/`.
Commands and receipt source paths are relative. Raw local build logs may contain
machine-specific diagnostics and should not be committed. Shared library
dependencies remain the sibling packages named in `lean/lakefile.toml`; the
audit does not replace their independent source reviews or preservation guards.

`passed_mapped_contracts` means precisely that these checks passed for the
recorded source hashes, including all authored local Lean modules. It does not
certify the English-to-Lean correspondence or the PDF layout. Earlier
`passed_components` receipts cover only the exact partial map and sources they
record; they do not certify the completed reduction. Any source or map change
requires a fresh audit.

`build_paper.py` separately runs `latexmk` and records the PDF hash. Visual review
and semantic manuscript review are separate from both successful compilation
and the axiom audit.

`manuscript/semantic-review.json` records the manual English/Lean correspondence
and focused novelty review, including source comparisons and their limitations.
`manuscript/review.json` records visual checks of the exact PDF hash.
