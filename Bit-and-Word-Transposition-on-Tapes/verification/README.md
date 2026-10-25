# Verification

`contracts.json` maps manuscript results and supporting interfaces to exact
Lean declarations, including the complete native bit-to-word implication.
This Lean map is complete and has no pending entries. Its mapped modules
are imported by `lean/BitWord.lean`; their closure must cover every authored
module under `lean/BitWord/`.

`written-results.json` separately lists the phase extractor, marker lemma,
and normalizer equivalence. These have complete written proofs but are not
formalized. A complete Lean map does not certify these additional results.

Run `python3 verification/verify.py` from the paper directory. The script:

1. Validates the declaration map and aggregate imports.
2. Follows all local imports from the mapped modules, rejects proof escapes in
   those sources, and records their hashes together with the package pins.
3. Checks manuscript labels, references, citations, and an exact map of every
   numbered definition or result against the union of the Lean and written
   maps. The maps must be disjoint; each written-only statement must carry
   its explicit `notformalized` marker.
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
certify the written proofs, English-to-Lean correspondence, or PDF layout. Earlier
`passed_components` receipts cover only the exact partial map and sources they
record; they do not certify the completed reduction. Changed Lean sources or
declaration maps require a fresh Lean audit. The published `verified.json`
remains a historical receipt for its exact hashes; the constructive extension
does not alter those Lean sources or declarations.

`build_paper.py` separately runs `latexmk` and records the PDF hash. Visual review
and semantic manuscript review are separate from both successful compilation
and the axiom audit.

`manuscript/semantic-review.json` records the original manual English/Lean
correspondence and focused novelty review, including their limitations.
`manuscript/review.json` records visual checks of that earlier PDF hash.
`manuscript/phase-review.json` records the constructive extension's current
written-proof review, proof-status checks, and rendered PDF inspection.
It is not a replacement Lean audit or a new literature-priority claim.
