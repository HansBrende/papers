MANUSCRIPT AND VERIFICATION GUIDE

Start here
  ../../paper/main.pdf          Complete review copy
  ../../paper/main.tex          LaTeX entry point
  ../../paper/references.bib    Cited bibliography
  declarations.json            Numbered results and all formal annotations
  attribution-ledger.json      Source uses, provenance, novelty qualifications
  completion.json              Final artifact and review receipt

The original six theorem families are the adaptive separator/treewidth bounds, fixed
two-coordinate Boolean packet bounds, including helper-selected global recoding, affine-motion barriers,
fully paid native padding, two-stage helper toll, and scan-palette/recursive
stage exclusions. The adaptive-coding/ extension adds nonlinear adaptive forest
bounds and expander-shear recovery/construction results. Its review record
distinguishes these from the historical packet-strengthening/ revision.
The generated declarations.json records the current counts of numbered
definitions/results and explicitly cited formal declarations. The unrestricted canonical transposition question
remains open. Exact Lean statements and proofs take precedence over the prose.

Reproduce from the follow-up folder

Keep the first paper in its original adjacent folder. Install elan and the
pinned toolchain. Retain the Lake/mathlib pins. Python 3 is needed for the
verification scripts; latexmk, BibTeX and the packages in paper/main.tex are
needed for the multi-file LaTeX build. Put latexmk on PATH or set LATEXMK
to its executable; resolved executable paths are not written to public receipts.

  python3 verification/fetch_openai_metric.py
  python3 verification/check_upstream.py
  cd lean
  lake exe cache get
  cd ..
  python3 verification/manuscript/verify.py
  python3 verification/manuscript/build_paper.py

The source fetcher accepts --source-root PATH for an existing offline checkout,
and --check for an already installed copy. The installer verifies the pinned
204-module source closure and retains its attribution and license. Network
access is required only when dependencies are absent and must be fetched.

verify.py runs prepare.py, verifies the mathematical source inventory and upstream
sources (with the explicit comment/editorial and proof-refactor records described
below), checks the ordered additive proof manifests in source_extensions.py, performs an ordinary full
library build, builds every explicitly
cited module, and runs lean/PaperAxioms.lean. The latter is generated from the
manuscript rather than maintained as a separate subset. It audits every cited
declaration and rejects axioms other than propext, Classical.choice, Quot.sound.
The generated PacketAxioms.lean additionally checks every declaration in the
new additive modules against the same axiom whitelist. ProofRefactorAxioms.lean
separately checks the intentionally refactored original modules.
The proof-refactor audit compares every original declaration in those modules
with its captured pre-refactor elaborated type; names, universe parameters and
expression structure are preserved, disregarding only bound-variable labels.
For the broader historical SupportAxioms.lean audit, run from the follow-up folder:
  python3 verification/run_axiom_audit.py support
The helper builds all imports first, including audit-only first-paper modules.
Use both instead of support to run both audits. A bare lake build need not
build dependencies that occur only in these audit entry points.

build_paper.py keeps intermediate output in paper/build/ and copies a successful
PDF to paper/main.pdf. Review the TeX log for missing references and layout
warnings; a successful compile alone is not a visual review. For rendered
inspection with Poppler:

  mkdir -p paper/build/rendered
  pdftoppm -r 90 -png paper/main.pdf paper/build/rendered/page

Evidence and limits

verification.json contains commands, exit codes, log hashes, source hashes and
audit coverage. latex-build.json identifies the produced PDF. The contracts
and the final-pass cross-review receipts record English-to-Lean checks;
the visual-review receipts identify the actual rendered pages examined. The
completion receipt binds these to the delivered files. The active review-set.json identifies the semantic, program-role, and visual
receipts for this revision. The opus-review/ folder records every reviewer
suggestion and its disposition. The pre-review manuscript and raw receipts are preserved privately outside
this repository, identified by archive name and digest in the publication
normalization manifest. Older final-pass receipts refer to that earlier
manuscript; they are not current review claims.
Historical public records and scripts are path-sanitized views, not verbatim
run logs. Project paths resolve from the follow-up folder. external/ labels
identify private historical inputs and scratch artifacts, not public build
dependencies. Original bytes and their hashes are preserved privately; embedded
historical digests still refer to those original bytes. The normalization
manifest records each original-to-public digest transition. Current source
and proof hash maps are unchanged, and the active verifier regenerates portable
receipts. See ../../../CONTRIBUTING.md.


Rebuilding a PDF can change its timestamp/hash, so an old visual receipt must not be relabeled as
a review of a newly changed document without comparison or inspection.

With pypdf available in the chosen Python environment, run
  python3 verification/manuscript/completion_check.py
to check the current files against those receipts and refresh completion.json.
This command checks review bindings; it does not perform a new semantic or
visual review. Changed manuscripts require appropriate new reviews.

The checks are an ordinary build and declaration axiom audit, not a claim of a
new empty-environment kernel replay of every imported expression. Source and
visual reviews were performed by AI agents. They are not external human peer
review, and source attribution checks do not establish exhaustive novelty.

The earlier manuscript review changed two complete documentation comments in
UnconditionalPaidPadding.lean and no mathematical code. The current packet
extension adds new mathematical modules listed in
packet-strengthening/source-extension.json; their hashes are checked by the
current verifier, separately from the immutable original baseline.
The later adaptive-coding/source-extension.json adds its own files and numbered
results without changing the earlier packet manifest. The verifier checks the
complete union, rejects duplicate files, and checks the succession of statement
inventories. It does not infer that a recorded source hash proves a theorem;
the matching build and axiom checks provide that evidence.
The second review refactors old XOR endpoints into specializations of the
Boolean-packet results and the unweighted cover into the weighted cover.
The proof-refactor manifest records exact reversible edits to the four affected
baseline files, moved shared declarations and preserved elaborated types.
source_guard.py reconstructs original audited bytes from the recorded changes
and rejects unrecorded changes. Fresh builds, type comparisons and axiom audits
check the refactored sources. Historical proof receipts are not rewritten. upstream-editorial-amendment.json in the parent verification folder
records a separate committed first-paper editorial update. The upstream
check verifies the frozen proof files and the documented editorial revision,
ignoring generated artifacts; tracked or nonignored added files still fail. PaperAxioms.lean is the new generated audit
entry point. The shared first-paper framework is imported directly through
lean/upstream, with adapter build products kept in the follow-up folder.
