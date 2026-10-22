MANUSCRIPT AND VERIFICATION GUIDE

Start here
  ../../paper/main.pdf          Complete review copy
  ../../paper/main.tex          LaTeX entry point
  ../../paper/references.bib    Cited bibliography
  declarations.json            Numbered results and all formal annotations
  attribution-ledger.json      Source uses, provenance, novelty qualifications
  completion.json              Final artifact and review receipt

The six theorem families are the adaptive separator/treewidth bounds, fixed
coordinate-XOR bounds after nonlinear row recoding, affine-motion barriers,
fully paid native padding, two-stage helper toll, and scan-palette/recursive
stage exclusions. There are 31 numbered definitions/results and 142 explicitly
cited formal declarations. The unrestricted canonical transposition question
remains open. Exact Lean statements and proofs take precedence over the prose.

Reproduce from the follow-up folder

Keep the first paper in its original adjacent folder. Install elan and the
pinned toolchain. Retain the Lake/mathlib pins. Python 3 is needed for the
verification scripts; latexmk, BibTeX and the packages in paper/main.tex are
needed for the multi-file LaTeX build.

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

verify.py runs prepare.py, verifies the unchanged mathematical and upstream
sources, performs an ordinary full library build, builds every explicitly
cited module, and runs lean/PaperAxioms.lean. The latter is generated from the
manuscript rather than maintained as a separate subset. It audits every cited
declaration and rejects axioms other than propext, Classical.choice, Quot.sound.
The broader historical SupportAxioms.lean audit remains available separately.

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
completion receipt binds these to the delivered files. The final editorial
pass uses final-pass-*-cross-review.json and final-pass-visual-part*.json;
older receipts are retained as history. final-pass-program-roles.json records
the contribution of each numbered statement to the research programs.
Historical audit records and one-off research scripts retain the paths used
when they ran, including the folder's earlier capitalization. The reproduction
commands above locate the current folder automatically; paths within this
paper in the current attribution ledger are relative to that folder.

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

The mathematical Lean sources and the original sibling paper were not changed
while preparing this manuscript. PaperAxioms.lean is the new generated audit
entry point. The shared first-paper framework is imported directly through
lean/upstream, with adapter build products kept in the follow-up folder.
