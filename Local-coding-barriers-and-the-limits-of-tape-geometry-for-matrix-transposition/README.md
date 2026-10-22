# Local coding barriers and the limits of tape geometry for matrix transposition

The follow-up manuscript by **Hans Brende and GPT-6 Astra (OpenAI)** is in
[paper/main.pdf](paper/main.pdf); its complete LaTeX source starts at
[paper/main.tex](paper/main.tex). It uses **d** for the matrix dimension.
The paper presents the six theorem families, exact scopes, proof outlines,
connections to the first paper, attribution and a roadmap. Lean statements
and proofs are authoritative; the prose outlines are explanatory conveniences.

The [manuscript verification guide](verification/manuscript/README.txt) explains
how to reproduce the build and audit. The [completion receipt](verification/manuscript/completion.json)
ties the final sources and PDF to the declaration, attribution, semantic and
rendered-page reviews. No unrestricted transposition or multiplication bound
is claimed, and novelty qualifications remain explicit.

All **six target theorem families are formalized, independently reviewed at
source level, and kernel checked after strengthening and cleanup**. This
completes the formalization task; unrestricted transposition complexity remains
open in this work. The source reviews do not replace human peer review or
establish literature novelty.

The [fresh R1909 audit](verification/r1909-audit.txt) compares every target
against the recovered original specification, discloses unformalized side claims,
and records three new strengthenings. It removes another 1739 net mathematical
lines and passes a fresh kernel replay as well as the build and axiom audit.

The [R1910 strengthening and reuse pass](verification/r1910-audit.txt) extends
the two-stage entropy toll to arbitrary input distributions, exposes universal
padding state/tape bounds, improves the path/cycle XOR error coefficient from
3 to 2√2, and removes 693 more net mathematical source lines.
A module split removes unnecessary compiler dependencies from 232 analytic
modules. Forty-seven jump proofs share general rules; the full build and 6289-declaration
axiom audit pass.

The [R1911 pass](verification/r1911-audit.txt) extends adaptive separator and
treewidth bounds to arbitrary input distributions and weakens the affine
approximation lemma to pointwise convergence. Shared compiler, finite-code
and XOR proofs remove duplication; the broader statements leave total source
almost unchanged (-10 lines). Full build and 6297-declaration axiom audit pass.

The [R1912 build-speed pass](verification/r1912-audit.txt) reduces the measured
compiler target rebuild from **62.8s to 13.3s**, while its merged target now
contains twenty former source bodies. Modules fall from 1157 to 896; the compiler
prerequisite path falls from 188 to 38. All 6297 original audited declaration
contracts are preserved: 6028 exact type matches, 267 kernel conversions and
two checks of exact archived theorem headers. The full build and
6306-declaration axiom audit pass.
This target measurement is not a whole-project speedup claim. Use the
[module guide](verification/r1912-module-guide.txt) to locate moved proofs.

The [R1914 analytic build pass](verification/r1914-audit.txt) reduces the clean paired target proof check from **14.39s to 5.33s**. All6306 original audited contracts and all six theorem families are preserved. See the report for the distinct matched-workload evidence and its limits.

The [R1915 spectral build pass](verification/r1915-audit.txt) reduces the matched cached proof-edit rebuild from **75.061s to 17.189s** in one observed pair. All 6306 original audited contracts and all six theorem families are preserved. See the report for the distinct matched-workload evidence and its limits.

The [R1916 strengthening pass](verification/r1916-audit.txt) improves the finite XOR bound and weakens the affine approximation premise to pointwise error. Thirteen compiler proofs now share one embedding lemma; total source grows by 51 lines after the stronger statements. All six theorem families remain proved.

Start with the [exact statements, improvements, scope and relevance](paper/verified-results.txt).
The six families are:

- [Adaptive separators and average treewidth](lean/TransposeFollowup/AdaptiveTreewidth.lean),
  now allowing arbitrary input laws and finite original-row query supports.
- [Nonlinear row recoding with fixed pairwise XOR](lean/TransposeFollowup/XorDegreeBound.lean).
- [Affine motion and physical approximation barriers](lean/TransposeFollowup/PhysicalAffineApproximationObstruction.lean).
- [Unconditional fully paid padding](lean/TransposeFollowup/UnconditionalPaidPadding.lean),
  with universal runtime, state and tape overhead constants preceding the payload machine.
- [Exact two-stage helper toll](lean/TransposeFollowup/TwoStageHelper.lean).
- [Concrete scan palettes](lean/TransposeFollowup/MatrixPaletteObstructions.lean) and
  [contracting recursion with exceptional work](lean/TransposeFollowup/NativeExceptionalRecursion.lean).

The [referee record](verification/r1908-referee-reviews.json) includes findings
and resolutions. The [validation receipt](verification/support-build.json)
and [current completion record](verification/r1916-completion.json) identify the checked
sources and permitted axioms. The [cleanup inventory](verification/r1908-cleanup.json)
records 24 retired modules preserved in the research archive; independent unused
mathematical results were retained deliberately. The
[historical implementation milestones](verification/historical-implementation-milestones.txt)
are provenance, not current status. Full checkpoint history remains in
[progress](verification/progress.txt).

The [prior-art note](paper/prior-art.txt) and [bibliography](paper/prior-art.bib)
record the known failure of Mittal--Raz Conjecture36 and its attribution.
Its refutation is not a contribution claimed by this follow-up.

The `lean/upstream` package imports the sibling original paper directly and
writes dependency build artifacts here. The original directory is unchanged.
The shared original definitions are reused, not copied. Thirteen modules in
`lean/FixedTapeCompiler` reuse our earlier local native compiler proofs;
[provenance](verification/archive-source-provenance.json) records those sources.
A [pinned source adapter](lean/openai-metric/README.txt) imports the external
OAI scalar theorem. Keep the Lean toolchain and mathlib pins unchanged.

From this paper directory, verify or fetch the pinned external dependency with
`python3 verification/fetch_openai_metric.py` (`--check` verifies an existing
installation). Then run `lake build` and `lake env lean SupportAxioms.lean`
from `lean/`. `python3 verification/check_upstream.py` verifies that the original
paper's 117 files and directory inventory remain unchanged.

Development branch: `codex/transpose-followup-formalization`.
