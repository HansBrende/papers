> Historical checkpoint: this review predates the B1–B8 extension. See [the current integration record](integration.md) for the new scope and remaining formalization work.

# Independent English–Lean faithfulness review

Review date: 2026-11-10. This review concerns the working draft, not a release
certification. The reviewer did not author the draft or its Lean proofs and read
the repository's `CONTRIBUTING.md` before reviewing. No commit or push was made.

## Result

No unresolved substantive English–Lean mismatch was found. The review compared
all 39 numbered items: 37 formalized algebraic results, one formalized definition,
and the explicitly written-only paid two-work-tape theorem. It examined actual
definitions, theorem hypotheses and conclusions, and substantive proof paths,
rather than inferring coverage from declaration names or the generated index.

Three small scope/status issues were corrected during review:

- The coprime-retention corollary now says a **partition into two nonsingleton
  classes** forces the symmetric source. The former wording could include
  additional singleton classes, for which that conclusion need not follow.
- The symmetric-source correctness theorem was generalized to arbitrary class
  types, matching the manuscript's “every receiver partition.” The proof's
  decoder ignores its class argument. The revised declaration was reread.
- The introduction now explicitly identifies the native compiler and execution
  invariants as the remaining formalization obligation, consistent with the
  abstract, README and formalization appendix.

The native theorem remains clearly written-only. Neither a source dimension
calculation nor the algebraic construction is represented as verification of its
transition table, execution invariant, time bound or controller cost.

## Mathematical scope checked

- Capacity statements allow arbitrary deterministic source decoders and coupled
  lanes over the stated fields and finite-dimensional modules. The component,
  run and averaging arguments derive the bounds from actual source spaces.
  The periodic equality is scalar-width and includes its coprimality,
  characteristic and splitting-field conditions; scalar extension supplies the
  stated nonsplitting upper bound.
- The normal-basis interval construction and cyclic lift provide actual sources
  and recovery maps. Their width, parity, characteristic and dimension
  restrictions agree with the text. The binary constructions' quantifiers do
  not claim every width when only an extension-field width and its multiples
  are available.
- Scalar-closure defect, retention and stability use the stated common scalar
  action and actual shared-correctness sources. Correctness is not silently
  extended to the scalar hull. The varying-field stability records contain
  actual algebraic data; their numerical inequalities and boundedness are
  proved rather than supplied as certificates.
- The triple-source obstruction bounds arbitrary binary linear subcodes,
  including coupling among lanes. Its mixed-block asymptotic consequence has
  the advertised growing dimension and width. It does not assert a stronger
  universal nonlinear-source obstruction.
- Exact linear composition derives linear decoders from complete-domain class
  uniformity. This step is not applied to arbitrary source-only correctness.
  The common-message, progression and recurrence arguments derive the forced
  subspace and rank bound. The growing rank theorem retains `(d : F) ≠ 0` and
  proves divergence after normalization by `b*d`, not a fixed fraction of the
  full matrix volume.
- Nonlinear balance, agreement, period and sandwich statements retain their
  different architectures and hypotheses. Complete-space bijectivity is
  derived where needed from finite-state exactness. An unrestricted outer
  postprocessor is not inserted into the balance-based endpoint. Anchored and
  single-site endpoints derive their concrete group actions and transitivity;
  they do not assume those conclusions as certificates. The single-site proof
  includes `d = 3` and every positive width, with the coincident-index case
  treated separately.

The English outlines were checked for the logical steps underlying these
claims. They sometimes present a mathematically equivalent argument rather
than the exact Lean proof organization; no unsupported strengthening was found.

## Read scope and limits

All numbered statements and their outlines were read in
`paper/sections/model.tex`, `capacity.tex`, `structure.tex`, `constructions.tex`,
`composition.tex`, `nonlinear.tex`, `appendix-structure.tex`,
`appendix-linearization.tex`, and `strengthening.tex`. The paid implementation's
written proof was also read. Final status wording was reread in
`paper/sections/abstract.tex`, `introduction.tex`, `formalization.tex`, `open.tex`,
`verification.tex`, and `README.md`.

The Lean review read the cited endpoint declarations and their definitions, plus
substantial supporting proofs in `lean/SharedDecoders/`: the capacity ambient,
iteration, difference-cover, run, completion and optimization families; interval,
marker, cyclic-lift, seed, periodic, spectral, block-recovery and base-change
constructions; closure and retention families; triple-source and subcode
barriers; complete/linear composition, channels, progression, recurrence, rank,
band and extraction; word action, balance, agreement, subgroup classes, period
transport and uniform sandwich; and the anchored, local-descent, single-site
and transvection proofs. The arithmetic averaging and Ramsey interfaces were
read as well. Supporting shared proofs read included
`../lean-machine/LeanMachine/BoundedLiminf.lean` and
`../lean-machine/LeanMachine/IncidenceSecondMoment.lean`.

This is not a claim to have read every line of every transitive dependency.
Bibliographic source verification and rendered-PDF inspection are separate
reviews. The latest single-site endpoint, arbitrary-class symmetric theorem,
and final formal-status prose were included; no unreviewed mathematical change
was known when this report was written.

## Mechanical verification

A comment-stripped scan of 96 local/shared Lean files found no executable
`sorry`, `admit`, `native_decide`, new `axiom`, `unsafe`, `sorryAx`, `run_meta`, or
`run_tac` token. This scan is supplementary, not a substitute for kernel checking
or an axiom-closure audit. The finite single-site orbit uses ordinary kernel
`decide +kernel`.

The regenerated `lean/PaperAxioms.lean` contains 88 axiom-print requests. The
coordinating agent reports that the individual endpoint checks and their
standard-axiom audits passed. The final aggregate package build and regenerated
axiom audit were still running when this report was written; their completion
must be recorded before treating global verification as complete. This reviewer
did not launch a competing full build.

## Final integration addendum

After this source review, the coordinating agent completed the full 90-module
package build without warnings and ran all 88 generated axiom-print requests.
Every dependency list was contained in `propext`, `Classical.choice`,
`Quot.sound`; no errors were reported. The final lint cleanup removed unused
nonzero-dimension section assumptions from five auxiliary source lemmas; it
introduced no new hypothesis or weaker conclusion. These execution results are
recorded separately from the independent source inspection above.
