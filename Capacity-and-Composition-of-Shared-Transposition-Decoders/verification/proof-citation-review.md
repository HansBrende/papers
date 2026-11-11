> Historical checkpoint: this review predates the B1–B8 extension. See [the current integration record](integration.md) for the new scope and remaining formalization work.

# Independent proof and citation review

Reviewed 10 November 2026. The manuscript remains a working draft.

I read the repository's `CONTRIBUTING.md`, the complete manuscript in the
order included by `paper/main.tex`, the README, publication plan and
strengthening record. This review checks the English mathematical arguments,
the written native protocol, cited inputs and scope of the conclusions. The
separate [English–Lean review](english-lean-review.md) checks the declaration
interfaces; this review is not a second exhaustive signature audit or a new
package/axiom build.

No unresolved mathematical gap was found in the reviewed argument chains
within their stated hypotheses. The native implementation is accepted as a
written finite-control construction, with its explicit formalization boundary
retained.

## Proof checks

- **Capacity and structural bounds.** Checked the same-view decoder argument,
  covariance-space dimension and invariance, iterated intersections, cyclic
  run identities including zero and short-cycle steps, cancellation yielding
  `41/64`, and the divisor estimate yielding `5/3`. The doubling averages use
  their actual image distributions. Checked the difference-cover cardinality,
  saturation and epsilon dichotomy; the completion uses `C ∩ ker P`, not a
  presumed correct image of `C`. The normal-basis interval construction has
  the required disjoint residual views and retains its parity hypothesis.
  The scalar-closure defect and symmetric-retention arguments use joint ranks,
  including coupled lanes; the `13/5`, `3/5` and quantitative stability
  constants follow from the displayed inequalities. The coprime-partner and
  prime-dimension exceptions are consistent with the cyclic orbit counts.

- **Constructions and source dimensions.** Checked the CRT rotation convention,
  averaging projector, symmetric-kernel dimension in every characteristic,
  and the same-class lifted decoder. The coprimality and invertibility of `m`
  are necessary hypotheses and remain present. For periodic linear capacity,
  simultaneous outer diagonalization leaves the swap unchanged, and the
  descending block recovery supplies exactly
  `s²m(m−1)/2 + Σ δ_j` coordinates. The equality is scalar and requires
  splitting; the nonsplitting upper bound uses algebraic-closure capacity.
  The imported binary seed supplies a 25-dimensional source, with no seed
  optimality claim. Checked the paired-frequency triple source, its joint
  binary row-sum rank, and both above-half mixture formulas. These subcode
  barriers concern one chosen source at enlarged widths, not maximum
  capacities at bit or canonical width.

- **Paid implementation.** Checked the two-work-tape protocol against the
  frozen model's old-location reads/writes, unit head moves and single-bit
  appends. The bank address is `((r+c) mod m)b+t`; 36 fixed payload tracks
  contain precisely the seed matrix needed for the output Boolean function.
  FIRST/LAST/HOME/END/START are separate tracks, covering `b=1` and `m=1`.
  Physical rewinds, six laps per row, the final row offset and the raw rewind
  are paid. The displayed per-pass budget
  `2P + d² + 2db + 8d + 6 ≤ 5P` holds for the admitted dimensions.
  Length counting, binary-search validation and bank initialization use only
  tape-resident unbounded registers. Their fixed polynomial logarithmic
  overhead is absorbed by `P=d²b` in each of the two stated width regimes.
  There is no third work head or donated size advice in this schedule.

- **Composition and nonlinear strengthening.** Checked the common-message
  fixed-space correction, the complete-factorization witness, Ramsey cutoff
  and recurrence exponent range. The frequency band has dimension `bdk`;
  its intersection charges one global rank error. Exact linear composition
  works over every field; the growing rank deficit retains `(d : F) ≠ 0`.
  Its conclusion is superlinear in `bd`, not a positive fraction of `bd²`.
  Checked the equivariant sandwich, periodic subgroup/class count, agreement
  probabilities, balanced-fibre divisibility argument and period transport.
  Independently checked the anchored seven-cycle and local weight reduction,
  and the single-site step-three/step-four transvection generation, including
  the separate dimensions three and four. Their balance and period arguments
  allow lane mixing but do not permit an arbitrary equivariant outer map in
  the combined two-class endpoint conclusions. They do not settle all masks
  or unrestricted nonlinear two-stage composition.

## Citation checks and corrections

All nine series entries in `paper/references.bib` were compared with the title,
author and date information at the locally available pinned revision
`b29fa7ac3a932a98f069c6f7667c502781550ed3`. For the cited synthesis and memo,
I also checked the linear shared-rule definition, translate bound, explicit
25-dimensional seed, solver qualification on the dimension-19 example,
growing-class blow-up and period/composition discussion. The memo's growing
class count is distinguished from the present fixed-class lift. The Mathlib
revision matches the manifest and installed source, with the stated toolchain.

[Milne's original notes](https://www.jmilne.org/math/CourseNotes/FT.pdf)
verify the title, author, version 5.10, September 2022 and the normal-basis
theorem, Theorem 5.18 on page 68. The citation was made precise accordingly.
[JSTOR's journal record](https://www.jstor.org/stable/1993764) verifies Hales
and Jewett, *Regularity and Positional Games*, *Transactions of the American
Mathematical Society* 106(2), 222–229 (1963); the AMS DOI is consistent with
the publisher's bibliographic record. The original journal full text was not
retrieved in this review. The exact finite combinatorial-line interface used
here was checked in the pinned Mathlib source, together with the manuscript's
sum-of-symbols progression reduction. No numerical Hales–Jewett bound or
minimality of `W(2,3)=9` is being cited.

Small corrections applied during review: identify the previous `3/4` bound as
a linear-decoder result; distinguish finite-dimensional linear bijectivity
from finite nonlinear state-space bijectivity; name the cited complete seed
rule `K_6`; call the native machine's witnessed space a transpose-correct
subcode; keep the scalar-extension outline at the sufficient rank inequality;
remove a reused row-index name; and replace the single-site reverse-step
sentence with a simple-path commutator argument.

## Remaining limits

This review did not construct a frozen-model transition table or prove native
execution, coordinate, controller and time invariants in Lean. That compiler
remains the substantial formalization todo. Nor did it rerun the earlier
solver nonexistence claim, perform a broad literature or thesis search, or
establish priority. PDF inspection, reproducibility checks and complete
package/axiom verification are separate checks. No argument reviewed here
supplies an interface from arbitrary tape executions to fixed-class sources
or same-space complete factorizations, so no unrestricted native transposition
impossibility conclusion follows.
