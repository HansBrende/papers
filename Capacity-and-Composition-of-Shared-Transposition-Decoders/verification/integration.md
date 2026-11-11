# Historical integration verification — 10 November 2026

Working draft; no publication, commit or push is implied.

This record preserves the earlier integration and review scope. Subsequent
formalization completed the ordinary results: the current manuscript has 72
fully formalized numbered results and one written-only native compiler.
The current README and theorem status lines supersede the counts and remaining
tasks below. Later upstream reconciliation also updated the Paper 17 citation;
the earlier revision here identifies what this review actually examined.

## Updated Paper 17 crosscheck

Reviewed Paper 17 at repository revision
`14b157af655b8826092a778a8a4fc996512dfde0`, including Proposition 6.15,
Corollary 6.16 and the class-uniform memo. Its entry-rule change and affine-advice
bounds do not subsume the eight extension packages. The manuscript credits the
fixed-advice counting argument and distinguishes advice bits, entry changes,
whole-row changes and the rank of joint propagated corrections.

The Paper 17 citation is pinned to this revision. The class-uniform memo remains
pinned to `b29fa7a`; its cited advice source was checked unchanged. The bounded-
differences citation was checked against Warnke's pinned primary preprint,
Theorem 1, equation (2), and McDiarmid's primary publication metadata.

## Integrated scope and reviews

All B1–B8 packages have precise statements and complete written proofs or faithful
formal outlines. The line-source theorem and its affine qualification are derived
from the actual zero-padded views. Unequal-block recovery now subsumes the old
same-block proof, deleting the repeated reconstruction argument. The seed's full
kernel is checked with a sparse linear identity, then exactness is propagated to
the actual cyclic lift and every independent binary lane.

Independent focused reviews checked B1's orbit/counting/line claims and B2/B8's
block, exact-kernel and complete-residual arguments. A further pass checked the
multiplier, ratio, orbit-assignment and sharp baseline examples. The main author
reviewed B3–B7's prose, assumptions and claimed scope against the new endpoints.
Corrections included explicit block coefficient hypotheses, attribution of the
generic deterministic lift to its actual declaration, the active-coordinate
condition in the Frobenius lemma, and the line proof's formal-outline label.
No unresolved mathematical issue was found in these passes. They do not replace
the remaining formalization tasks named at each partial or written-only result.

Optional items kept out of this manuscript: the mixed-relation demand-map
isomorphism, the triple example's small demand-map rank, and the clean auxiliary-
register variant. They need additional definitions or a different architecture;
the existing capacity/composition statements do not silently include them.
The old dimension-30 numerical lift control is subsumed by the exact general
kernel theorem and is now a numerical illustration. Candidate-specific shear
implementation details are retained separately; only their general complete-
baseline consequence belongs here. The multiplier/ratio diagnostics and sharp
separable/row-column examples were included, with written-only status.

## Checks

- Full Lean package build: 119 local modules, 3431 build jobs, successful.
- Generated declaration audit: 171 requests, all checked exactly once; only
  `propext`, `Classical.choice` and `Quot.sound` occur.
- Numbered items: 75 including one formal definition; 57 carry a formal status,
  7 a partial status and 11 a written-only status. These are presentation counts,
  not a count of independent new theorems.
- The coefficient generator is a reproduction tool, not a trusted rank oracle.
  `binarySeed_recovery_identity` is checked in Lean without native evaluation.
- PDF: 62 pages; no undefined references/citations or overfull boxes.
  Every rendered page was inspected; the active-row and sharp-baseline pages
  were also checked at full page size. Theorem headings retain space for their
  status and opening lines; the bibliography fits together on its final page.
- Final repository portable-path check passed on 3751 files; tracked diff
  whitespace check passed. No machine-specific source paths were introduced.

Ordinary unfinished orbit, concentration, Fourier, entropy and counting work is
listed in the README. The native two-tape transition-table compiler is a separate
substantial task. A passing build verifies the formal endpoints and their
assumptions, not the written-only bridges.
