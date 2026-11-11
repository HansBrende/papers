# Cleanup and scope review: 10 November 2026

Working draft. This is a focused maintenance and English/Lean scope review,
not a new line-by-line audit of the entire library. The earlier
[formalization checkpoint](formalization-checkpoint.md) retains its historical
validation scope. The counts remain 35 fully formalized, six partial and seven
written-only theorems, lemmas, propositions and corollaries.

## Lean changes

- Reuse one half-open slab-index equivalence and the existing slab snapshot
  and capacity estimates in ordinary, clustered and getter geometry. The
  wall-count lemma now allows any natural carrier speed, including zero;
  the existing applications specialize it to their actual speed bounds.
- Delete five duplicate private proofs, including recursive last-element
  membership, which is supplied by Lean's `List.getLastD_mem_cons`.
- Reuse the earlier `observationEntropy_injective` theorem for the joint
  information identity. Remove redundant inhabitance assumptions from six
  information endpoints, treating the empty source explicitly. Actual
  recovery, nonnegative weights and normalization where needed are retained.

These changes remove 58 lines across seven Lean modules. No public endpoint
was deleted and no numerical native bound was weakened. The local-getter
statement now permits one work tape, matching its existing formal endpoint;
its earlier restriction to at least two tapes was unnecessary.

The two companion manuscripts now share the index/audit generator in the
repository's `tools/lean_paper_index.py`. Their local commands are unchanged.
The shared generator rejects malformed inline declaration names before
writing generated output.

## Manuscript and frontier scope

The abstract, introduction and roadmap now distinguish the all-width direct
replay/cut results from canonical-width simulator consequences. The roadmap
states the exact deficit inequality that a certificate on the original entry
quotient would have to violate. The bound applies to timely correct inputs
outside an ambient exception, not to a conditional fraction of an arbitrary
small success set.

Paper 17 and its current numbering were checked at revision `ac70dc4`.
Original-execution transport removes an applicability restriction of earlier
simulator certificates. It does not supply a cheap native cut, a shared-rule
factorization, a linear correctness source or a general multiscale time charge.
The remaining native compilers and their dependent conclusions keep their
explicit written-only or partial status.

A separate review read the remaining written carrier, catalogue,
raw-relative, historical-cache, persistence, eraser, redundant-archive and
monitor/spool arguments. In particular, the future-catalogue argument and
the formal transport theorem use different clocks; their respective radius
bounds are not interchangeable. No blocking defect was found in this review.

The unpublished-result screen found no missing package that belongs in this
paper. Routing/purification and whole-program normalization need separate
hypotheses and remain separate follow-ups.

## Validation

- Full Lean build passed: 201 local modules, 9,518 dependency jobs.
- All 153 generated axiom requests returned the exact requested declarations,
  with dependencies contained in `propext`, `Classical.choice` and `Quot.sound`.
  The build and audit had no errors or warnings.
- The 52-page PDF was rebuilt; every rendered page was inspected. No
  overfull boxes, unresolved references or citations, clipping or overlap
  remained.
- The forbidden-construct, whitespace, frozen-source and public-path checks
  passed. Lean and Mathlib pins remain unchanged. The shared Lean machinery
  was unchanged during this pass; its earlier audit was not repeated.

The standard commands in the README reproduce the build, declaration audit
and PDF. The shared-generator refactor first reproduced the previous outputs
byte for byte; a malformed inline declaration was rejected before any write.
No commit, push, release or formal-status promotion is part of this review.
