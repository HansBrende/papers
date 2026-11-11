# Cleanup and strengthening review: 10 November 2026

Working draft. This focused maintenance review supplements the earlier
reviews; it is not a new independent line-by-line audit of the entire library.
There remain 72 fully formalized numbered theorems, lemmas, propositions and
corollaries, and one written-only native two-work-tape implementation.
Definitions and examples are excluded from that count.

## Strengthenings

- `twoHop_progression_gcd` replaces the positive-step correction by the
  actual orbit correction `gcd(d,s)`, also allowing zero and modular steps.
  For a monochromatic progression of length `ell`,
  `ell*d ≤ M₂*d + (ell-1)*M₂*gcd(d,s)`.
  Thus a coprime-step progression of length `M₂+1` gives `d ≤ M₂²`.
  The previous progression theorem is a direct corollary; the global
  two-class cutoff remains `d ≤ 16`. The actual complete factorization,
  class uniformity and linearity hypotheses are unchanged.
- `multiplier_class_count_prefix` counts the attained label range and gives
  `min(d,h)` classes without an extension-degree lower bound on the receiver
  count or a finite ambient label type. The former full-degree statement
  follows directly. The covariance and balanced-fibre hypotheses remain.
- `one_class_residual_eq_bot` directly certifies the already-stated zero
  residual in the one-class extension-linear case. It concerns the actual
  `C ∩ ker P` residual, not an assumed linearity of the entire source over
  the extension field.
- The fixed-depth random-mask mean and tail need only
  `d > (3^k-1)/2`. The numbered three-level theorem now states `d > 13` and
  `ε ≥ 0`, matching the broader scope already proved by its Lean endpoint.

The gcd, attained-range and zero-residual additions received an independent
English/Lean and proof check. Existing clients and the earlier progression
and multiplier statements retain their interfaces.

## Simplification and scope corrections

Replace a duplicate power induction and Boolean-filter argument by existing
library results; remove an unused private positivity lemma and the unneeded
single-site module heartbeat override. Together with the threshold cleanup,
seven Lean files change by a net addition of 95 lines: the new theorem proofs
more than offset the small deletions. The two companion papers also share
their index/audit generator instead of maintaining duplicate scripts.

The manuscript now explicitly states `M ≤ d/2` wherever it advertises the
inverse-square-root class deficit, and `η ≥ 0` in the isolation-floor result.
The introductory line-source half-rate statement is asymptotic for a fixed
number of classes. These repair English qualifications; no Lean theorem
was weakened.

The revised introduction and roadmap distinguish capacity, complete-map
composition and a native-machine reduction. They identify the advances on
Paper 17's Problems 9.1 and 9.4 without claiming to solve its half-rate,
linear interval-attainment or multiscale questions. Fixed-class additive
excess is credited to the updated Paper 17. Duplicate bibliography entries
were consolidated at revision `ac70dc4`, after checking the cited statements
and memo. General written results there are not described as Lean proofs.

The source-level inventory review found no missing integration package.
Quadratic packet summaries and complete-program normalization have different
interfaces and remain separate follow-ups. High entropy alone still does
not supply the linear correctness source used by the capacity bounds.

## Validation

- Full Lean build passed: 160 local modules, 4,085 dependency jobs.
- All 228 generated axiom requests returned the exact requested declarations,
  with dependencies contained in `propext`, `Classical.choice` and `Quot.sound`.
  This includes the newly named fixed-depth source and probability endpoints.
  The build and audit had no errors or warnings.
- The 64-page PDF was rebuilt; every rendered page was inspected, including
  the revised composition, random-mask and multiplier statements. No
  overfull boxes, unresolved references or citations, clipping or overlap
  remained.
- The forbidden-construct, whitespace, frozen-source and public-path checks
  passed. Lean and Mathlib pins remain unchanged. The shared Lean machinery
  was unchanged during this pass; its earlier audit was not repeated.

The README commands reproduce the build, generated declaration audit and PDF.
The generator refactor initially preserved outputs byte for byte; it also
rejects malformed inline declaration names before writing generated files.
No commit, push, release or formal-status promotion is part of this review.
